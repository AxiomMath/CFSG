module

public import Certificates.Data.Kernel.Mat8S
public import CFSG.Certificates.Kernel.Mat8RSound

public section

namespace CFSG.KC.Mat8S

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P CFSG.KC.Mat8R

theorem memS_insS (d m : ℕ) (t : NT ℕ) (x y : ℕ) :
    memS d m (insS d m t x) y = (x == y || memS d m t y) :=
  ntMem_ins d _ _ t x y (fun e => by rw [e])

theorem memS_empty (d m y : ℕ) : memS d m (.tip []) y = false := by
  rw [memS, ntMem_tip]
  rfl

def SR (d m : ℕ) (p q : NT ℕ × List ℕ × List ℕ) : Prop :=
  (∀ z, memP p.1 z = memS d m q.1 z) ∧ p.2 = q.2

theorem foldR_rel {α β : Type} (F G : β → α → β) (R : β → β → Prop)
    (h : ∀ p q x, R p q → R (F p x) (G q x)) :
    ∀ (l : List α) (p q : β), R p q → R (foldR F p l) (foldR G q l) := by
  intro l
  induction l with
  | nil => intro p q hpq; exact hpq
  | cons x l ih => intro p q hpq; exact ih _ _ (h p q x hpq)

theorem stepS_rel (d m : ℕ) (p q : NT ℕ × List ℕ × List ℕ) (y : ℕ) (h : SR d m p q) :
    SR d m (stepY p y) (stepS d m q y) := by
  rcases p with ⟨t, a, f⟩
  rcases q with ⟨s, a', f'⟩
  obtain ⟨h1, h2⟩ := h
  have h1' : ∀ z, memP t z = memS d m s z := h1
  have h2' : (a, f) = (a', f') := h2
  rw [Prod.mk.injEq] at h2'
  obtain ⟨rfl, rfl⟩ := h2'
  rw [stepY_eq]
  change SR d m (if memP t y then (t, a, f) else (insP t y, y :: a, y :: f))
    (Bool.rec (motive := fun _ => NT ℕ × List ℕ × List ℕ)
      (insS d m s y, y :: a, y :: f) (s, a, f) (memS d m s y))
  rw [h1' y]
  cases hc : memS d m s y
  · refine ⟨fun z => ?_, rfl⟩
    change memP (insP t y) z = memS d m (insS d m s y) z
    rw [memP_insP, memS_insS, h1' z]
  · exact ⟨h1', rfl⟩

theorem layerS_rel (d m : ℕ) (gens : List ℕ) (t s : NT ℕ) (acc fr : List ℕ)
    (h : ∀ z, memP t z = memS d m s z) :
    SR d m (layerR gens t acc fr) (layerS d m gens s acc fr) :=
  foldR_rel _ _ (SR d m) (fun p q x hpq => foldR_rel _ _ (SR d m)
    (fun p q g hpq => stepS_rel d m p q (mulP g x) hpq) gens p q hpq) fr _ _ ⟨h, rfl⟩

theorem bfsS_eq (d m : ℕ) (gens : List ℕ) (cap : ℕ) :
    ∀ fuel (t s : NT ℕ) acc fr, (∀ z, memP t z = memS d m s z) →
      bfsS d m gens cap fuel s acc fr = bfsR gens cap fuel t acc fr := by
  intro fuel
  induction fuel with
  | zero => intro t s acc fr _; rfl
  | succ n ih =>
    intro t s acc fr h
    cases fr with
    | nil => rfl
    | cons x l =>
      change Bool.rec (motive := fun _ => List ℕ) (Prod.rec (motive := fun _ => List ℕ)
            (fun s r => Prod.rec (motive := fun _ => List ℕ) (fun a f => bfsS d m gens cap n s a f) r)
            (layerS d m gens s acc (x :: l)))
          acc (Nat.ble cap (lenR acc)) =
        Bool.rec (motive := fun _ => List ℕ) (Prod.rec (motive := fun _ => List ℕ)
            (fun s r => Prod.rec (motive := fun _ => List ℕ) (fun a f => bfsR gens cap n s a f) r)
            (layerR gens t acc (x :: l)))
          acc (Nat.ble cap (lenR acc))
      rw [prodRec3, prodRec3]
      obtain ⟨h1, h2⟩ := layerS_rel d m gens t s acc (x :: l) h
      rw [← h2, ih _ _ _ _ h1]

theorem elemsS_eq (d m : ℕ) (gens : List ℕ) (cap : ℕ) : elemsS d m gens cap = elemsP gens cap := by
  rw [elemsS, ← elemsR_eq, elemsR]
  refine bfsS_eq d m gens cap 200 _ _ _ _ (fun z => ?_)
  rw [memP_insP, memS_insS, memP_empty, memS_empty]

theorem elemsFS_eq (d m : ℕ) (gens : List (List ℕ)) (cap : ℕ) :
    elemsFS d m gens cap = elemsF gens cap := by
  rw [elemsFS, elemsF, elemsS_eq]

def NInv (t : NT ℕ) (acc : List ℕ) : Prop :=
  (∀ q, memP t q = acc.contains q) ∧ acc.Nodup ∧ ∀ q ∈ acc, q < 2 ^ 64

theorem nInv_step (st : NT ℕ × List ℕ × List ℕ) (y : ℕ) (hy : y < 2 ^ 64) (h : NInv st.1 st.2.1) :
    NInv (if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)).1
      (if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)).2.1 := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hc : memP st.1 y = true
  · rw [if_pos hc]
    exact ⟨h1, h2, h3⟩
  · rw [if_neg hc]
    have hn : y ∉ st.2.1 := by
      intro hm
      rw [h1 y, List.contains_iff_mem.mpr hm] at hc
      exact hc rfl
    refine ⟨fun q => ?_, List.nodup_cons.mpr ⟨hn, h2⟩, fun q hq => ?_⟩
    · dsimp only
      rw [memP_insP, h1 q, List.contains_cons, beq_symm y q]
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hy
      · exact h3 q hq

theorem nInv_inner (gens : List ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (st : NT ℕ × List ℕ × List ℕ), NInv st.1 st.2.1 →
      NInv (l.foldl (fun (st : NT ℕ × List ℕ × List ℕ) i =>
          let y := mulP (gens.getD i oneP) x
          if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)) st).1
        (l.foldl (fun (st : NT ℕ × List ℕ × List ℕ) i =>
          let y := mulP (gens.getD i oneP) x
          if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)) st).2.1
  | [], _, h => h
  | i :: l, st, h => nInv_inner gens x l _ (nInv_step st _ (mulP_lt _ _) h)

theorem nInv_outer (gens : List ℕ) :
    ∀ (fr : List ℕ) (st : NT ℕ × List ℕ × List ℕ), NInv st.1 st.2.1 →
      NInv (fr.foldl (fun (st : NT ℕ × List ℕ × List ℕ) x =>
          (List.range gens.length).foldl (fun (st : NT ℕ × List ℕ × List ℕ) i =>
            let y := mulP (gens.getD i oneP) x
            if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)) st) st).1
        (fr.foldl (fun (st : NT ℕ × List ℕ × List ℕ) x =>
          (List.range gens.length).foldl (fun (st : NT ℕ × List ℕ × List ℕ) i =>
            let y := mulP (gens.getD i oneP) x
            if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)) st) st).2.1
  | [], _, h => h
  | x :: fr, st, h => nInv_outer gens fr _ (nInv_inner gens x _ st h)

theorem nInv_bfsP (gens : List ℕ) (cap : ℕ) :
    ∀ fuel (t : NT ℕ) acc fr, NInv t acc →
      (bfsP gens cap fuel t acc fr).Nodup ∧ ∀ q ∈ bfsP gens cap fuel t acc fr, q < 2 ^ 64 := by
  intro fuel
  induction fuel with
  | zero => intro t acc fr h; exact h.2
  | succ n ih =>
    intro t acc fr h
    cases fr with
    | nil => exact h.2
    | cons x l =>
      rw [bfsP]
      on_goal 2 => exact fun h => List.cons_ne_nil x l h
      split_ifs
      · exact h.2
      · exact ih _ _ _ (nInv_outer gens (x :: l) (t, acc, []) h)

theorem nInv_elemsP (gens : List ℕ) (cap : ℕ) :
    (elemsP gens cap).Nodup ∧ ∀ q ∈ elemsP gens cap, q < 2 ^ 64 := by
  refine nInv_bfsP gens cap 200 _ _ _ ⟨fun q => ?_, List.nodup_singleton _, fun q hq => ?_⟩
  · rw [memP_insP, memP_empty, List.contains_cons, List.contains_nil, beq_symm]
  · rw [List.mem_singleton.mp hq]
    exact oneP_lt

theorem code64R_unpackM (X : ℕ) (h : X < 2 ^ 64) : code64R (unpackM X) = X := by
  rw [code64R_eq, unpackM_eq, code64_unpackS, Nat.mod_eq_of_lt h]

theorem nodupP_elemsF (gens : List (List ℕ)) (hg : gens.all validB = true) (cap : ℕ) :
    nodupP ((elemsF gens cap).map code64R) = true := by
  obtain ⟨h1, h2⟩ := nInv_elemsP (gens.map code64R) cap
  rw [elemsF, if_pos hg, List.map_map, nodupP_iff]
  rw [List.map_congr_left (f := code64R ∘ unpackM) (g := id)
    (fun q hq => code64R_unpackM q (h2 q hq)), List.map_id]
  exact h1

@[expose] def closedP (gp L : List ℕ) : Bool :=
  L.all fun x => gp.all fun g => memP (ofListP L) (mulP g x)

theorem contains_map_unpackM (L : List ℕ) (hL : ∀ q ∈ L, q < 2 ^ 64) (Y : ℕ) (hY : Y < 2 ^ 64) :
    (L.map unpackM).contains (unpackM Y) = L.contains Y := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨a, ha, e⟩
    rw [← unpackM_inj (hL a ha) hY e]
    exact ha
  · intro h
    exact ⟨Y, h, rfl⟩

theorem closedB_unpack (gp L : List ℕ) (hL : ∀ q ∈ L, q < 2 ^ 64) :
    closedB (gp.map unpackM) (L.map unpackM) = closedP gp L := by
  simp only [closedB, closedP, Std.HashSet.contains_ofList, List.all_map, Function.comp_def,
    mul8_unpackM, memP_ofListP]
  congr 1
  funext X
  congr 1
  funext G
  exact contains_map_unpackM L hL _ (mulP_lt _ _)

theorem map_unpack_code64 (gens : List (List ℕ)) (hg : gens.all validB = true) :
    (gens.map code64R).map unpackM = gens := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id gens]
  apply List.map_congr_left
  intro a ha
  rw [List.all_eq_true] at hg
  exact unpackM_code64R a (hg a ha)

theorem closedB_elemsF (gens : List (List ℕ)) (cap : ℕ) :
    closedB gens (elemsF gens cap) = if gens.all validB then
      closedP (gens.map code64R) (elemsP (gens.map code64R) cap)
    else closedB gens (elemsOf gens cap) := by
  by_cases hg : gens.all validB = true
  · rw [if_pos hg, elemsF, if_pos hg]
    have h := closedB_unpack (gens.map code64R) (elemsP (gens.map code64R) cap)
      (nInv_elemsP _ _).2
    rw [map_unpack_code64 gens hg] at h
    exact h
  · rw [if_neg hg, elemsF, if_neg hg]

theorem nodupP_elemsF_if (gens : List (List ℕ)) (cap : ℕ) :
    nodupP ((elemsF gens cap).map code64R) = if gens.all validB then true
    else nodupP ((elemsOf gens cap).map code64R) := by
  by_cases hg : gens.all validB = true
  · rw [if_pos hg, nodupP_elemsF gens hg]
  · rw [if_neg hg, elemsF, if_neg hg]

theorem all_validB_elemsF (gens : List (List ℕ)) (cap : ℕ) :
    (elemsF gens cap).all validB = if gens.all validB then true
    else (elemsOf gens cap).all validB := by
  by_cases hg : gens.all validB = true
  · rw [if_pos hg, elemsF, if_pos hg, List.all_map, List.all_eq_true]
    intro X _
    exact validB_unpackM X
  · rw [if_neg hg, elemsF, if_neg hg]

theorem memLR_elemsF_one (gens : List (List ℕ)) (cap : ℕ) :
    memLR (ofListLR (elemsF gens cap)) one8 = if gens.all validB then
      memP (ofListP (elemsP (gens.map code64R) cap)) oneP
    else memLR (ofListLR (elemsOf gens cap)) one8 := by
  by_cases hg : gens.all validB = true
  · rw [if_pos hg, elemsF, if_pos hg, memLR_ofListLR, memP_ofListP, ← oneP_eq,
      contains_map_unpackM _ (nInv_elemsP _ _).2 _ oneP_lt]
  · rw [if_neg hg, elemsF, if_neg hg]

theorem all_memLR_elemsF (L : List ℕ) (gens : List (List ℕ)) (cap : ℕ) :
    (L.map unpackM).all (memLR (ofListLR (elemsF gens cap))) =
      if gens.all validB && L.all (fun q => decide (q < 2 ^ 64)) then
        L.all (memP (ofListP (elemsP (gens.map code64R) cap)))
      else (L.map unpackM).all (memLR (ofListLR (elemsOf gens cap))) := by
  by_cases hg : (gens.all validB && L.all (fun q => decide (q < 2 ^ 64))) = true
  · rw [if_pos hg]
    rw [Bool.and_eq_true] at hg
    obtain ⟨hg, hL⟩ := hg
    rw [List.all_eq_true] at hL
    rw [elemsF, if_pos hg, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun X hX => ?_
    rw [Function.comp_apply, memLR_ofListLR, memP_ofListP,
      contains_map_unpackM _ (nInv_elemsP _ _).2 _ (of_decide_eq_true (hL X hX))]
  · rw [if_neg hg, elemsOf_toF]

theorem all_elemsF (gens : List (List ℕ)) (cap : ℕ) (f : List ℕ → Bool) :
    (elemsF gens cap).all f = if gens.all validB then
      (elemsP (gens.map code64R) cap).all (fun X => f (unpackM X))
    else (elemsOf gens cap).all f := by
  by_cases hg : gens.all validB = true
  · rw [if_pos hg, elemsF, if_pos hg, List.all_map]
    rfl
  · rw [if_neg hg, elemsF, if_neg hg]

theorem any_elemsF (gens : List (List ℕ)) (cap : ℕ) (f : List ℕ → Bool) :
    (elemsF gens cap).any f = if gens.all validB then
      (elemsP (gens.map code64R) cap).any (fun X => f (unpackM X))
    else (elemsOf gens cap).any f := by
  by_cases hg : gens.all validB = true
  · rw [if_pos hg, elemsF, if_pos hg, List.any_map]
    rfl
  · rw [if_neg hg, elemsF, if_neg hg]

theorem mul8F_unpackM (X Y : ℕ) : mul8F (unpackM X) (unpackM Y) = unpackM (mulP X Y) := by
  rw [mul8F_eq, mul8_unpackM]

theorem beq_one_mulP (X Y : ℕ) : (unpackM (mulP X Y) == one8) = (mulP X Y == oneP) := by
  rw [← oneP_eq, unpackM_beq (mulP_lt _ _) oneP_lt]

theorem beq_mulP_mulP (A B C D : ℕ) :
    (unpackM (mulP A B) == unpackM (mulP C D)) = (mulP A B == mulP C D) :=
  unpackM_beq (mulP_lt _ _) (mulP_lt _ _)

end CFSG.KC.Mat8S

end
