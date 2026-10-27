module

public import CFSG.Certificates.Kernel.SporSch.Co1RankElSound

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC.Loop CFSG.KC.Co1RankCoord

variable {G : Type*} [Group G]

@[expose] def spanG : List G → List G → List G
  | [], acc => acc
  | g :: gs, acc => spanG gs (acc ++ acc.map (· * g))

theorem length_spanG : ∀ (gs acc : List G), (spanG gs acc).length = 2 ^ gs.length * acc.length
  | [], acc => by simp [spanG]
  | g :: gs, acc => by
    rw [spanG, length_spanG gs, List.length_append, List.length_map, List.length_cons, pow_succ]
    ring

theorem mem_spanG : ∀ (gs acc : List G) (x : G),
    x ∈ spanG gs acc ↔ ∃ a ∈ acc, ∃ p ∈ spanG gs [1], x = a * p
  | [], acc, x => by simp [spanG]
  | g :: gs, acc, x => by
    simp only [spanG]
    rw [mem_spanG gs (acc ++ acc.map (· * g)) x]
    constructor
    · rintro ⟨a', ha', p, hp, rfl⟩
      rcases List.mem_append.1 ha' with ha | ha
      · exact ⟨a', ha, p, (mem_spanG gs _ p).2 ⟨1, by simp, p, hp, by simp⟩, rfl⟩
      · obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
        exact ⟨a0, ha0, g * p, (mem_spanG gs _ _).2 ⟨g, by simp, p, hp, by simp⟩, by group⟩
    · rintro ⟨a, ha, p', hp', rfl⟩
      obtain ⟨a'', ha'', p, hp, rfl⟩ := (mem_spanG gs _ p').1 hp'
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, one_mul,
        List.mem_cons, List.not_mem_nil, or_false] at ha''
      rcases ha'' with rfl | rfl
      · exact ⟨a, List.mem_append_left _ ha, p, hp, by group⟩
      · exact ⟨a * a'', List.mem_append_right _ (List.mem_map_of_mem ha), p, hp, by group⟩

theorem spanG_comm {y : G} : ∀ (gs acc : List G), (∀ g ∈ gs, g * y = y * g) →
    (∀ a ∈ acc, a * y = y * a) → ∀ p ∈ spanG gs acc, p * y = y * p
  | [], _, _, hacc => hacc
  | g :: gs, acc, hg, hacc => by
    refine spanG_comm gs _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hacc a ha
    · obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
      rw [mul_assoc, hg g List.mem_cons_self, ← mul_assoc, hacc a0 ha0, mul_assoc]

theorem subset_spanG : ∀ (gs acc : List G), ∀ a ∈ acc, a ∈ spanG gs acc
  | [], _, _, ha => ha
  | _ :: gs, _, _, ha => subset_spanG gs _ _ (List.mem_append_left _ ha)

section Inv

variable {gs : List G} (hc : ∀ g ∈ gs, ∀ h ∈ gs, g * h = h * g) (hsq : ∀ g ∈ gs, g * g = 1)
include hc hsq

theorem spanG_mul : ∀ p ∈ spanG gs [1], ∀ g ∈ gs, p * g ∈ spanG gs [1] := by
  induction gs with
  | nil => simp
  | cons g0 gs ih =>
    have hc' : ∀ g ∈ gs, ∀ h ∈ gs, g * h = h * g := fun g hg h hh =>
      hc g (List.mem_cons_of_mem _ hg) h (List.mem_cons_of_mem _ hh)
    have hsq' : ∀ g ∈ gs, g * g = 1 := fun g hg => hsq g (List.mem_cons_of_mem _ hg)
    intro p hp g hg
    change p ∈ spanG gs ([1] ++ [1].map (· * g0)) at hp
    change p * g ∈ spanG gs ([1] ++ [1].map (· * g0))
    obtain ⟨a, ha, p', hp', rfl⟩ := (mem_spanG gs _ p).1 hp
    rcases List.mem_cons.1 hg with hg0 | hgt
    · rw [hg0]
      have hcm := spanG_comm gs [1] (fun g' hg' => hc g' (List.mem_cons_of_mem _ hg') g0
        List.mem_cons_self) (by simp) p' hp'
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, one_mul,
        List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha1 | ha1
      · rw [ha1]
        exact (mem_spanG gs _ _).2 ⟨g0, by simp, p', hp', by rw [one_mul, hcm]⟩
      · rw [ha1]
        exact (mem_spanG gs _ _).2 ⟨1, by simp, p', hp', by
          rw [mul_assoc, hcm, ← mul_assoc, hsq g0 List.mem_cons_self, one_mul]⟩
    · exact (mem_spanG gs _ _).2 ⟨a, ha, p' * g, ih hc' hsq' p' hp' g hgt, by rw [mul_assoc]⟩

theorem closure_eq_spanG : (Subgroup.closure {x | x ∈ gs} : Set G) = {x | x ∈ spanG gs [1]} := by
  ext x
  constructor
  · intro hx
    refine Subgroup.closure_induction_right (p := fun x _ => x ∈ spanG gs [1])
      (subset_spanG gs [1] 1 (by simp)) (fun x _ y hy h => spanG_mul hc hsq x h y hy)
      (fun x _ y hy h => ?_) hx
    rw [inv_eq_of_mul_eq_one_right (hsq y hy)]
    exact spanG_mul hc hsq x h y hy
  · intro hx
    have key : ∀ (hs acc : List G), (∀ g ∈ hs, g ∈ gs) →
        (∀ a ∈ acc, a ∈ Subgroup.closure {x | x ∈ gs}) →
        ∀ p ∈ spanG hs acc, p ∈ Subgroup.closure {x | x ∈ gs} := by
      intro hs
      induction hs with
      | nil => exact fun acc _ hacc => hacc
      | cons g hs ih =>
        intro acc hg hacc
        refine ih _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · exact hacc a ha
        · obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
          exact Subgroup.mul_mem _ (hacc a0 ha0)
            (Subgroup.subset_closure (hg g List.mem_cons_self))
    exact key gs [1] (fun _ h => h) (by simp [Subgroup.one_mem]) x hx

theorem mul_self_of_mem_closure {x : G} (hx : x ∈ Subgroup.closure {x | x ∈ gs}) : x * x = 1 := by
  have key : x * x = 1 ∧ ∀ g ∈ gs, x * g = g * x := by
    refine Subgroup.closure_induction_right
      (p := fun x _ => x * x = 1 ∧ ∀ g ∈ gs, x * g = g * x) (by simp) ?_ ?_ hx
    · intro x _ y hy ⟨h1, h2⟩
      refine ⟨?_, fun g hg => ?_⟩
      · calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * x * (y * y) := by rw [← h2 y hy]; group
          _ = 1 := by rw [h1, hsq y hy, one_mul]
      · rw [mul_assoc, hc y hy g hg, ← mul_assoc, h2 g hg, mul_assoc]
    · intro x _ y hy ⟨h1, h2⟩
      rw [inv_eq_of_mul_eq_one_right (hsq y hy)]
      refine ⟨?_, fun g hg => ?_⟩
      · calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * x * (y * y) := by rw [← h2 y hy]; group
          _ = 1 := by rw [h1, hsq y hy, one_mul]
      · rw [mul_assoc, hc y hy g hg, ← mul_assoc, h2 g hg, mul_assoc]
  exact key.1

end Inv

@[expose] noncomputable def spanA (C : Dat) (gs acc : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun g _ ih acc => ih (dbl C g acc)) gs acc

theorem spanL_eq (C : Dat) (gs : List ℕ) : spanL C gs = spanA C gs [0] := rfl

theorem rec_append (L T : List ℕ) : List.rec (motive := fun _ => List ℕ → List ℕ) (fun T => T)
    (fun a _ ih T => List.cons a (ih T)) L T = L ++ T := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg (List.cons a) ih

theorem rec_map (C : Dat) (g : ℕ) (L : List ℕ) :
    List.rec (motive := fun _ => List ℕ) [] (fun a _ ih => List.cons (mulC C a g) ih) L =
      L.map (fun a => mulC C a g) := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg (List.cons _) ih

theorem dbl_eq (C : Dat) (g : ℕ) (L : List ℕ) : dbl C g L = L ++ L.map (fun a => mulC C a g) := by
  rw [dbl, rec_append, rec_map]

section Coord

variable {C : Dat} {b w : ℕ → G} (hM : Model C b w)
include hM

theorem map_spanA : ∀ (gs acc : List ℕ), (∀ g ∈ gs, g < 2 ^ (C.d + 7)) →
    (∀ a ∈ acc, a < 2 ^ (C.d + 7)) →
    (∀ x ∈ spanA C gs acc, x < 2 ^ (C.d + 7)) ∧
      (spanA C gs acc).map (el C.d b w) = spanG (gs.map (el C.d b w)) (acc.map (el C.d b w))
  | [], acc, _, hacc => ⟨hacc, rfl⟩
  | g :: gs, acc, hg, hacc => by
    have hacc' : ∀ a ∈ dbl C g acc, a < 2 ^ (C.d + 7) := by
      rw [dbl_eq]
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hacc a ha
      · obtain ⟨a, -, rfl⟩ := List.mem_map.1 ha
        exact mulC_lt C a g
    obtain ⟨h1, h2⟩ := map_spanA gs (dbl C g acc) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      hacc'
    refine ⟨h1, ?_⟩
    change (spanA C gs (dbl C g acc)).map _ = spanG _ _
    rw [h2, dbl_eq, List.map_append, List.map_map, List.map_cons, spanG]
    congr 2
    rw [List.map_map]
    refine List.map_congr_left fun a ha => ?_
    exact el_mulC hM (hacc a ha) (hg g List.mem_cons_self)

theorem subset_spanA : ∀ (gs acc : List ℕ), ∀ a ∈ acc, a ∈ spanA C gs acc
  | [], _, _, ha => ha
  | g :: gs, acc, a, ha => by
    change a ∈ spanA C gs (dbl C g acc)
    exact subset_spanA gs _ a (by rw [dbl_eq]; exact List.mem_append_left _ ha)

theorem zero_mem_spanL (gs : List ℕ) : 0 ∈ spanL C gs := subset_spanA hM gs [0] 0 (by simp)

theorem closure_coe_eq (h0 : w 0 = 1) {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 2 ^ (C.d + 7))
    (hcm : ∀ g ∈ gs, ∀ h ∈ gs, mulC C g h = mulC C h g) (hsq : ∀ g ∈ gs, mulC C g g = 0) :
    (Subgroup.closure {x | x ∈ gs.map (el C.d b w)} : Set G) =
      {z | z ∈ (spanL C gs).map (el C.d b w)} := by
  obtain ⟨-, hmap⟩ := map_spanA hM gs [0] hgs (by simp)
  rw [← spanL_eq] at hmap
  have hone : [0].map (el C.d b w) = [1] := by simp [el_zero _ _ _ h0]
  rw [hone] at hmap
  rw [hmap]
  refine closure_eq_spanG ?_ ?_
  · intro _ hg' _ hh'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hh'
    rw [← el_mulC hM (hgs g hg) (hgs h hh), ← el_mulC hM (hgs h hh) (hgs g hg), hcm g hg h hh]
  · intro _ hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    rw [← el_mulC hM (hgs g hg) (hgs g hg), hsq g hg, el_zero _ _ _ h0]

theorem spanL_lt {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 2 ^ (C.d + 7)) :
    ∀ x ∈ spanL C gs, x < 2 ^ (C.d + 7) :=
  (map_spanA hM gs [0] hgs (by simp)).1

theorem closure_el_eq [Finite G] (h0 : w 0 = 1)
    (hinj : ∀ x < 2 ^ (C.d + 7), ∀ y < 2 ^ (C.d + 7), el C.d b w x = el C.d b w y → x = y)
    {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 2 ^ (C.d + 7))
    (hcm : ∀ g ∈ gs, ∀ h ∈ gs, mulC C g h = mulC C h g) (hsq : ∀ g ∈ gs, mulC C g g = 0)
    {L : List ℕ} (hL : L.Nodup) (hlen : L.length = 2 ^ gs.length) (hLs : ∀ x ∈ L, x ∈ spanL C gs) :
    (Subgroup.closure {x | x ∈ gs.map (el C.d b w)} : Set G) = el C.d b w '' {x | x ∈ L} ∧
      Nat.card (Subgroup.closure {x | x ∈ gs.map (el C.d b w)}) = 2 ^ gs.length := by
  have h0' : ∀ a ∈ [0], a < 2 ^ (C.d + 7) := by simp
  obtain ⟨hlt, hmap⟩ := map_spanA hM gs [0] hgs h0'
  rw [← spanL_eq] at hlt hmap
  have hone : [0].map (el C.d b w) = [1] := by simp [el_zero _ _ _ h0]
  rw [hone] at hmap
  have hc' : ∀ g ∈ gs.map (el C.d b w), ∀ h ∈ gs.map (el C.d b w), g * h = h * g := by
    intro _ hg' _ hh'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hh'
    rw [← el_mulC hM (hgs g hg) (hgs h hh), ← el_mulC hM (hgs h hh) (hgs g hg), hcm g hg h hh]
  have hsq' : ∀ g ∈ gs.map (el C.d b w), g * g = 1 := by
    intro _ hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    rw [← el_mulC hM (hgs g hg) (hgs g hg), hsq g hg, el_zero _ _ _ h0]
  have hset := closure_eq_spanG hc' hsq'
  rw [← hmap] at hset
  classical
  have hLlt : ∀ x ∈ L, x < 2 ^ (C.d + 7) := fun x hx => hlt x (hLs x hx)
  have hnd : (L.map (el C.d b w)).Nodup :=
    List.Nodup.map_on (fun x hx y hy h => hinj x (hLlt x hx) y (hLlt y hy) h) hL
  have hsub : (L.map (el C.d b w)).toFinset ⊆ ((spanL C gs).map (el C.d b w)).toFinset := by
    intro z hz
    rw [List.mem_toFinset] at hz ⊢
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    exact List.mem_map_of_mem (hLs x hx)
  have hcardL : (L.map (el C.d b w)).toFinset.card = 2 ^ gs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen]
  have hcardS : ((spanL C gs).map (el C.d b w)).toFinset.card ≤ 2 ^ gs.length := by
    refine (List.toFinset_card_le _).trans ?_
    rw [hmap, length_spanG, List.length_map, List.length_singleton, mul_one]
  have heq : (L.map (el C.d b w)).toFinset = ((spanL C gs).map (el C.d b w)).toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hset' : (Subgroup.closure {x | x ∈ gs.map (el C.d b w)} : Set G) =
      ↑((L.map (el C.d b w)).toFinset) := by
    rw [hset, heq]
    ext z
    simp
  refine ⟨?_, ?_⟩
  · rw [hset']
    ext z
    simp
  · rw [← SetLike.coe_sort_coe, hset', Nat.card_coe_set_eq, Set.ncard_coe_finset, hcardL]

end Coord

end CFSG.KS.SporSch.Co1Rank

end
