module

public import Certificates.Data.Kernel.LocalQT.Pairs
public import CFSG.Certificates.Kernel.LocalQTEvalZKProved
public import CFSG.Certificates.Kernel.LocalQTTab2KSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM12CheckInputs

public section

namespace CFSG.KC.LQT.Pairs

open Equiv CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs
  CFSG.KC.LQT.W CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.Syl
  CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

@[expose] def cX (x : X12) : ℕ := codeP (x : Perm (Fin 12))

theorem cX_inj {x y : X12} (h : cX x = cX y) : x = y :=
  Subtype.ext (P.code_inj (n := 12) (by norm_num) h)

theorem cX_mul (x y : X12) : P.mul 12 (cX x) (cX y) = cX (x * y) :=
  P.code_mul (n := 12) (by norm_num) x.1 y.1

theorem cX_inv (x : X12) : P.inv 12 (cX x) = cX x⁻¹ :=
  P.code_inv (n := 12) (by norm_num) x.1

theorem cX_one : P.one 12 = cX 1 := P.code_one

theorem mem_map_cX (L : List X12) (x : X12) : cX x ∈ L.map cX ↔ x ∈ L := by
  simp only [List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => cX_inj e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem memL_cX (L : List X12) (x : X12) : memL (cX x) (L.map cX) = decide (x ∈ L) := by
  rw [Bool.eq_iff_iff, memL_iff, mem_map_cX, decide_eq_true_iff]

theorem comm_cX (x y : X12) : P.comm 12 (cX x) (cX y) = (x * y == y * x) := by
  rw [Bool.eq_iff_iff, P.comm, cX_mul, cX_mul, P.beq_iff, beq_iff_eq]
  exact ⟨cX_inj, fun h => h ▸ rfl⟩

theorem enc_inj {x y : X12} (h : enc x = enc y) : x = y := by
  refine Subtype.ext (Equiv.ext fun i => Fin.ext ?_)
  have := (List.map_inj_left.1 h) i (List.mem_finRange i)
  exact this

theorem tabX_eq (x : X12) : tabX x = x := Subtype.ext (tab_eq x.1)

theorem evalW_eq {G : Type*} [Group G] (S : List G) (w : List ℤ) : evalW S w = evalG S w := by
  induction w with
  | nil => rfl
  | cons z w ih => rw [evalW, evalG, ih]

theorem genX_codes {cA cB : ℕ} (hA : cX m12a = cA) (hB : cX m12b = cB) (ws : List (List ℤ)) :
    (ws.map genX).map cX = ws.map (evalZK 12 [cA, cB]) := by
  rw [List.map_map]
  refine List.map_congr_left fun w _ => ?_
  have hL : [cA, cB] = ([m12a, m12b].map Subtype.val).map codeP := by
    rw [← hA, ← hB]
    rfl
  rw [Function.comp_apply, genX, tabX_eq, hL, evalZK_codeP (by norm_num), cX, evalW_eq,
    coe_evalG]

@[expose] noncomputable def newGo (seen l : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun y _ ih acc => ih (Bool.rec (motive := fun _ => List ℕ) (List.cons y acc) acc
      (orB (memL y seen) (memL y acc)))) l

@[expose] def dstep (a : List X12) (y : X12) : List X12 := if y ∈ a then a else y :: a

@[expose] def nstep (L : List X12) (a : List X12) (y : X12) : List X12 :=
  if y ∈ L ∨ y ∈ a then a else y :: a

section Enc

variable {E : Type*} [DecidableEq E] {ec : X12 → E}

theorem mem_map_inj (hec : ∀ x y, ec x = ec y → x = y) (L : List X12) (x : X12) :
    ec x ∈ L.map ec ↔ x ∈ L := by
  simp only [List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => hec _ _ e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem foldl_dedup (hec : ∀ x y, ec x = ec y → x = y) (l acc : List X12) :
    l.foldl (fun (p : List X12 × List E) y =>
        if ec y ∈ p.2 then p else (y :: p.1, ec y :: p.2)) (acc, acc.map ec) =
      (l.foldl dstep acc, (l.foldl dstep acc).map ec) := by
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih =>
    simp only [List.foldl_cons, dstep, mem_map_inj hec]
    by_cases hy : y ∈ acc
    · simp only [hy, if_true]
      exact ih acc
    · simp only [hy, if_false]
      exact ih (y :: acc)

theorem foldl_filter (hec : ∀ x y, ec x = ec y → x = y) (L M acc : List X12) :
    (M.filter fun y => decide (ec y ∉ L.map ec)).foldl dstep acc = M.foldl (nstep L) acc := by
  have hf : (M.filter fun y => decide (ec y ∉ L.map ec)) = M.filter fun y => decide (y ∉ L) :=
    List.filter_congr fun y _ => by simp only [mem_map_inj hec]
  rw [hf]
  clear hf
  induction M generalizing acc with
  | nil => rfl
  | cons y M ih =>
    by_cases hL : y ∈ L
    · rw [List.filter_cons_of_neg (by simpa using hL), List.foldl_cons, ih]
      have hn : nstep L acc y = acc := if_pos (Or.inl hL)
      rw [hn]
    · rw [List.filter_cons_of_pos (by simpa using hL), List.foldl_cons, List.foldl_cons, ih]
      congr 1
      simp only [dstep, nstep, hL, false_or]

theorem dedupBy_filter (hec : ∀ x y, ec x = ec y → x = y) (L M : List X12) :
    dedupBy ec (M.filter fun y => decide (ec y ∉ L.map ec)) = (M.foldl (nstep L) []).reverse := by
  have e := foldl_dedup hec (M.filter fun y => decide (ec y ∉ L.map ec)) []
  unfold dedupBy
  rw [List.map_nil] at e
  rw [e, foldl_filter hec]

end Enc

theorem foldl_newGo (L M acc : List X12) :
    (M.foldl (nstep L) acc).map cX = newGo (L.map cX) (M.map cX) (acc.map cX) := by
  induction M generalizing acc with
  | nil => rfl
  | cons y M ih =>
    rw [List.foldl_cons, List.map_cons]
    change _ = newGo (L.map cX) (M.map cX) (Bool.rec (motive := fun _ => List ℕ)
      (List.cons (cX y) (acc.map cX)) (acc.map cX) (orB (memL (cX y) (L.map cX))
        (memL (cX y) (acc.map cX))))
    rw [memL_cX, memL_cX]
    by_cases h : y ∈ L ∨ y ∈ acc
    · have hb : orB (decide (y ∈ L)) (decide (y ∈ acc)) = true := by
        rw [P.orB_iff, decide_eq_true_iff, decide_eq_true_iff]
        exact h
      have hn : nstep L acc y = acc := if_pos h
      rw [hn, hb, ih]
    · have hb : orB (decide (y ∈ L)) (decide (y ∈ acc)) = false := by
        rw [← Bool.not_eq_true, P.orB_iff, decide_eq_true_iff, decide_eq_true_iff]
        exact h
      have hn : nstep L acc y = y :: acc := if_neg h
      rw [hn, hb, ih, List.map_cons]

theorem flatMap_gen (nrm : X12 → X12) (hn : ∀ x, nrm x = x) (m : ℕ → ℕ → ℕ)
    (hm : ∀ x y, m (cX x) (cX y) = cX (x * y)) (L gens : List X12) :
    (L.flatMap fun x => gens.map fun g => nrm (g * x)).map cX =
      List.flatten (List.map (fun x => List.map (fun g => m g x) (gens.map cX)) (L.map cX)) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.flatMap_cons, List.map_append, ih, List.map_cons, List.map_cons, List.flatten_cons]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun g _ => ?_
    rw [Function.comp_apply, Function.comp_apply, hn, hm]

theorem flatMap_codes (L gens : List X12) :
    (L.flatMap fun x => gens.map fun g => tabX (g * x)).map cX =
      List.flatten (List.map (fun x => List.map (fun g => P.mul 12 g x) (gens.map cX))
        (L.map cX)) :=
  flatMap_gen tabX tabX_eq (P.mul 12) cX_mul L gens

theorem step_codes (gens L : List X12) :
    (closureStep tabX enc gens L).map cX = List.append (L.map cX) (newK (L.map cX)
      (List.flatten (List.map (fun x => List.map (fun g => P.mul 12 g x) (gens.map cX))
        (L.map cX)))) := by
  unfold closureStep
  dsimp only
  rw [List.map_append, dedupBy_filter (fun _ _ => enc_inj), List.map_reverse, foldl_newGo,
    flatMap_codes]
  rfl

theorem cl_codes {cA cB : ℕ} (hA : cX m12a = cA) (hB : cX m12b = cB) (ws : List (List ℤ)) (k : ℕ) :
    (closureList tabX enc (ws.map genX) k).map cX =
      clK 12 (List.map (evalZK 12 [cA, cB]) ws) k := by
  rw [← genX_codes hA hB]
  induction k with
  | zero =>
    change [cX 1] = [P.one 12]
    rw [cX_one]
  | succ k ih =>
    change (closureStep tabX enc (ws.map genX) (closureList tabX enc (ws.map genX) k)).map cX =
      List.append (clK 12 ((ws.map genX).map cX) k) (newK (clK 12 ((ws.map genX).map cX) k)
        (List.flatten (List.map (fun x => List.map (fun g => P.mul 12 g x) ((ws.map genX).map cX))
          (clK 12 ((ws.map genX).map cX) k))))
    rw [← ih]
    exact step_codes _ _

theorem filter_codes (T : List X12) (p : X12 → Bool) (q : ℕ → Bool) (h : ∀ x ∈ T, q (cX x) = p x) :
    (T.filter p).map cX = filtL (T.map cX) q := by
  rw [T2.filtL_eqT, List.filter_map]
  congr 1
  exact List.filter_congr fun x hx => (h x hx).symm

theorem center_codes (S : List X12) {SC : List ℕ} (hS : S.map cX = SC) :
    (S.filter fun x => S.all fun s => s * x == x * s).map cX = centerK 12 SC := by
  subst hS
  refine filter_codes S _ _ fun x _ => ?_
  rw [Bool.eq_iff_iff, P.allL_iff, List.all_eq_true]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, comm_cX]

@[expose] noncomputable def dedGo (l : List ℕ) : Option ℕ → List ℕ :=
  List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
    (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
      (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x))) (ih (some x))
        (Nat.beq x y)) o) l

theorem mem_dedGo (c : ℕ) : ∀ (l : List ℕ) (o : Option ℕ),
    (c ∈ dedGo l o ∨ o = some c) ↔ (c ∈ l ∨ o = some c)
  | [], o => by simp [dedGo]
  | x :: l, o => by
    have ih := mem_dedGo c l (some x)
    simp only [Option.some.injEq] at ih
    have hk : (c ∈ x :: dedGo l (some x) ∨ o = some c) ↔ (c ∈ x :: l ∨ o = some c) := by
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl h)
        · rcases ih.1 (Or.inl h) with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h.symm)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl h)
        · rcases ih.2 (Or.inl h) with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h.symm)
        · exact Or.inr h
    cases o with
    | none => exact hk
    | some y =>
      change ((c ∈ Bool.rec (motive := fun _ => List ℕ) (x :: dedGo l (some x)) (dedGo l (some x))
        (Nat.beq x y)) ∨ some y = some c) ↔ _
      cases hb : Nat.beq x y with
      | false => exact hk
      | true =>
        obtain rfl := Nat.eq_of_beq_eq_true hb
        simp only [Option.some.injEq, List.mem_cons] at ih ⊢
        constructor
        · rintro (h | h)
          · rcases ih.1 (Or.inl h) with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
          · exact Or.inr h
        · rintro ((h | h) | h)
          · exact Or.inr h.symm
          · exact ih.2 (Or.inl h)
          · exact Or.inr h

theorem mem_dedupS (c : ℕ) (l : List ℕ) : c ∈ dedupS l ↔ c ∈ l := by
  have := mem_dedGo c l none
  simp only [reduceCtorEq, or_false] at this
  exact this

theorem sortN_perm (l : List ℕ) : (sortN l).Perm l := by
  have key : ∀ m, (Nat.rec (motive := fun _ => List (List ℕ)) (List.map (fun x => [x]) l)
      (fun _ ih => T2.passK ih) m).flatten.Perm l := by
    intro m
    induction m with
    | zero =>
      change (List.map (fun x => [x]) l).flatten.Perm l
      rw [T2.flatten_singletonsT]
    | succ m ih => exact (T2.passGoT_perm _ none).trans ih
  exact key 17

theorem mem_comms_gen (m : ℕ → ℕ → ℕ) (iv : ℕ → ℕ) (hm : ∀ x y, m (cX x) (cX y) = cX (x * y))
    (hi : ∀ x, iv (cX x) = cX x⁻¹) (S : List X12) (c : ℕ) :
    c ∈ List.flatten (List.map (fun s => List.map (fun t => m (m (m s t) (iv s)) (iv t))
      (S.map cX)) (S.map cX)) ↔ ∃ s ∈ S, ∃ t ∈ S, c = cX (s * t * s⁻¹ * t⁻¹) := by
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hc⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    exact ⟨s, hs, t, ht, by rw [hm, hi, hm, hi, hm]⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨_, List.mem_map.2 ⟨cX s, List.mem_map.2 ⟨s, hs, rfl⟩, rfl⟩,
      List.mem_map.2 ⟨cX t, List.mem_map.2 ⟨t, ht, rfl⟩, ?_⟩⟩
    rw [hm, hi, hm, hi, hm]

theorem mem_commsK (S : List X12) (c : ℕ) :
    c ∈ commsK 12 (S.map cX) ↔ ∃ s ∈ S, ∃ t ∈ S, c = cX (s * t * s⁻¹ * t⁻¹) := by
  rw [commsK, mem_dedupS, (sortN_perm _).mem_iff]
  exact mem_comms_gen (P.mul 12) (P.inv 12) cX_mul cX_inv S c

theorem centD_codes (S : List X12) {SC : List ℕ} (hS : S.map cX = SC) :
    (S.filter fun x => S.all fun s => S.all fun t =>
      (s * t * s⁻¹ * t⁻¹) * x == x * (s * t * s⁻¹ * t⁻¹)).map cX = centDK 12 SC := by
  subst hS
  refine filter_codes S _ _ fun x _ => ?_
  rw [Bool.eq_iff_iff, P.allL_iff, List.all_eq_true]
  simp only [mem_commsK, List.all_eq_true, forall_exists_index, and_imp]
  constructor
  · intro h s hs t ht
    have := h _ s hs t ht rfl
    rwa [comm_cX] at this
  · rintro h c s hs t ht rfl
    rw [comm_cX]
    exact h s hs t ht

end CFSG.KC.LQT.Pairs

end
