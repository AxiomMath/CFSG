module

public import CFSG.LieType.Universal.Spin.OddCT.Basic

public section

namespace CFSG.LieType.Universal.Spin

open CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

namespace OddCT

variable {n : ℕ} {K : Type} [Field K]

theorem longRoot_mem_oddRootGroup {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (h : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (c : Multiplicative K) : (oddFrame n K).longRoot hij s t c ∈ oddRootGroup n K γ := by
  rw [oddRootGroup_eq_long hij s t h]
  exact ⟨c, rfl⟩

theorem shortRoot_mem_oddRootGroup {γ : Fin n → ℤ} {i : Fin n} {s : Bool}
    (h : toStdB n γ = Pi.single i (boolSign s)) (c : Multiplicative K) :
    (oddFrame n K).shortRoot i s c ∈ oddRootGroup n K γ := by
  rw [oddRootGroup_eq_short i s h]
  exact ⟨c, rfl⟩

theorem rootB_mem (k : Fin n) (c : Multiplicative K) :
    rootB K k c ∈ oddRootGroup n K (Pi.single k 1) := by
  rw [oddRootGroup_single]
  exact ⟨c, rfl⟩

theorem negRootB_mem (k : Fin n) (c : Multiplicative K) :
    negRootB K k c ∈ oddRootGroup n K (-Pi.single k 1) := by
  rw [oddRootGroup_neg_single]
  exact ⟨c, rfl⟩

theorem rankOneB_mem_rankOne (k : Fin n) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    rankOneB K k M ∈ rankOne (oddRootGroup n K) k := by
  refine (Subgroup.closure_le _).mpr ?_ (rankOneB_mem_closure K k M)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact Subgroup.mem_sup_left (rootB_mem k c)
  · exact Subgroup.mem_sup_right (negRootB_mem k c)

theorem single_comp_swap (a p q : Fin n) (x : ℤ) :
    Pi.single a x ∘ Equiv.swap p q = Pi.single (Equiv.swap p q a) x := by
  rw [Pi.single_comp_equiv, Equiv.symm_swap]

theorem longWeylBool_true_false (i j m : Fin n) (r : Bool) :
    longWeylBool i j true false m r = r := by
  cases r <;> simp [longWeylBool]

theorem sign_mul_single (k i : Fin n) (s : Bool) (a : Fin n) :
    (if a = k then -1 else 1) * (Pi.single i (boolSign s) : Fin n → ℤ) a =
      (Pi.single i (boolSign (shortWeylBool k i s)) : Fin n → ℤ) a := by
  by_cases ha : a = i
  · subst ha
    by_cases hk : a = k
    · simp [shortWeylBool, hk]
    · simp [shortWeylBool, hk]
  · simp [ha]

theorem weylB_conj_longRoot_mem (k : Fin n) {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (hγ : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : K) :
    weylB K k * (oddFrame n K).longRoot hij s t (.ofAdd c) * (weylB K k)⁻¹ ∈
      oddRootGroup n K (reflection (cartanB n) k γ) := by
  by_cases hk : k.val + 1 < n
  · rw [weylB_conj_longRoot_of_lt K hk hij s t c]
    refine longRoot_mem_oddRootGroup _ ?_ _
    rw [longWeylBool_true_false, longWeylBool_true_false, toStdB_reflection_of_lt n hk, hγ,
      Pi.add_comp, single_comp_swap, single_comp_swap]
  · rw [weylB_conj_longRoot_of_not_lt K hk hij s t c]
    refine longRoot_mem_oddRootGroup _ ?_ _
    rw [toStdB_reflection, stdReflB_of_not_lt n hk, hγ]
    funext a
    rw [Pi.add_apply, mul_add, Pi.add_apply, sign_mul_single, sign_mul_single]

theorem weylB_conj_shortRoot_mem (k : Fin n) {γ : Fin n → ℤ} (i : Fin n) (s : Bool)
    (hγ : toStdB n γ = Pi.single i (boolSign s)) (c : K) :
    weylB K k * (oddFrame n K).shortRoot i s (.ofAdd c) * (weylB K k)⁻¹ ∈
      oddRootGroup n K (reflection (cartanB n) k γ) := by
  by_cases hk : k.val + 1 < n
  · rw [weylB_conj_shortRoot_of_lt K hk i s c]
    refine shortRoot_mem_oddRootGroup ?_ _
    rw [longWeylBool_true_false, toStdB_reflection_of_lt n hk, hγ, single_comp_swap]
  · rw [weylB_conj_shortRoot_of_not_lt K hk i s c]
    refine shortRoot_mem_oddRootGroup ?_ _
    rw [toStdB_reflection, stdReflB_of_not_lt n hk, hγ]
    funext a
    rw [sign_mul_single]

theorem torusB_conj_mem (k : Fin n) (τ : Kˣ) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) {x : spinGroup (quadOdd n K)}
    (hx : x ∈ oddRootGroup n K γ) :
    torusB K k τ * x * (torusB K k τ)⁻¹ ∈ oddRootGroup n K γ := by
  rcases exists_oddRootGroup_eq (K := K) hγ with ⟨i, j, hij, s, t, hs, h⟩ | ⟨i, s, hs, h⟩
  · rw [h] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective c
    by_cases hk : k.val + 1 < n
    · rw [torusB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp)),
        HypFrame.longTorus_conj_longRoot]
      exact ⟨_, rfl⟩
    · rw [torusB_of_not_lt K hk, OddFrame.shortTorus_conj_longRoot]
      exact ⟨_, rfl⟩
  · rw [h] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective c
    by_cases hk : k.val + 1 < n
    · rw [torusB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp)),
        OddFrame.longTorus_conj_shortRoot]
      exact ⟨_, rfl⟩
    · rw [torusB_of_not_lt K hk, OddFrame.shortTorus_conj_shortRoot]
      exact ⟨_, rfl⟩

theorem cartanB_of_succ {i j : Fin n} (h : i.val + 1 = j.val) : cartanB n i j = -1 := by
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem cartanB_of_pred {i j : Fin n} (h : j.val + 1 = i.val) :
    cartanB n i j = if i.val + 1 = n then -2 else -1 := by
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem cartanB_of_far {i j : Fin n} (hij : i ≠ j) (h₁ : i.val + 1 ≠ j.val)
    (h₂ : j.val + 1 ≠ i.val) : cartanB n i j = 0 := by
  have := Fin.val_ne_of_ne hij
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem coxeterMatrix_cartanB_apply (i j : Fin n) :
    coxeterMatrix (isFiniteType_cartanB n) i j =
      TauCeti.coxeterOrder (cartanB n i j * cartanB n j i) :=
  TauCeti.coxeterMatrixOfCartanMatrix_apply _ _ _ i j

theorem coxeterMatrix_of_succ {i j : Fin n} (h : i.val + 1 = j.val) (hj : j.val + 1 < n) :
    coxeterMatrix (isFiniteType_cartanB n) i j = 3 := by
  rw [coxeterMatrix_cartanB_apply, cartanB_of_succ h, cartanB_of_pred h, ite_eq_right (by omega),
    show (-1 : ℤ) * -1 = 1 by norm_num, TauCeti.coxeterOrder_one]

theorem coxeterMatrix_of_succ_last {i j : Fin n} (h : i.val + 1 = j.val) (hj : j.val + 1 = n) :
    coxeterMatrix (isFiniteType_cartanB n) i j = 4 := by
  rw [coxeterMatrix_cartanB_apply, cartanB_of_succ h, cartanB_of_pred h, ite_eq_left hj,
    show (-1 : ℤ) * -2 = 2 by norm_num, TauCeti.coxeterOrder_two]

theorem coxeterMatrix_of_far {i j : Fin n} (hij : i ≠ j) (h₁ : i.val + 1 ≠ j.val)
    (h₂ : j.val + 1 ≠ i.val) : coxeterMatrix (isFiniteType_cartanB n) i j = 2 := by
  rw [coxeterMatrix_cartanB_apply, cartanB_of_far hij h₁ h₂, zero_mul, TauCeti.coxeterOrder_zero]

theorem weylB_braid_of_lt {i j : Fin n} (hij : i < j) :
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanB n)) i j).map
        (weylB K)).prod =
      ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanB n)) j i).map
        (weylB K)).prod := by
  have hij' : i.val < j.val := hij
  have hsymm := (coxeterMatrix (isFiniteType_cartanB n)).symmetric j i
  rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, hsymm]
  by_cases hadj : i.val + 1 = j.val
  · by_cases hj : j.val + 1 < n
    · rw [show (coxeterMatrix (isFiniteType_cartanB n)).M i j = 3 from
        coxeterMatrix_of_succ hadj hj]
      show ([j, i, j].map (weylB K)).prod = ([i, j, i].map (weylB K)).prod
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      simpa only [mul_assoc] using (weylB_braid_of_succ K hadj hj).symm
    · rw [show (coxeterMatrix (isFiniteType_cartanB n)).M i j = 4 from
        coxeterMatrix_of_succ_last hadj (by omega)]
      show ([i, j, i, j].map (weylB K)).prod = ([j, i, j, i].map (weylB K)).prod
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      simpa only [mul_assoc] using weylB_braid_last K (k := i) (l := j) (by omega) (by omega)
  · rw [show (coxeterMatrix (isFiniteType_cartanB n)).M i j = 2 from
      coxeterMatrix_of_far hij.ne hadj (by omega)]
    show ([i, j].map (weylB K)).prod = ([j, i].map (weylB K)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (weylB_commute K hij.ne hadj (by omega)).eq

end OddCT

open OddCT

variable (n : ℕ) (K : Type) [Field K]

theorem oddDatum_n_mem : ∀ i : Fin n, weylB K i ∈ rankOne (oddRootGroup n K) i := fun k =>
  rankOneB_mem_rankOne k (weylSL2 1)

theorem oddDatum_conj_mem : ∀ i : Fin n, ∀ γ ∈ roots (isFiniteType_cartanB n) ∅,
    ∀ x ∈ oddRootGroup n K γ, weylB K i * x * (weylB K i)⁻¹ ∈
      oddRootGroup n K (weylAction (isFiniteType_cartanB n)
        ((coxeterMatrix (isFiniteType_cartanB n)).toCoxeterSystem.simple i) γ) := by
  intro k γ hγ x hx
  rw [weylAction_simple]
  rcases exists_oddRootGroup_eq (K := K) hγ with ⟨i, j, hij, s, t, hs, h⟩ | ⟨i, s, hs, h⟩
  · rw [h] at hx
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective c
    exact weylB_conj_longRoot_mem k hij s t hs c
  · rw [h] at hx
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective c
    exact weylB_conj_shortRoot_mem k i s hs c

theorem oddDatum_braid : ∀ i j : Fin n,
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanB n)) i j).map (weylB K)).prod =
      ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanB n)) j i).map
        (weylB K)).prod := by
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact weylB_braid_of_lt h
  · rfl
  · exact (weylB_braid_of_lt h).symm

theorem oddDatum_H_le : ∀ i : Fin n, (torusB K i).range ≤ rankOne (oddRootGroup n K) i := by
  rintro k _ ⟨τ, rfl⟩
  exact rankOneB_mem_rankOne k (diagSL2 τ)

theorem oddDatum_sq_mem : ∀ i : Fin n, weylB K i ^ 2 ∈ (torusB K i).range := fun k =>
  ⟨-1, by rw [pow_two, weylB_mul_self]⟩

theorem oddDatum_H_conj_mem : ∀ k : Fin n, ∀ γ ∈ roots (isFiniteType_cartanB n) ∅,
    ∀ h ∈ (torusB K k).range, ∀ x ∈ oddRootGroup n K γ, h * x * h⁻¹ ∈ oddRootGroup n K γ := by
  rintro k γ hγ _ ⟨τ, rfl⟩ x hx
  exact torusB_conj_mem k τ hγ hx

theorem oddDatum_conj_H_mem : ∀ j k : Fin n, ∀ h ∈ (torusB K k).range,
    weylB K j * h * (weylB K j)⁻¹ ∈ (torusB K j).range ⊔ (torusB K k).range := by
  rintro j k _ ⟨τ, rfl⟩
  exact weylB_conj_torusB_mem K j k τ

theorem oddDatum_isCTGroupDatum
    (hgen : ⨆ γ ∈ roots (isFiniteType_cartanB n) ∅, oddRootGroup n K γ = ⊤) :
    IsCTGroupDatum (coxeterMatrix (isFiniteType_cartanB n)).toCoxeterSystem
      (weylAction (isFiniteType_cartanB n)) (roots (isFiniteType_cartanB n) ∅)
      (oddRootGroup n K) (weylB K) (fun k => (torusB K k).range) where
  n_mem := oddDatum_n_mem n K
  conj_mem := oddDatum_conj_mem n K
  braid := oddDatum_braid n K
  H_le := oddDatum_H_le n K
  sq_mem := oddDatum_sq_mem n K
  H_conj_mem := oddDatum_H_conj_mem n K
  conj_H_mem := oddDatum_conj_H_mem n K
  le_rankOne := oddDatum_le_rankOne n K
  iSup_eq_top := hgen

end CFSG.LieType.Universal.Spin
