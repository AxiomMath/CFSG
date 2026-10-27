module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear
public import CFSG.ClassicalInvolution.WeakCT.Center

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

section Diagonal

variable {F : Type} [Field F] {n : ℕ}

theorem single_mul_diagonal_eq (e : Fin n → F) (i j : Fin n) :
    Matrix.single i j (1 : F) * Matrix.diagonal e = e j • Matrix.single i j (1 : F) := by
  ext p q
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hp : i = p <;> by_cases hq : j = q <;> simp [hp, hq]

theorem diagonal_mul_single_eq (e : Fin n → F) (i j : Fin n) :
    Matrix.diagonal e * Matrix.single i j (1 : F) = e i • Matrix.single i j (1 : F) := by
  ext p q
  simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hp : i = p <;> by_cases hq : j = q <;> simp [hp, hq]

theorem transvection_mem_longRootGroup_diagonal (e : Fin n → F) {i j : Fin n} (hij : i ≠ j)
    (hee : e i = e j) (hj : 1 + e j = 0) :
    Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈ longRootGroup (Matrix.diagonal e) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.transvection_coe, add_mul, mul_add, Matrix.one_mul,
      Matrix.mul_one, single_mul_diagonal_eq, diagonal_mul_single_eq, hee]
  · have h : Matrix.single i j (1 : F) + e j • Matrix.single i j (1 : F) = 0 := by
      calc Matrix.single i j (1 : F) + e j • Matrix.single i j (1 : F)
          = (1 + e j) • Matrix.single i j (1 : F) := by rw [add_smul, one_smul]
        _ = 0 := by rw [hj, zero_smul]
    rw [Matrix.SpecialLinearGroup.transvection_coe, add_mul, Matrix.one_mul, mul_add,
      Matrix.mul_one, single_mul_diagonal_eq, h, add_zero]

theorem mul_self_eq_one_of_commute_single [Fintype F] (hF : Fintype.card F = 3)
    (h2 : (2 : F) ≠ 0) (e : Fin n → F) (he : ∀ p, e p = 1 ∨ e p = -1)
    {ν : Matrix (Fin n) (Fin n) F} (hdet : ν.det = 1)
    (hD : ν * Matrix.diagonal e = Matrix.diagonal e * ν)
    (hs : ∀ i j, i ≠ j → e i = e j → Commute (Matrix.single i j (1 : F)) ν) : ν * ν = 1 := by
  have hoff : ∀ p q, p ≠ q → ν p q = 0 := by
    intro p q hpq
    by_cases hep : e p = e q
    · exact row_eq_zero_of_commute_single (hs q p hpq.symm hep.symm) hpq.symm
    · have h := congrFun (congrFun hD p) q
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      rcases he p with hp | hp <;> rcases he q with hq | hq
      · exact absurd (hp.trans hq.symm) hep
      · rw [hp, hq] at h
        have h3 : (2 : F) * ν p q = 0 := by linear_combination -h
        exact (mul_eq_zero.mp h3).resolve_left h2
      · rw [hp, hq] at h
        have h3 : (2 : F) * ν p q = 0 := by linear_combination h
        exact (mul_eq_zero.mp h3).resolve_left h2
      · exact absurd (hp.trans hq.symm) hep
  have hdiag : ν = Matrix.diagonal (fun p => ν p p) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [Matrix.diagonal_apply_ne _ hpq, hoff p q hpq]
  have hsq : ∀ p, ν p p * ν p p = 1 := by
    intro p
    have hp : ν p p ≠ 0 := by
      intro hp
      have h0 : ν.det = 0 := Matrix.det_eq_zero_of_row_eq_zero p fun q => by
        by_cases hpq : p = q
        · subst hpq
          exact hp
        · exact hoff p q hpq
      rw [hdet] at h0
      exact one_ne_zero h0
    have := FiniteField.pow_card_sub_one_eq_one (ν p p) hp
    rw [hF] at this
    simpa [pow_two] using this
  calc ν * ν = Matrix.diagonal (fun p => ν p p) * Matrix.diagonal (fun p => ν p p) := by
        rw [← hdiag]
    _ = Matrix.diagonal (fun p => ν p p * ν p p) := Matrix.diagonal_mul_diagonal _ _
    _ = 1 := by
        rw [← Matrix.diagonal_one]
        congr 1
        funext p
        exact hsq p

end Diagonal

section Main

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem commute_single_of_mul_transvection {n : ℕ} {ν : SL(n, F)} {i j : Fin n} (hij : i ≠ j)
    (h : ν * Matrix.SpecialLinearGroup.transvection hij (1 : F) =
      Matrix.SpecialLinearGroup.transvection hij (1 : F) * ν) :
    Commute (Matrix.single i j (1 : F)) (ν : Matrix (Fin n) (Fin n) F) := by
  have h' := congrArg (fun y : SL(n, F) => (y : Matrix (Fin n) (Fin n) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    mul_add, add_mul, Matrix.mul_one, Matrix.one_mul] at h'
  exact (add_left_cancel h').symm

omit [Finite F] in
theorem negBlockK_compl {n a : ℕ} (han : a ≤ n) :
    negBlockK F n a (n - a) = -negBlockK F n 0 a := by
  rw [negBlockK_eq_diagonal, negBlockK_eq_diagonal, Matrix.diagonal_neg]
  congr 1
  funext x
  have hx := x.isLt
  by_cases h : x.val < a
  · have h1 : ¬ (a ≤ x.val) := by omega
    simp [h, h1]
  · have h1 : a ≤ x.val ∧ x.val < a + (n - a) := ⟨by omega, by omega⟩
    simp [h, h1]

theorem oddCoreIn_centralizer_eq_bot_of_blockDiag (hF : Nat.card F = 3) {n a : ℕ} (ha : 0 < a)
    (han : a < n) (g : SL(n, F))
    (hg : (g : Matrix (Fin n) (Fin n) F) = negBlockK F n 0 a) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g : SL(n, F) ⧸ Subgroup.center SL(n, F))} :
        Set (SL(n, F) ⧸ Subgroup.center SL(n, F)))) = ⊥ := by
  have h2 : (2 : F) ≠ 0 :=
    two_ne_zero_of_odd_natCard (by rw [hF]; decide)
  have hn1 : 1 ≤ n := by omega
  set D : Matrix (Fin n) (Fin n) F := negBlockK F n 0 a with hD
  have hDc : negBlockK F n a (n - a) = -D := negBlockK_compl han.le
  have hcomm : ∀ x : SL(n, F), x ∈ Subgroup.centralizer ({g} : Set SL(n, F)) ↔
      (x : Matrix (Fin n) (Fin n) F) * D = D * x := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg (fun y : SL(n, F) => (y : Matrix (Fin n) (Fin n) F)) h
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
    · intro h
      ext i j
      have h' := congrFun (congrFun h i) j
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
  have hneg : ∀ x : SL(n, F), (x : Matrix (Fin n) (Fin n) F) * (-D) = (-D) * x ↔
      (x : Matrix (Fin n) (Fin n) F) * D = D * x := by
    intro x
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  refine oddCoreIn_centralizer_eq_bot_of_blocks (isPGroup_center_specialLinear hF hn1) g
    (ι := Bool) (fun b => cond b (longRootGroup (negBlockK F n a (n - a)))
      (longRootGroup (negBlockK F n 0 a))) ?_ ?_ ?_ ?_
  · intro b x hx
    cases b
    · exact (hcomm x).mpr hx.1
    · refine (hcomm x).mpr ((hneg x).mp ?_)
      rw [← hDc]
      exact hx.1
  · intro b c hc x hx
    have hc' := (hcomm c).mp hc
    cases b
    · exact conj_mem_longRootGroup_of_commute hc' hx
    · rw [hDc]
      rw [hDc] at hx
      exact conj_mem_longRootGroup_of_commute ((hneg c).mpr hc') hx
  · intro b
    set θ := QuotientGroup.mk' (Subgroup.center SL(n, F)) with hθ
    have hker : θ.ker ≤ Subgroup.center SL(n, F) := (QuotientGroup.ker_mk' _).le
    cases b
    · have hr := range_blockSL_eq_longRootGroupK h2 (n := n) (j := 0) (k := a) (by omega)
      show oddCoreIn ((longRootGroup (negBlockK F n 0 a)).map θ) = ⊥
      rw [← hr, ← MonoidHom.range_comp]
      exact oddCoreIn_range_eq_bot_of_injective _ (comp_blockSL_injective hker _ han)
        (componentOddCore_specialLinear_eq_bot hF a)
    · have hr := range_blockSL_eq_longRootGroupK h2 (n := n) (j := a) (k := n - a) (by omega)
      show oddCoreIn ((longRootGroup (negBlockK F n a (n - a))).map θ) = ⊥
      rw [← hr, ← MonoidHom.range_comp]
      exact oddCoreIn_range_eq_bot_of_injective _ (comp_blockSL_injective hker _ (by omega))
        (componentOddCore_specialLinear_eq_bot hF (n - a))
  · intro ν hν hL
    have hνD := (hcomm ν).mp hν
    refine ⟨1, ?_⟩
    let _ : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
    set e : Fin n → F := fun p => if a ≤ p.val then 1 else -1 with he_def
    have hDe : D = Matrix.diagonal e := by
      rw [hD, negBlockK_eq_diagonal]
      congr 1
      funext p
      by_cases h : p.val < a
      · simp [e, h, not_le.mpr h]
      · simp [e, h, not_lt.mp h]
    have hnegDe : -D = Matrix.diagonal (fun p => -e p) := by rw [hDe, Matrix.diagonal_neg]
    have he : ∀ p, e p = 1 ∨ e p = -1 := fun p => by
      by_cases h : a ≤ p.val
      · exact Or.inl (by simp [e, h])
      · exact Or.inr (by simp [e, h])
    have key := mul_self_eq_one_of_commute_single hcard h2 e he ν.2 (by rw [← hDe]; exact hνD) ?_
    · have : ν * ν = 1 := by
        ext i j
        have h' := congrFun (congrFun key i) j
        simpa [Matrix.SpecialLinearGroup.coe_mul] using h'
      simpa [pow_two] using this
    · intro i j hij hee
      rcases he i with h1 | h1
      · have hj1 : e j = 1 := hee ▸ h1
        have hx : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
            longRootGroup (negBlockK F n a (n - a)) := by
          rw [hDc, hnegDe]
          exact transvection_mem_longRootGroup_diagonal _ hij (by simp [hee]) (by simp [hj1])
        exact commute_single_of_mul_transvection hij (hL true _ hx)
      · have hj1 : e j = -1 := hee ▸ h1
        have hx : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
            longRootGroup (negBlockK F n 0 a) := by
          rw [← hD, hDe]
          exact transvection_mem_longRootGroup_diagonal e hij hee (by simp [hj1])
        exact commute_single_of_mul_transvection hij (hL false _ hx)

end Main

end CFSG.ClassicalInvolution.Q3
