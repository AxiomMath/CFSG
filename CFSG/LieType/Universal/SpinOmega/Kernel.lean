module

public import CFSG.LieType.Universal.SpinCenterMinus
public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.LieType.Universal.Spin.RootElements

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

theorem mem_ker_spinAction_of_coe_eq_neg_one {x : spinGroup Q}
    (hx : (x : CliffordAlgebra Q) = -1) : x ∈ (spinAction Q).ker := by
  rw [MonoidHom.mem_ker]
  refine LinearEquiv.ext fun v => ?_
  rw [spinAction_apply_eq_iff', hx, neg_one_mul, mul_neg_one]
  rfl

theorem mem_ker_spinAction_iff_of_isCentral [Algebra.IsCentral K (CliffordAlgebra Q)]
    (x : spinGroup Q) :
    x ∈ (spinAction Q).ker ↔ x = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  constructor
  · intro hx
    rcases eq_one_or_eq_neg_one_of_commute
      (fun v => commute_of_mem_ker_spinAction Q hx (ι Q v)) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact one_mem _
    · exact mem_ker_spinAction_of_coe_eq_neg_one Q h

theorem eq_negOne_iff (hQ : Q ≠ 0) (x : spinGroup Q) :
    x = spinGroup.negOne Q hQ ↔ (x : CliffordAlgebra Q) = -1 := by
  rw [Subtype.ext_iff, spinGroup.coe_negOne]

theorem neg_one_eq_one_of_two_eq_zero (h2 : (2 : K) = 0) : (-1 : CliffordAlgebra Q) = 1 := by
  have h : (1 : CliffordAlgebra Q) + 1 = 0 := by
    rw [one_add_one_eq_two, ← map_ofNat (algebraMap K (CliffordAlgebra Q)) 2, h2, map_zero]
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem ker_spinAction_eq_bot_of_isCentral [Algebra.IsCentral K (CliffordAlgebra Q)]
    (h2 : (2 : K) = 0) : (spinAction Q).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  rcases (mem_ker_spinAction_iff_of_isCentral Q x).mp hx with h | h
  · exact h
  · exact Subtype.ext (h.trans (neg_one_eq_one_of_two_eq_zero Q h2))

end General

section Matrix

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : QuadraticForm K (σ → K))

theorem ker_spinMatrix : (spinMatrix Q).ker = (spinAction Q).ker := by
  ext x
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    refine LinearEquiv.ext fun v => ?_
    rw [← spinMatrix_mulVec, h, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro h
    ext i j
    rw [coe_spinMatrix, h]
    simp [LinearMap.toMatrix'_apply, Pi.single_apply, Matrix.one_apply]

end Matrix

section Forms

variable {n : ℕ} {K : Type} [Field K]

theorem mem_ker_spinMatrix_quadOdd_iff (h2 : (2 : K) ≠ 0) (x : spinGroup (quadOdd n K)) :
    x ∈ (spinMatrix (quadOdd n K)).ker ↔ x = 1 ∨ (x : CliffordAlgebra (quadOdd n K)) = -1 := by
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  rw [ker_spinMatrix, mem_ker_spinAction_iff (quadOdd n K) (nondegenerate_quadOdd n K) x,
    eq_negOne_iff]

theorem mem_ker_spinMatrix_quadPlus_iff (x : spinGroup (quadPlus n K)) :
    x ∈ (spinMatrix (quadPlus n K)).ker ↔ x = 1 ∨ (x : CliffordAlgebra (quadPlus n K)) = -1 := by
  have := isCentral_cliffordAlgebra_quadPlus K n
  rw [ker_spinMatrix, mem_ker_spinAction_iff_of_isCentral]

theorem ker_spinMatrix_quadPlus_eq_bot (h2 : (2 : K) = 0) :
    (spinMatrix (quadPlus n K)).ker = ⊥ := by
  have := isCentral_cliffordAlgebra_quadPlus K n
  rw [ker_spinMatrix, ker_spinAction_eq_bot_of_isCentral _ h2]

variable {b c : K}

theorem mem_ker_spinMatrix_quadMinus_iff [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x : spinGroup (quadMinus n K b c)) :
    x ∈ (spinMatrix (quadMinus n K b c)).ker ↔
      x = 1 ∨ (x : CliffordAlgebra (quadMinus n K b c)) = -1 := by
  have := isCentral_cliffordAlgebra_quadMinus n b c hirr
  rw [ker_spinMatrix, mem_ker_spinAction_iff_of_isCentral]

theorem ker_spinMatrix_quadMinus_eq_bot [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : K) = 0) : (spinMatrix (quadMinus n K b c)).ker = ⊥ := by
  have := isCentral_cliffordAlgebra_quadMinus n b c hirr
  rw [ker_spinMatrix, ker_spinAction_eq_bot_of_isCentral _ h2]

end Forms

section Sets

variable {n : ℕ} {K : Type} [Field K]

theorem coe_ker_spinMatrix_quadOdd (h2 : (2 : K) ≠ 0) :
    ((spinMatrix (quadOdd n K)).ker : Set (spinGroup (quadOdd n K))) =
      {1, spinGroup.negOne _ (nondegenerate_quadOdd n K).ne_zero} := by
  ext x
  rw [SetLike.mem_coe, mem_ker_spinMatrix_quadOdd_iff h2, Set.mem_insert_iff,
    Set.mem_singleton_iff, eq_negOne_iff]

theorem coe_ker_spinMatrix_quadPlus [NeZero n] :
    ((spinMatrix (quadPlus n K)).ker : Set (spinGroup (quadPlus n K))) =
      {1, spinGroup.negOne _ (nondegenerate_quadPlus n K).ne_zero} := by
  ext x
  rw [SetLike.mem_coe, mem_ker_spinMatrix_quadPlus_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, eq_negOne_iff]

variable {b c : K}

theorem coe_ker_spinMatrix_quadMinus [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((spinMatrix (quadMinus n K b c)).ker : Set (spinGroup (quadMinus n K b c))) =
      {1, spinGroup.negOne _ (nondegenerate_quadMinus_of_finite n K hirr).ne_zero} := by
  ext x
  rw [SetLike.mem_coe, mem_ker_spinMatrix_quadMinus_iff hirr, Set.mem_insert_iff,
    Set.mem_singleton_iff, eq_negOne_iff]

end Sets

end CFSG.LieType.Universal.Spin
