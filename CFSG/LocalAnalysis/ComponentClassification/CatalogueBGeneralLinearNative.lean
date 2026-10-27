module

public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.CatalogueBGeneralLinear

noncomputable section

open Matrix

universe u

abbrev specialLinearRange (n : ℕ) (K : Type u) [Field K] :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) K) :=
  (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin n) K →* Matrix.GeneralLinearGroup (Fin n) K).range

@[expose] def specialLinearEquivRange (n : ℕ) (K : Type u) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K ≃* specialLinearRange n K :=
  MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective

theorem specialLinearEquivRange_val (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.SpecialLinearGroup (Fin n) K) :
    (specialLinearEquivRange n K A).val = Matrix.SpecialLinearGroup.toGL A := rfl

@[expose] def rangeEquivSpecialLinear (n : ℕ) (K : Type u) [Field K] :
    specialLinearRange n K ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  (specialLinearEquivRange n K).symm

theorem rangeEquivSpecialLinear_toGL (n : ℕ) (K : Type u) [Field K]
    (A : specialLinearRange n K) :
    Matrix.SpecialLinearGroup.toGL (rangeEquivSpecialLinear n K A) = A.val := by
  exact congrArg Subtype.val ((specialLinearEquivRange n K).apply_symm_apply A)

theorem specialLinearRange_eq_detKernel (n : ℕ) (K : Type u) [Field K] :
    specialLinearRange n K = (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) K →* Kˣ).ker :=
  Matrix.SpecialLinearGroup.range_toGL_eq_ker_det

instance specialLinearRangeNormal (n : ℕ) (K : Type u) [Field K] :
    (specialLinearRange n K).Normal := by
  rw [specialLinearRange_eq_detKernel]
  infer_instance

@[expose] def determinantQuotientHom (n : ℕ) (K : Type u) [Field K] :
    Matrix.GeneralLinearGroup (Fin n) K ⧸ specialLinearRange n K →* Kˣ :=
  QuotientGroup.lift (specialLinearRange n K) Matrix.GeneralLinearGroup.det
    (le_of_eq (specialLinearRange_eq_detKernel n K))

theorem determinantQuotientHom_injective (n : ℕ) (K : Type u) [Field K] :
    Function.Injective (determinantQuotientHom n K) := by
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr
    (specialLinearRange_eq_detKernel n K)

theorem determinantQuotient_commutative (n : ℕ) (K : Type u) [Field K] :
    IsMulCommutative (Matrix.GeneralLinearGroup (Fin n) K ⧸ specialLinearRange n K) := by
  apply isMulCommutative_iff.mpr
  intro A B
  apply determinantQuotientHom_injective n K
  simp only [map_mul, mul_comm]

theorem determinantQuotient_solvable (n : ℕ) (K : Type u) [Field K] :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin n) K ⧸ specialLinearRange n K) :=
  Group.isSolvable_of_isSolvable_injective (determinantQuotientHom_injective n K)

theorem specialLinear_perfect (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (h22 : n ≠ 2 ∨ Nat.card K ≠ 2)
    (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) := by
  by_cases hn2 : n = 2
  · subst n
    have hK : 4 ≤ Nat.card K := by
      have htwo : 2 ≤ Nat.card K := Nat.succ_le_iff.mpr Finite.one_lt_card
      simp only [ne_eq, not_true_eq_false, false_or] at h22 h23
      omega
    exact CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  · exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)

theorem projectiveSpecialLinear_simple (n : ℕ) (K : Type u) [Field K]
    (hn : 2 ≤ n) (h22 : n ≠ 2 ∨ Nat.card K ≠ 2)
    (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
  CFSG.BenderSuzuki.External.huppert_II_6_13 n hn h22 h23

theorem specialLinear_quasisimple (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (h22 : n ≠ 2 ∨ Nat.card K ≠ 2)
    (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin n) K) := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    specialLinear_perfect n K hn h22 h23
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
    projectiveSpecialLinear_simple n K hn h22 h23
  apply CatalogueBAlternating.quasisimple_iff_native.mpr
  exact ⟨Group.IsPerfect.commutator_eq_top, inferInstance⟩

theorem specialLinearRange_quasisimple (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (h22 : n ≠ 2 ∨ Nat.card K ≠ 2)
    (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (specialLinearRange n K) :=
  CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (rangeEquivSpecialLinear n K)
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (specialLinear_quasisimple n K hn h22 h23)))

end

end CFSG.ComponentClassification.CatalogueBGeneralLinear
