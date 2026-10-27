module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.CoverLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PerfectCover
open scoped commutatorElement

section Abstract

variable {Y P : Type} [Group Y] [Group P]

theorem mem_innAutDerived_of_inv_lift [Group.IsPerfect Y] (e : (Y ⧸ Subgroup.center Y) ≃* P)
    {α τ : MulAut Y} (h3 : α ^ 3 = 1)
    (hinn : IsInnerAut (MulAut.congr e (centerDescend Y τ) * MulAut.congr e (centerDescend Y α) *
      (MulAut.congr e (centerDescend Y τ))⁻¹ * MulAut.congr e (centerDescend Y α))) :
    α ∈ innAutDerived Y := by
  have hc : ⁅τ, α⁆ ∈ commutator (MulAut Y) := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hprod : ⁅τ, α⁆ * α ^ 2 = τ * α * τ⁻¹ * α := by
    rw [commutatorElement_def]
    group
  have hinn' : IsInnerAut (⁅τ, α⁆ * α ^ 2) := by
    rw [hprod]
    have h1 : IsInnerAut (MulAut.congr e (centerDescend Y (τ * α * τ⁻¹ * α))) := by
      have : MulAut.congr e (centerDescend Y (τ * α * τ⁻¹ * α)) =
          MulAut.congr e (centerDescend Y τ) * MulAut.congr e (centerDescend Y α) *
            (MulAut.congr e (centerDescend Y τ))⁻¹ * MulAut.congr e (centerDescend Y α) := by
        simp only [map_mul, map_inv]
      rw [this]
      exact hinn
    exact isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr e _).1 h1)
  have hinner : ⁅τ, α⁆ * α ^ 2 ∈ innAutDerived Y := innerAut_le_innAutDerived Y hinn'
  have hα2 : α ^ 2 ∈ innAutDerived Y := by
    have hα2eq : α ^ 2 = (⁅τ, α⁆)⁻¹ * (⁅τ, α⁆ * α ^ 2) := by group
    rw [hα2eq]
    exact (innAutDerived Y).mul_mem ((innAutDerived Y).inv_mem
      (commutator_le_innAutDerived Y hc)) hinner
  have : α = (α ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
  rw [this]
  exact (innAutDerived Y).pow_mem hα2 2

end Abstract

section Psl

variable {n : ℕ} {K : Type} [Field K]

theorem det_inverseTranspose_psl (A : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose A) =
      (GeneralLinearGroup.det A)⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

theorem isInnerAut_dual_conj_mul (A : GL (Fin n) K) :
    IsInnerAut (dualAut n K * conjAut n K A * (dualAut n K)⁻¹ * conjAut n K A) := by
  rw [dualAut_mul_conjAut A, mul_inv_cancel_right, ← map_mul]
  refine conjAut_mem_range_conj_of_det_eq_pow (μ := 1) ?_
  rw [map_mul, det_inverseTranspose_psl, inv_mul_cancel, one_pow]

end Psl

theorem mem_innAutDerived_of_diag_psl {n : ℕ} {K : Type} [Field K] [Finite K] {Y : Type} [Group Y]
    [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) (e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL n K)
    (hM : IsCyclic (hopfMultiplier (Y ⧸ Subgroup.center Y))) {α : MulAut Y} (h3 : α ^ 3 = 1)
    (hD : MulAut.congr e (centerDescend Y α) ∈ linearAutGroup n K) : α ∈ innAutDerived Y := by
  classical
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  haveI : Finite (Y ⧸ Subgroup.center Y) := inferInstance
  haveI : Group.IsPerfect (Y ⧸ Subgroup.center Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center Y))
      (QuotientGroup.mk'_surjective _)
  set π : Y →* (Y ⧸ Subgroup.center Y) := QuotientGroup.mk' (Subgroup.center Y) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le
  obtain ⟨τY, hτY⟩ := exists_lift_aut_of_cyclic_multiplier hM π hπ hπker
    (MulAut.congr e.symm (dualAut n K))
  refine mem_innAutDerived_of_inv_lift e h3 (τ := τY) ?_
  have hρτ : MulAut.congr e (centerDescend Y τY) = dualAut n K := by
    refine MulEquiv.ext fun p => ?_
    obtain ⟨y, rfl⟩ : ∃ y : Y, e (QuotientGroup.mk y) = p := by
      obtain ⟨q, rfl⟩ := e.surjective p
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨y, rfl⟩
    rw [← descend_compat e τY y]
    have h1 := hτY y
    have h2 : (QuotientGroup.mk (τY y) : Y ⧸ Subgroup.center Y) =
        e.symm (dualAut n K (e (QuotientGroup.mk y))) := by
      simpa [hπdef, MulAut.congr_apply] using h1
    rw [h2]
    simp
  rw [hρτ]
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hD
  rw [← hA]
  exact isInnerAut_dual_conj_mul A

end CFSG.HardMathSupport.Dickson.Sec6.I923
