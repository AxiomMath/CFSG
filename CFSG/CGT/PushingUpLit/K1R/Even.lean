module

public import CFSG.CGT.PushingUpLit.K1R.Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEven

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.EvenBN.GMSK.CatEven
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem even_lie_type_no_inner_root {D : Type} [Group D] [Finite D] (hDs : IsSimpleGroup D)
    (heven : EvenLieType D) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = 2 ^ n) (α : MulAut D) (hα : orderOf α = 2)
    (hin : α ∈ (MulAut.conj : D →* MulAut D).range) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : False := by
  obtain ⟨φ⟩ := hSK
  obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
  set D' : Subgroup (fixedSubgroup α) := S.subgroupOf (fixedSubgroup α) with hD'def
  let eD' : D' ≃* Matrix.SpecialLinearGroup (Fin 2) K := (subgroupOfEquivOfLe hSα).trans φ
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    sl2_isSimpleGroup (two_eq_zero_of_card (by omega) hK) (by
      rw [hK]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hD's : IsSimpleGroup D' := eD'.isSimpleGroup
  have hD'nab : ∃ x y : D', x * y ≠ y * x :=
    ⟨eD'.symm a, eD'.symm b, fun h => hab (by
      have h1 := congrArg eD' h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1)⟩
  have hD' : IsComponent D' :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hD'nab).1, hSn.isSubnormal⟩
  have hZD' : center D' = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hD'nab).2
  have hLie : LieModel (D' ⧸ center D') .PSL 2 2 n :=
    lieModel_PSL_two_of_mulEquiv_SL_two hn hK
      (((QuotientGroup.quotientMulEquivOfEq hZD').trans QuotientGroup.quotientBot).trans eD')
  have hnab : ∃ x y : D, x * y ≠ y * x :=
    ⟨φ.symm a, φ.symm b, fun h => hab (by
      have h1 := congrArg φ (Subtype.ext h : φ.symm a * φ.symm b = φ.symm b * φ.symm a)
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1)⟩
  exact CFSG.SeitzReduction.LinearPilot.catSLmEvenInner D hDs hnab heven α hα hin 2 n D' hD' hLie

theorem innerKernelSelector_evenLieType : InnerKernelSelector fun D _ => EvenLieType D :=
  InnerKernelSelector.of_false fun _ _ _ hDs heven _ hn K _ _ hK α hα hin S hSα hSn hSK _ =>
    even_lie_type_no_inner_root hDs heven hn K hK α hα hin S hSα hSn hSK

end CFSG.CGT.PushingUpLit.K1R
