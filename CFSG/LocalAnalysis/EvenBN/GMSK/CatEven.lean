module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuter
public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace CatEven

theorem lieModel_PSL_two_of_mulEquiv_SL_two {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : LieModel X .PSL 2 2 n :=
  CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two hn hK e

end CatEven

open CatEven

section Selector

theorem even_lie_type_fixed_root_selector {D : Type} [Group D] [Finite D]
    (hDs : IsSimpleGroup D) (heven : EvenLieType D) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K]
    [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) (hr : FixedRootRankOne α S) :
    LieModel D .PSL 2 2 (2 * n) ∨ LieModel D .PSU 3 2 n ∨ LieModel D .PSL 3 2 n := by
  obtain ⟨φ⟩ := hSK
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    sl2_isSimpleGroup (two_eq_zero_of_card (by omega) hK) (by
      rw [hK]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
  set D' : Subgroup (fixedSubgroup α) := S.subgroupOf (fixedSubgroup α) with hD'def
  let eD' : D' ≃* Matrix.SpecialLinearGroup (Fin 2) K := (subgroupOfEquivOfLe hSα).trans φ
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
  have hmap : D'.map (fixedSubgroup α).subtype = S := by
    rw [hD'def, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (show S ≤ fixedSubgroup α from hSα)]
  have hsmall : CFSG.SeitzReduction.LinearPilot.FixedCentralizerTwoSmall α D' := by
    intro U hU hUc hUfix
    rw [hmap] at hUc
    exact (hr U (le_inf hUfix hUc) hU).1
  have hnab : ∃ x y : D, x * y ≠ y * x :=
    ⟨φ.symm a, φ.symm b, fun h => hab (by
      have h1 := congrArg φ (Subtype.ext h : φ.symm a * φ.symm b = φ.symm b * φ.symm a)
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1)⟩
  by_cases hin : α ∈ (MulAut.conj : D →* MulAut D).range
  · exact (CFSG.SeitzReduction.LinearPilot.catSLmEvenInner D hDs hnab heven α hα hin 2 n D' hD'
      hLie).elim
  · exact CFSG.SeitzReduction.RankOne.catSL2EvenOuterList n D hDs hnab heven α hin
      ⟨hα, D', hD', hLie, hsmall⟩

theorem fixedRootSelector_evenLieType : FixedRootSelector fun D _ => EvenLieType D := by
  intro D _ _ hDs heven n hn K _ _ hK α hα S hSα hSn hSK hr
  rcases even_lie_type_fixed_root_selector hDs heven hn K hK α hα S hSα hSn hSK hr with
    h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

end Selector

end CFSG.LocalAnalysis.EvenBN.GMSK
