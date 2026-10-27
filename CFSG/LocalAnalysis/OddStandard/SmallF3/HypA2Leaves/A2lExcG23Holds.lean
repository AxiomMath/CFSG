module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcG23
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)

section Quasi


theorem a2lFixedQuasi_holds : a2lFixedQuasi :=
  fun _ _ _ _ hna h => CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna h

end Quasi

section G23


theorem a2l_g23_explicit {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3) (β : MulAut (adjointGroup ReeTag.G2.tag K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    LieModel L .PSL 2 2 3 := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hK1 : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  rcases G2_three_involution_inner_quadratic_or_exceptional (f := 1) le_rfl hK1 hβ2 with
    ⟨g, a, hβg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hβg⟩ | ⟨b, g, hfb, rfl⟩
  ·
    exfalso
    have hKodd : Odd (Nat.card K) := by rw [hK]; decide
    obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
      exists_toralCentralizer_equiv_of_innerDiag (Or.inl rfl) hKodd hβg hβ2
    have hβ1 : β ≠ 1 := fun h => by
      rw [h, orderOf_one] at hβ
      exact absurd hβ (by norm_num)
    obtain ⟨-, -, -, -, hq3⟩ := odd_G2_toral_involution_fixed_p_components K hKodd b hb
    have hsolv : Group.IsSolvable (toralCentralizer .G2 K b) := (hq3 hK (hb1 hβ1)).1
    haveI : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
      (f := (Ψ.trans Θ).toMonoidHom) (Ψ.trans Θ).injective
    exact not_isComponent_of_isSolvable hL
  ·
    exfalso
    have h3 : 3 ≤ 3 ^ e := calc
      (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
    rw [hK] at hKe
    nlinarith
  ·
    obtain rfl : b = 0 := by omega
    have hK' : Nat.card K = 3 ^ (2 * 0 + 1) := by rw [hK]; norm_num
    obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
      LieType.Ree.G2_exceptional_coset_involution_fixed_p_components 0 K hK' g hβ2
    have hc : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K 0) =
        ReeTag.G2.finiteReeAut K 0 :=
      (MulEquiv.ext fun _ => rfl : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K 0) =
        ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K 0) * ψ⁻¹).trans hψ
    have hmap : (fixedSubgroup (ReeTag.G2.finiteReeAut K 0)).map
        (adjointGroup ReeTag.G2.tag K).subtype = ReeTag.G2.reeGamma K 0 := rfl
    have hFc : fixedSubgroup (MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K 0)) =
        fixedSubgroup (ReeTag.G2.finiteReeAut K 0) := by rw [hc]
    let Ψ' : X ≃* ReeTag.G2.reeGamma K 0 := Ψ.trans ((fixedSubgroupCongrEquiv ψ _).trans
      ((MulEquiv.subgroupCongr hFc).trans
        (((fixedSubgroup (ReeTag.G2.finiteReeAut K 0)).equivMapOfInjective _
          Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap))))
    obtain ⟨hDs, -, -, -, -, -⟩ :=
      CatalogueBSmallRee.small_Ree_whole_group_p_components 0 K hK'
    set Γ := ReeTag.G2.reeGamma K 0 with hΓ
    have eJ : commutator Γ ≃* (commutator Γ).map Γ.subtype :=
      (commutator Γ).equivMapOfInjective _ Subtype.val_injective
    have : IsSimpleGroup ((commutator Γ).map Γ.subtype) := (MulEquiv.isSimpleGroup_congr eJ).1 hDs
    have hJF : (commutator Γ).map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
    have hJsub : ((commutator Γ).map Γ.subtype).subgroupOf Γ = commutator Γ :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    have hJn : (((commutator Γ).map Γ.subtype).subgroupOf Γ).Normal := by
      rw [hJsub]
      exact Subgroup.commutator_normal ⊤ ⊤
    have hsolv : Group.IsSolvable (Γ ⧸ ((commutator Γ).map Γ.subtype).subgroupOf Γ) := by
      have : Group.IsSolvable (Abelianization Γ) := inferInstance
      exact Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
        (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
    obtain ⟨E⟩ := nonempty_component_equiv_of_normal_simple hJF hJn hsolv Ψ' hL
    obtain ⟨-, -, -, -, -, -, h0⟩ :=
      LiteratureLocal.small_Ree_G2_fixed_points_and_Ree3_PGammaL2_8 0 K hK'
    obtain ⟨-, -, -, -, hstated, -⟩ := h0 rfl
    have hL0 : LieModel (commutator Γ) .PSL 2 2 3 := Or.inl ⟨by decide, hstated⟩
    exact LieType.CurtisTits.lieModel_of_mulEquiv (E.trans eJ.symm).symm hL0

theorem a2lG23Comp_holds : a2lG23Comp := by
  intro S _ hS α hα L hL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hS).2 :
      UntwistedChevalleyModel S .G2 (3 ^ 1))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have : CharP F ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three le_rfl
      hF
  exact a2l_g23_explicit (K := F) (by simpa using hF) _ hβ (fixedSubgroupCongrEquiv e α) hL

end G23

end CFSG.OddStandard.SmallF3.HypA2Leaves
