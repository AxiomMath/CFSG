module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Block
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInnerY

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem asc82Omega8MinusData_holds : Asc82Omega8MinusData := by
  intro G _ _ L hL hmod
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := isOmegaStar_of_lieModel_minus hmod
  letI := i1
  letI := i2
  letI := i3
  have hπQ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim, hs]
    decide
  obtain ⟨e'⟩ := nonempty_omegaGroup_mulEquiv_omegaProj hQ hπQ
  let E : ↥L ⧸ oddCore ↥L ≃* omegaGroup hQ := e.trans e'.symm
  let ρ : ↥L →* omegaGroup hQ := E.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥L))
  have hρ : OddCentralCover ρ := oddCentralCover_quotient_oddCore hL.1 E
  obtain ⟨zb, hzb2, hpocket, Xb, hXb, hXbmodel, hXbodd⟩ :=
    exists_involution_component_four_minus hQ hdim hs
  have hzb : zb * zb = 1 := by
    rw [← pow_two]
    exact hzb2 ▸ pow_orderOf_eq_one zb
  obtain ⟨⟨w, hwL⟩, hww, hρw⟩ := hρ.exists_mul_self_eq_one_lift hzb
  have hρw' : E (QuotientGroup.mk (⟨w, hwL⟩ : ↥L)) = zb := hρw
  have hw1 : (⟨w, hwL⟩ : ↥L) ≠ 1 := by
    intro h
    have h1 : zb = 1 := by rw [← hρw, h, map_one]
    rw [h1, orderOf_one] at hzb2
    omega
  have hw2 : orderOf w = 2 :=
    (Subgroup.orderOf_mk w hwL).symm.trans
      (orderOf_eq_prime (by rw [pow_two]; exact hww) hw1)
  have hXq : CFSG.IsQuasisimple ↥Xb := hXb.isQuasisimple
  have hpocketL : IsI4PlusIn L w := by
    have h1 := isI4PlusIn_top_map_mulEquiv E.symm hpocket
    have h2 : E.symm zb = QuotientGroup.mk (⟨w, hwL⟩ : ↥L) := by
      rw [← hρw']
      exact E.symm_apply_apply _
    rw [h2] at h1
    exact isI4PlusIn_of_quotient hwL hw2 h1
  have hXc : IsComponentIn Xb (centralizer ({ρ ⟨w, hwL⟩} : Set (omegaGroup hQ))) := by
    rw [hρw]
    exact hXb
  have hDcomp := hρ.isComponentIn_coverDerived hww hXc
  have hJcomp : IsComponentIn ((coverDerived ρ Xb).map L.subtype)
      (L ⊓ centralizer ({w} : Set G)) := by
    have := isComponentIn_map_of_injective L.subtype L.subtype_injective hDcomp
    rwa [map_subtype_centralizer L hwL] at this
  refine ⟨w, hpocketL, (coverDerived ρ Xb).map L.subtype, hJcomp, ?_⟩
  have hcov := hρ.oddCentralCover_coverDerivedHom hXq
  have hker : oddCore ↥(coverDerived ρ Xb) = (coverDerivedHom ρ Xb).ker :=
    hcov.oddCore_eq_ker hXbodd
  let eD : ↥(coverDerived ρ Xb) ⧸ oddCore ↥(coverDerived ρ Xb) ≃* ↥Xb :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hcov.surjective)
  have hDF : IsFStarGroup ↥(coverDerived ρ Xb) :=
    Or.inr ⟨hρ.isQuasisimple_coverDerived hXq, Or.inl (LieModel.of_mulEquiv eD.symm hXbmodel)⟩
  exact isFStarGroup_of_mulEquiv ((coverDerived ρ Xb).equivMapOfInjective L.subtype
    L.subtype_injective) hDF

end CFSG.OddStandard.SmallF3.Omega
