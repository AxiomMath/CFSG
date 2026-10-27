module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem fj_exists_component_of_layerModel {P : Type} [Group P] [Finite P] {H : Subgroup P}
    {t : CFSG.Open.StatedLieTag} {n k : ℕ}
    (hsh : ∀ (E : Type) [Group E], LieModel E t n 3 k →
      IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E)
    (hLM : LayerModel ↥H t n k) {B : Subgroup P} (hBH : B ≤ H)
    (hB : B ≤ Subgroup.closure {c : P | c ∈ B ∧ Odd (orderOf c)}) :
    ∃ J : Subgroup P, IsComponentIn J H ∧ InFStar J ∧ B ≤ J := by
  obtain ⟨E, hEn, hLie, h2⟩ := hLM
  obtain ⟨hs, hnc, hF⟩ := hsh ↥E hLie
  haveI := hEn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E' : Subgroup P := E.map H.subtype
  have hE'H : E' ≤ H := Subgroup.map_subtype_le E
  have hsub : E'.subgroupOf H = E := Subgroup.comap_map_eq_self_of_injective H.subtype_injective E
  have hEq : ↥E ≃* ↥E' := Subgroup.equivMapOfInjective E H.subtype H.subtype_injective
  have hqE : CFSG.IsQuasisimple ↥E := ff_isQuasisimple_of_simple hs hnc
  have hqE' : CFSG.IsQuasisimple ↥E' := CFSG.LocalCores.isQuasisimple_of_mulEquiv hEq hqE
  have hnE' : (E'.subgroupOf H).Normal := by
    rw [hsub]
    exact hEn
  refine ⟨E', isComponentIn_of_normal hE'H hqE' hnE', ?_, ?_⟩
  · rw [InFStar]
    exact isFStarGroup_of_mulEquiv hEq hF
  · refine hB.trans ((Subgroup.closure_le _).mpr ?_)
    rintro c ⟨hcB, hodd⟩
    have hcH : c ∈ H := hBH hcB
    have hoddH : Odd (orderOf (⟨c, hcH⟩ : ↥H)) := by
      rw [← Subgroup.orderOf_coe]
      exact hodd
    have hdvd : orderOf (QuotientGroup.mk (s := E) (⟨c, hcH⟩ : ↥H)) ∣ orderOf (⟨c, hcH⟩ : ↥H) :=
      orderOf_map_dvd (QuotientGroup.mk' E) _
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp h2) (QuotientGroup.mk (s := E) (⟨c, hcH⟩ : ↥H))
    have hj0 : j = 0 := by
      by_contra hne
      have h2d : 2 ∣ orderOf (⟨c, hcH⟩ : ↥H) := (hj ▸ dvd_pow_self 2 hne).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hoddH) (even_iff_two_dvd.mpr h2d)
    have hmk : QuotientGroup.mk (s := E) (⟨c, hcH⟩ : ↥H) = 1 := by
      rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    exact Subgroup.mem_map.mpr ⟨⟨c, hcH⟩, (QuotientGroup.eq_one_iff _).mp hmk, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
