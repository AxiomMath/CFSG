module

import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {P : Type} [Group P] [Finite P] {H : Subgroup P} {t : CFSG.Open.StatedLieTag} {n k : ℕ}

theorem fg_component_layer
    (hsh : ∀ (E : Type) [Group E], LieModel E t n 3 k →
      IsSimpleGroup E ∧ ∃ a b : E, a * b ≠ b * a)
    (hLM : LayerModel ↥H t n k) {J : Subgroup P} (hJ : IsComponentIn J H) :
    ∃ (E : Subgroup ↥H) (_ : E.Normal), LieModel ↥E t n 3 k ∧ IsPGroup 2 (↥H ⧸ E) ∧
      J = E.map H.subtype := by
  obtain ⟨E, hEn, hLie, h2⟩ := hLM
  obtain ⟨hs, hnc⟩ := hsh ↥E hLie
  haveI := hEn
  let E' : Subgroup P := E.map H.subtype
  have hE'H : E' ≤ H := Subgroup.map_subtype_le E
  have hsub : E'.subgroupOf H = E := Subgroup.comap_map_eq_self_of_injective H.subtype_injective E
  have hEq : ↥E ≃* ↥E' := Subgroup.equivMapOfInjective E H.subtype H.subtype_injective
  have hqE : CFSG.IsQuasisimple ↥E := ff_isQuasisimple_of_simple hs hnc
  have hqE' : CFSG.IsQuasisimple ↥E' := CFSG.LocalCores.isQuasisimple_of_mulEquiv hEq hqE
  have hnE' : (E'.subgroupOf H).Normal := by
    rw [hsub]
    exact hEn
  have hcE' : IsComponentIn E' H := isComponentIn_of_normal hE'H hqE' hnE'
  have hJE : J ≤ E' := by
    have hperf : Group.IsPerfect ↥(J.subgroupOf H) := hJ.2.1.1
    have hle : J.subgroupOf H ≤ E := ff_perfect_le_of_quot_two E h2 (J.subgroupOf H) hperf
    intro j hj
    have hjH : j ∈ H := hJ.1 hj
    have hmem : (⟨j, hjH⟩ : ↥H) ∈ J.subgroupOf H := hj
    exact ⟨⟨j, hjH⟩, hle hmem, rfl⟩
  exact ⟨E, hEn, hLie, h2, IsComponentIn.eq_of_le hJ hcE' hJE⟩

theorem fg_lieModel_of_layerModel
    (hsh : ∀ (E : Type) [Group E], LieModel E t n 3 k →
      IsSimpleGroup E ∧ ∃ a b : E, a * b ≠ b * a)
    (hLM : LayerModel ↥H t n k) {J : Subgroup P} (hJ : IsComponentIn J H) :
    LieModel ↥J t n 3 k := by
  obtain ⟨E, hEn, hLie, -, hJeq⟩ := fg_component_layer hsh hLM hJ
  exact LieModel.of_mulEquiv
    ((Subgroup.equivMapOfInjective E H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hJeq.symm)) hLie

theorem fg_mem_component_of_perfect
    (hsh : ∀ (E : Type) [Group E], LieModel E t n 3 k →
      IsSimpleGroup E ∧ ∃ a b : E, a * b ≠ b * a)
    (hLM : LayerModel ↥H t n k) {J : Subgroup P} (hJ : IsComponentIn J H) {Γ : Type} [Group Γ]
    (hperf : Group.IsPerfect Γ) (ψ : Γ →* ↥H) (g : Γ) : ((ψ g : ↥H) : P) ∈ J := by
  obtain ⟨E, hEn, -, h2, hJeq⟩ := fg_component_layer hsh hLM hJ
  haveI := hEn
  haveI := hperf
  have hperfR : Group.IsPerfect ↥ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hle : ψ.range ≤ E := ff_perfect_le_of_quot_two E h2 ψ.range hperfR
  rw [hJeq]
  exact ⟨ψ g, hle ⟨g, rfl⟩, rfl⟩

theorem fg_mem_component_of_pow_three
    (hsh : ∀ (E : Type) [Group E], LieModel E t n 3 k →
      IsSimpleGroup E ∧ ∃ a b : E, a * b ≠ b * a)
    (hLM : LayerModel ↥H t n k) {J : Subgroup P} (hJ : IsComponentIn J H) (g : ↥H)
    (hg : g ^ 3 = 1) : (g : P) ∈ J := by
  obtain ⟨E, hEn, -, h2, hJeq⟩ := fg_component_layer hsh hLM hJ
  haveI := hEn
  have hmem : g ∈ E := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp h2) (QuotientGroup.mk g : ↥H ⧸ E)
    have h3 : (QuotientGroup.mk g : ↥H ⧸ E) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
    have hdvd : 2 ^ m ∣ 3 := by
      rw [← hm]
      exact orderOf_dvd_of_pow_eq_one h3
    have hm0 : m = 0 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact h
      · exfalso
        have h2dvd : 2 ∣ 3 := (dvd_pow_self 2 h.ne').trans hdvd
        exact absurd h2dvd (by decide)
    have hone : (QuotientGroup.mk g : ↥H ⧸ E) = 1 := by
      rw [← orderOf_eq_one_iff, hm, hm0, pow_zero]
    exact (QuotientGroup.eq_one_iff g).mp hone
  rw [hJeq]
  exact ⟨g, hmem, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
