module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SStd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S6Aux
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Aux

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Main


variable {G : Type} [Group G] [Finite G]

theorem mem_omegaNbr_of_normalizes_a7 {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hJK : J ≠ K) {z u : G} (hz : IsUniqueInvolution K z)
    (hu : IsUniqueInvolution J u) (hzN : z ∈ Subgroup.normalizer (J : Set G)) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨mJ, hmJ⟩ := hcl J hJ
  obtain ⟨mK, hmK⟩ := hcl K hK
  obtain ⟨P, hPJ, hP2, hP8, hPc⟩ :=
    Hat2A7.exists_two_subgroup_centralizing hmJ.witness hzN hz.sq
  have hPz : P ≤ Subgroup.centralizer ({z} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hPc r hr).symm
  have hPN : P ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ hJK.symm hz hPJ hP2 (by omega) hPz
  obtain ⟨huP, huniq⟩ := involution_mem_of_isPGroup hu hPJ hP2 (by omega)
  obtain ⟨R, hR, hRc⟩ :=
    exists_sylow_centralized hmK hPN hP2 huP huniq (by omega) hu.sq hu.ne_one
  exact mem_omegaNbr_of_sylow_centralizes hΩ hK hJ hJK hu hR hRc

theorem normalizes_of_mem_omegaNbr_a7 {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (h : J ∈ omegaNbr Ω K) {z u : G} (hz : IsUniqueInvolution K z)
    (hu : IsUniqueInvolution J u) : z ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨-, hJK, R, hR, hRJ, hRN⟩ := h
  obtain ⟨mK, hmK⟩ := hcl K hK
  have hRs : IsSylow2In R J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ hR hRJ
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  obtain ⟨huR, huniq⟩ := involution_mem_of_isPGroup hu hRJ hRs.2.1 (by omega)
  obtain ⟨R', hR', hR'c⟩ :=
    exists_sylow_centralized hmK hRN hRs.2.1 huR huniq (by omega) hu.sq hu.ne_one
  exact le_normalizer_of_sylow_centralizes hΩ hK hJ hJK hu hR' hR'c
    (Sec6Gen.mem_of_isSylow2In hz hR')

theorem mem_omegaNbr_iff_normalizes_a7 {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hJK : J ≠ K) {z u : G} (hz : IsUniqueInvolution K z)
    (hu : IsUniqueInvolution J u) :
    J ∈ omegaNbr Ω K ↔ z ∈ Subgroup.normalizer (J : Set G) :=
  ⟨fun h => normalizes_of_mem_omegaNbr_a7 hΩ hcl hK hJ h hz hu,
    mem_omegaNbr_of_normalizes_a7 hΩ hcl hK hJ hJK hz hu⟩

theorem a7T6_proved : A7T6 := by
  intro G _ _ _ Ω K hstd hedge
  have hpre : Pre2A7 Ω K := hstd.toPre2A7
  have hΩ : HypOmegaGen Ω := hpre.hyp
  have hK : K ∈ Ω := hpre.mem
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨g, hne, hcomm⟩ := exists_commuting_conj_ne_a7 hpre.nonabelian hz.ne_one hz.sq
  have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hu : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hz.conj g
  have hJK : conjSub g K ≠ K := fun h => hne (hz.conj_eq h)
  have hzN : z ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    by_contra hnot
    have hzu : z * (g * z * g⁻¹) * z⁻¹ = g * z * g⁻¹ := by
      calc z * (g * z * g⁻¹) * z⁻¹ = (g * z * g⁻¹) * z * z⁻¹ := by rw [← hcomm]
        _ = g * z * g⁻¹ := by group
    have hu' := hu.conj z
    rw [hzu] at hu'
    have hJ' : conjSub z (conjSub g K) ∈ Ω := hΩ.conjInvariant z _ hJ
    exact hedge _ hJ _ hJ'
      (Or.inl (Q3.Q3CL.T3.twin_mem_omegaNbr hΩ hJ hJ' hnot hu hu'))
  have h := mem_omegaNbr_of_normalizes_a7 hΩ hpre.classical hK hJ hJK hz hu hzN
  exact hedge K hK _ hJ (Or.inl h)

end Main

end CFSG.ClassicalInvolution.Hat2A7S
