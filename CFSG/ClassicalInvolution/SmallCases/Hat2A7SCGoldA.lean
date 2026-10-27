module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCAlpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Classes


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem oddCore_layerJoin_le_normalizer (hΩ : HypOmegaGen Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    oddCoreOf (T8.layerJoin Ω z) ≤ Subgroup.normalizer (K : Set G) := by
  intro n hn
  have h1 : n ∈ T8.layerJoin Ω z := oddCoreOf_le_self _ hn
  have h2 : n ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ z h1
  exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK (hnt K hK) hz h2

theorem eq_one_of_odd_of_isPGroup {Q H : Subgroup G} (hQ : Odd (Nat.card Q)) (hH : IsPGroup 2 H)
    {x : G} (hxQ : x ∈ Q) (hxH : x ∈ H) : x = 1 :=
  Asc77.eq_one_of_isPGroup_of_mem_odd hQ hxQ (hH.to_le (Subgroup.zpowers_le.mpr hxH))

theorem exists_common_nbr_of_layerImg_ne (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {J N : Subgroup G} (hJ : J ∈ omegaNbr Ω K)
    (hN : N ∈ omegaNbr Ω K) (hne : T8.layerImg Ω z J ≠ T8.layerImg Ω z N) :
    ∃ M, M ∈ omegaNbr Ω K ∧ M ∈ omegaNbr Ω J ∧ T8.layerImg Ω z M = T8.layerImg Ω z N := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := Hat2A7S8.witness_of_pre hs
  have hLH : Hat2A7S8.Asc77.T8.LayerHyp Ω z := Hat2A7S8.layerHyp_of_pre hs hz.sq hz.ne_one
  have hJx : T8.XMem Ω z J := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hK hz hJ
  have hNx : T8.XMem Ω z N := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hK hz hN
  have hF := Hat2A7S8.Asc77.T8.LayerFam.layerSet hΩ hNx
  rcases hF.images_eq_or_commute hLH ⟨N, hNx, rfl⟩ ⟨J, hJx, rfl⟩ with h | hcomm
  · exact absurd h.symm hne
  · obtain ⟨n, hn, hnb⟩ := Hat2A7S8.Asc77.T8.exists_oddCore_conj_omegaNbr_of_commute hLH hNx hJx
      (Ne.symm hne) hcomm
    have hnN : n ∈ Subgroup.normalizer (K : Set G) :=
      oddCore_layerJoin_le_normalizer hΩ hnt hK hz hn
    have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hnN
    refine ⟨conjSub n N, ?_, ?_, ?_⟩
    · exact Hat2A7S8.conjSub_mem_omegaNbr_of_normalizes hΩ hnK hN
    · exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (hΩ.conjInvariant n N hN.1) hJ.1 hnb
    · exact T8.layerImg_conj_of_mem_oddCore hn

theorem layerImg_cases (hs : Pre2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hnoI : ¬ Hat2A7S8.IndepTri Ω K z) {J₁ J₂ N : Subgroup G} (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (hN : N ∈ omegaNbr Ω K)
    (hne : T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂) :
    T8.layerImg Ω z N = T8.layerImg Ω z J₁ ∨ T8.layerImg Ω z N = T8.layerImg Ω z J₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨M₂, hM₂K, hM₂J, hM₂⟩ := exists_common_nbr_of_layerImg_ne hs hnt hK hz hJ₁ hJ₂ hne
  obtain ⟨M₃, hM₃K, hM₃J, hM₃⟩ := exists_common_nbr_of_layerImg_ne hs hnt hK hz hJ₁ hN
    (Ne.symm h1)
  have hM23 : M₂ ≠ M₃ := fun h => h2 (by rw [← hM₃, ← h, hM₂])
  obtain ⟨t₁, ht₁⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ₁.1
  exact hnoI (indepTri_of_two_common_nbrs hΩ hnt hK hz hJ₁ ht₁ hM₂K hM₂J hM₃K hM₃J hM23)

theorem involution_eq_mul_of_common_nbr (hΩ : HypOmegaGen Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K J M : Subgroup G} {z tJ tM : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hnoI : ¬ Hat2A7S8.IndepTri Ω K z)
    (hJ : J ∈ omegaNbr Ω K) (htJ : IsUniqueInvolution J tJ) (hMK : M ∈ omegaNbr Ω K)
    (hMJ : M ∈ omegaNbr Ω J) (htM : IsUniqueInvolution M tM) : tM = z * tJ := by
  by_cases hmem : tM ∈ Subgroup.closure ({z, tJ} : Set G)
  · exact Hat2A7S8.eq_mul_of_mem_closure_pair hΩ hnt hK hz hJ htJ hMK hMJ htM hmem
  · exact absurd (⟨J, M, tJ, tM, hJ, hMK, hMJ, htJ, htM, hmem⟩ : Hat2A7S8.IndepTri Ω K z) hnoI

theorem involution_eq_of_layerImg_eq (hs : Pre2A7 Ω K₀) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {H : Subgroup G} (hH : IsPGroup 2 H) {J N : Subgroup G}
    (hJ : J ∈ omegaNbr Ω K) (hN : N ∈ omegaNbr Ω K)
    (heq : T8.layerImg Ω z J = T8.layerImg Ω z N) {tJ tN : G} (htJ : IsUniqueInvolution J tJ)
    (htN : IsUniqueInvolution N tN) (hJH : tJ ∈ H) (hNH : tN ∈ H) : tJ = tN := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := Hat2A7S8.witness_of_pre hs
  have hLH : Hat2A7S8.Asc77.T8.LayerHyp Ω z := Hat2A7S8.layerHyp_of_pre hs hz.sq hz.ne_one
  have hJx : T8.XMem Ω z J := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hK hz hJ
  have hNx : T8.XMem Ω z N := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hK hz hN
  obtain ⟨n, hn, hnJ⟩ := Hat2A7S8.Asc77.T8.exists_oddCore_conj_of_layerImg_eq hLH hJx hNx heq
  have htN' : IsUniqueInvolution N (n * tJ * n⁻¹) := by
    rw [← hnJ]
    exact htJ.conj n
  have htNeq : tN = n * tJ * n⁻¹ := htN.eq htN'
  have htJz : tJ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : z * tJ * z⁻¹ = tJ :=
      htJ.conj_eq (mem_normalizer_iff_conjSub_eq.mp
        (Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hK hz hJ).2.1)
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have htJN : tJ ∈ Subgroup.normalizer (oddCoreOf (T8.layerJoin Ω z) : Set G) :=
    Hat2A7S8.Asc77.T8.mem_normalizer_oddCoreOf_layerJoin hΩ
      (by rw [T8.cenZ_eq_centralizer]; exact htJz)
  have hq : tJ⁻¹ * tN ∈ oddCoreOf (T8.layerJoin Ω z) := by
    have h1 : tJ⁻¹ * n * tJ ∈ oddCoreOf (T8.layerJoin Ω z) := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (oddCoreOf (T8.layerJoin Ω z) : Set G)).inv_mem htJN) n).mp hn
      simpa using this
    have e : tJ⁻¹ * tN = (tJ⁻¹ * n * tJ) * n⁻¹ := by
      have hti : tJ⁻¹ = tJ := inv_eq_of_mul_eq_one_right htJ.sq
      rw [htNeq, hti]
      group
    rw [e]
    exact (oddCoreOf (T8.layerJoin Ω z)).mul_mem h1 ((oddCoreOf (T8.layerJoin Ω z)).inv_mem hn)
  have hqH : tJ⁻¹ * tN ∈ H := H.mul_mem (H.inv_mem hJH) hNH
  have h1 : tJ⁻¹ * tN = 1 :=
    eq_one_of_odd_of_isPGroup (odd_natCard_oddCoreOf _) hH hq hqH
  have h2 : tJ = tN := inv_mul_eq_one.mp h1
  exact h2

end Classes

end CFSG.ClassicalInvolution.Hat2A7S
