module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Alpha

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem indepTri_conj (hΩ : HypOmegaGen Ω) {K : Subgroup G} {z : G}
    (h : Hat2A7S8.IndepTri Ω K z) (g : G) :
    Hat2A7S8.IndepTri Ω (conjSub g K) (g * z * g⁻¹) := by
  obtain ⟨A, B', tA, tB, hA, hB', hB'A, htA, htB, hind⟩ := h
  refine ⟨conjSub g A, conjSub g B', g * tA * g⁻¹, g * tB * g⁻¹,
    omegaNbr_conj hΩ.conjInvariant hA g, omegaNbr_conj hΩ.conjInvariant hB' g,
    omegaNbr_conj hΩ.conjInvariant hB'A g, htA.conj g, htB.conj g, ?_⟩
  intro hmem
  rw [← T7A.conjSub_closure_pair] at hmem
  apply hind
  have h1 := mem_conjSub_iff.mp hmem
  have e : g⁻¹ * (g * tB * g⁻¹) * g = tB := by group
  rwa [e] at h1

variable [IsSimpleGroup G] {K₀ : Subgroup G}

theorem indepTri_all (hs : Pre2A7 Ω K₀) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (hI : Hat2A7S8.IndepTri Ω K z) :
    ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → Hat2A7S8.IndepTri Ω L u := by
  intro L hL u hu
  obtain ⟨g, hg⟩ := hs.trans L hL
  obtain ⟨h, hh⟩ := hs.trans K hK
  have hLK : L = conjSub (g * h⁻¹) K := by
    rw [conjSub_mul, ← hh, conjSub_inv_conjSub, hg]
  have hI' := indepTri_conj hs.hyp hI (g * h⁻¹)
  have hz' : IsUniqueInvolution L ((g * h⁻¹) * z * (g * h⁻¹)⁻¹) := by
    rw [hLK]
    exact hz.conj (g * h⁻¹)
  have hu' : u = (g * h⁻¹) * z * (g * h⁻¹)⁻¹ := hu.eq hz'
  rw [hLK, hu']
  exact hI'

theorem alphaConstAll_of_indepTri (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (hI : Hat2A7S8.IndepTri Ω K z) : Hat2A7S8.AlphaConstAll Ω := by
  intro K' hK' z' hz' J₁ hJ₁ J₂ hJ₂ t₁ t₂ ht₁ ht₂
  obtain ⟨A, B', tA, tB, hA, hB', hB'A, htA, htB, hind⟩ :=
    indepTri_all hs hK hz hI K' hK' z' hz'
  have hOz := Hat2A7S8.oddCoreOf_layerJoin_le_normalizer_alpha hs hnt hK' hA hB' hB'A hz' htA htB
    hind
  rw [Hat2A7S8.alphaOf_eq_of_layer hs hnt hK' hz' hA hJ₁ htA ht₁ hOz,
    Hat2A7S8.alphaOf_eq_of_layer hs hnt hK' hz' hA hJ₂ htA ht₂ hOz]

theorem alphaOf_eq_bot_of_indepTri (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hconn : DConnected Ω) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ Ω) {z₁ : G} (hz₁ : IsUniqueInvolution K₁ z₁)
    (hI : Hat2A7S8.IndepTri Ω K₁ z₁) :
    ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z → ∀ J ∈ omegaNbr Ω K, ∀ t : G,
      IsUniqueInvolution J t → alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hA := alphaConstAll_of_indepTri hs hnt hK₁ hz₁ hI
  obtain ⟨A, B', tA, tB, hAn, hB', hB'A, htA, htB, hind⟩ := hI
  have hN : sigmaNorm Ω K₁ ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z₁} : Set G)) : Set G) :=
    Hat2A7S8.sigmaNorm_le_normalizer_alpha hΩ hA hK₁ hz₁ hAn htA
  have htop : sigmaNorm Ω K₁ = ⊤ := by
    refine eq_top_iff.mpr fun n _ => ?_
    rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK₁]
    exact hconn K₁ hK₁ _ (hΩ.conjInvariant n K₁ hK₁)
  rw [htop, top_le_iff] at hN
  have hnorm : (alphaOf (Subgroup.closure ({tA, z₁} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hN
  have hodd := Hat2A7S8.odd_card_alphaOf_of_indep hs hnt hK₁ hAn hB' hB'A hz₁ htA htB hind
  have hα₀ : alphaOf (Subgroup.closure ({tA, z₁} : Set G)) = ⊥ := by
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hord : orderOf z₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz₁.sq) hz₁.ne_one
      have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z₁
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  intro K hK z hz J hJ t ht
  obtain ⟨-, hP⟩ :=
    Hat2A7S8.alphaOf_eq_of_mem_dComp hΩ hA hK₁ hz₁ hAn htA (hconn K₁ hK₁ K hK)
  rw [hP J hJ z t hz ht, hα₀]

theorem false_of_indepTri (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hedge : ¬ DEdgeless Ω) (hconn : DConnected Ω)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) {z₁ : G} (hz₁ : IsUniqueInvolution K₁ z₁)
    (hI : Hat2A7S8.IndepTri Ω K₁ z₁) : False :=
  false_of_oddCentral hs hedge hconn fun K hK z hz =>
    oddCentralAt_of_alphaOf_bot hz fun J hJ t ht _ =>
      alphaOf_eq_bot_of_indepTri hs hnt hconn hK₁ hz₁ hI K hK z hz J hJ t ht

theorem indepTri_of_two_common_nbrs (hΩ : HypOmegaGen Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K J K₁ K₂ : Subgroup G} {z t : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t)
    (h1K : K₁ ∈ omegaNbr Ω K) (h1J : K₁ ∈ omegaNbr Ω J) (h2K : K₂ ∈ omegaNbr Ω K)
    (h2J : K₂ ∈ omegaNbr Ω J) (h12 : K₁ ≠ K₂) : Hat2A7S8.IndepTri Ω K z := by
  obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΩ h1K.1
  obtain ⟨z₂, hz₂⟩ := Sec6Gen.exists_uniqueInvolution hΩ h2K.1
  by_cases h1 : z₁ ∈ Subgroup.closure ({z, t} : Set G)
  · by_cases h2 : z₂ ∈ Subgroup.closure ({z, t} : Set G)
    · exfalso
      have e1 := Hat2A7S8.eq_mul_of_mem_closure_pair hΩ hnt hK hz hJ ht h1K h1J hz₁ h1
      have e2 := Hat2A7S8.eq_mul_of_mem_closure_pair hΩ hnt hK hz hJ ht h2K h2J hz₂ h2
      have hz₂' : IsUniqueInvolution K₂ z₁ := by
        rw [e1, ← e2]
        exact hz₂
      exact h12 (hnt K₂ h2K.1 K₁ ⟨h1K.1, z₁, hz₂', hz₁⟩)
    · exact ⟨J, K₂, t, z₂, hJ, h2K, h2J, ht, hz₂, h2⟩
  · exact ⟨J, K₁, t, z₁, hJ, h1K, h1J, ht, hz₁, h1⟩

end Alpha

end CFSG.ClassicalInvolution.Hat2A7S
