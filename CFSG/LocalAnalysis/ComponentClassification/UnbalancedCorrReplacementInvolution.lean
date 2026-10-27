module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrRankGap
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSwapReplacement

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G] [Finite G]

theorem noncentral_unbalancing_replacement_involution {a : G} (ha : orderOf a = 2)
    {J : Subgroup G} (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hmax : ∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K → GSReach J K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index ∧
        ((pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
          pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K) ≤
            pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J)))
    {b y : G} {L : Subgroup G} (hC : UnbalancedGS.GSCorr a J b L)
    (hUL : GSUnbalancingTriple b y L) (hnotiso : ¬ UnbalancedGS.GSIsoCorr a J b L)
    {S P Q T : Subgroup G} (hSH : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hbS : b ∈ S)
    (hP : P = S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J))
    (hQ : Q = S ⊓ centralizer ({b} : Set G)) (hT : T = P ⊓ centralizer ({b} : Set G))
    (hJ2 : 2 ≤ pRank 2 ↥J) (hyS : y ∈ S) :
    (P.subgroupOf S).Normal ∧ T = P ⊓ Q ∧ T < P ∧ pRank 2 ↥T < pRank 2 ↥P ∧
    pRank 2 ↥P =
      pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) ∧
    ¬ P ≤ Q ∧ 8 ≤ Nat.card T ∧
    ∃ R : Subgroup G,
      (R : Set G) = {u | u ∈ T ∧ ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * u⁻¹ * k * u ∈
        (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype} ∧
      R ≤ Q ∧ (R.subgroupOf Q).Normal ∧
      zpowers a ⊓ R = ⊥ ∧ zpowers a ⊔ R = T ∧ (∀ x ∈ zpowers a, ∀ z ∈ R, x * z = z * x) ∧
      ∃ w ∈ P, w ∈ normalizer (Q : Set G) ∧ w ∉ Q ∧ w ^ 2 ∈ T ∧
        ∃ e : G, orderOf e = 2 ∧ e ∈ R ⊓ conjugate R w ∧
          Q ⊔ zpowers w ≤ S ⊓ centralizer ({e} : Set G) ∧
          Q < S ⊓ centralizer ({e} : Set G) ∧ e ∈ P ∧ e ∈ normalizer (J : Set G) ∧
          (∀ j ∈ J, j⁻¹ * e⁻¹ * j * e ∈ (pPrimeCore 2 J).map J.subtype) ∧
          (∀ k ∈ L ⊔ conjugate L a, k⁻¹ * e⁻¹ * k * e ∈
            (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype) ∧
          e * a = a * e ∧ e * b = b * e ∧ e * y = y * e := by
  obtain ⟨hne, hdeq, -, -, -, -, -, hPQJ, hbig⟩ :=
    nonisomorphic_unbalancing_correspondence_rank_gap ha hJa hJ hmax hC hUL hnotiso hSH hSsyl
      hbS hP hQ hT
  obtain ⟨hlt, hTP, hPQ, hT8⟩ := hbig hJ2
  obtain ⟨hPS, hTPQ, R, hR, hRQ, hRn, hbot, hsup, hcomm, w, hwP, hwN, hwQ, hw2, e, he, heR, hQw,
    hQlt, heP, heN, heJ, heK, hea, heb, heQ⟩ :=
    swapped_correspondence_large_kernel_centralizer_replacement hC hne hdeq.symm hSH hSsyl hbS
      hP hQ hT hTP hT8
  have hyQ : y ∈ Q := by
    rw [hQ]
    exact mem_inf.mpr ⟨hyS, mem_centralizer_singleton_iff.mpr hUL.2.2.1.symm⟩
  exact ⟨hPS, hTPQ, hTP, hlt, hPQJ, hPQ, hT8, R, hR, hRQ, hRn, hbot, hsup, hcomm, w, hwP, hwN,
    hwQ, hw2, e, he, heR, hQw, hQlt, heP, heN, heJ, heK, hea, heb, heQ y hyQ⟩

end CFSG.ComponentClassification.UnbalancedCorr
