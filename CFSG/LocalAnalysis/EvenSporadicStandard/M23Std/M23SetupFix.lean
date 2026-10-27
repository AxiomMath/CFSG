module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23FixFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.MainHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23FixedData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KEngine2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23A7
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.BadKExclude
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Setup

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.QuasithinUnique.Unc25G2.M2x CFSG.EvenSporadicStandard.Wong77.M23Sylow

theorem m23_localData3Fix
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .M23)
    {z : G} (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2) :
    ∃ (t m : G) (T1 F1 F2 : Subgroup G), t ∈ L ∧ OneClassData L z t ∧
      FusionData L t T1 F1 F2 m ∧ NData L F1 ∧ FixedData L F1 ∧ Trans2Data L F1 ∧
      GoodK z F1 ∧ NormQuotA7 (normalizer (F1 : Set G) ⊓ L) F1 ∧ FixFour L F1 := by
  have := h.simple
  obtain ⟨e⟩ := hL
  let φ : Carrier .M23 →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hrange : φ.range = L := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [φ]⟩
  have hS := (Certificates.certificate24160).1
  have hP : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have h2E : TwoEAt sylowS := twoE_M23.exists_at hP sylowS_index_odd
  obtain ⟨F1, F2, hD, hN, hmem1⟩ := m23_fusionData_pinned h2E
  have hD' := hrange ▸ FusionData.map hφ hD
  have hN' := hrange ▸ NData.map hφ hN
  have hX' := hrange ▸ FixedData.map hφ (fixedData_pinned hmem1)
  have hT' := hrange ▸ Trans2Data.map hφ (trans2Data_pinned hmem1)
  have hLift' := hrange ▸ LiftData.map hφ (liftData_pinned hmem1)
  have hFix' : FixFour L (F1.map φ) := hrange ▸ FixFour.map hφ (fixFour_pinned hmem1)
  have htL : φ tEl ∈ L := hrange ▸ ⟨tEl, rfl⟩
  have ht2 : orderOf (φ tEl) = 2 := by
    obtain ⟨hsq, h1⟩ := tEl_involution
    rw [orderOf_injective φ hφ]
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
  have hOne := m23_oneClassData h ⟨e⟩ hz hz2 htL ht2
  have hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z) := fun u hu hu2 hu1 =>
    fused_all h.nonabelian hOne hu hu2 hu1
  have htr := exists_normalizer_conj_eq_mul h.nonabelian hOne hD' hN'.trans
  have hA7 : NormQuotA7 (normalizer ((F1.map φ : Subgroup G) : Set G) ⊓ L) (F1.map φ) := by
    rw [← hrange, normalizer_map_inf_range hφ]
    exact NormQuotA7.map hφ (normQuotA7_pinned hmem1 hN)
  refine ⟨φ tEl, φ mEl, sylowS.map φ, F1.map φ, F2.map φ, htL, hOne, hD', hN', hX', hT', ?_, hA7,
    hFix'⟩
  rcases goodK_or_badK hOne hN' hT' with hgood | hbad
  · exact hgood
  · exact (badK_false hOne hZ hN' hX' htr hbad hLift').elim

theorem m23_setupFix
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .M23)
    {z : G} (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2) :
    ∃ (t : G) (F L1 N : Subgroup G), t ∈ L ∧ Setup L z t F L1 N ∧ (∀ x ∈ L1, ¬ IsConj z x) ∧
      (∀ k ∈ Ksub z F, IsConj z k → ∃ f ∈ F, k = z * f) ∧
      NormQuotA7 (normalizer (F : Set G) ⊓ L) F ∧ FixFour L F := by
  have := h.simple
  obtain ⟨t, m, T1, F1, F2, htL, hOne, hD, hN, hX, hT, hgood, hA7, hFix⟩ :=
    m23_localData3Fix h hL hz hz2
  have hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z) := fun u hu hu2 hu1 =>
    fused_all h.nonabelian hOne hu hu2 hu1
  have htr := exists_normalizer_conj_eq_mul h.nonabelian hOne hD hN.trans
  have hR := m23_rankFour hL
  obtain ⟨L1, -, hFL1, hcard, hsq, hcomm, -, hK, -, hcz, hnormE, hnc, -, -, -, hBu, hnormK,
      hconj⟩ :=
    K_goodK_of_data h.nonabelian hOne hD hN hX hR hgood
  obtain ⟨N, hNle, hNnorm, hNodd, hNdisj, hNsup⟩ := hBu
  have hsurj := phiHom_surjective hOne hZ hN htr
  refine ⟨t, F1, L1, N, htL, ⟨hOne, hN, hZ, hFL1, hcard, hsq, hcomm, hK, hcz, hnormE, hnormK,
    hNle, hNnorm, hNodd, hNdisj, hNsup, fun f hf => ?_⟩, hnc, hconj, hA7, hFix⟩
  obtain ⟨κ, hκ⟩ := hsurj ⟨f, hf⟩
  exact ⟨κ, κ.2, congrArg Subtype.val hκ⟩

end CFSG.EvenSporadicStandard.M23Std
