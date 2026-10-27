module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWCent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWNon
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46Z
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Walter.J1

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]


theorem exists_central_involution_of_outcome {a x : G} {J S W : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G))
    {K : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hout : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) ∨
      (conjugate K a ≠ K ∧ J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G))))
    {T : Subgroup G} (hT : IsSylowTwoIn T (normalizer (W : Set G))) (hST : S ≤ T) :
    ∃ b ∈ T ⊓ normalizer (K : Set G), orderOf b = 2 ∧
      (∀ s ∈ T ⊓ normalizer (K : Set G), s * b = b * s) ∧ b ∈ coreActionKernel K := by
  obtain ⟨-, hU3, -, -, hSyl, haS, -⟩ := id hset
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  set M : Subgroup G := normalizer (W : Set G) with hM
  set S' : Subgroup G := T ⊓ normalizer (K : Set G) with hS'
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hT
  have haM : a ∈ M := hNJ (hSyl.1 haS)
  have haT : a ∈ T := hST haS
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha2
  set Q' : Subgroup G := S' ⊓ coreActionKernel K with hQ'
  have hQ'ne : Q' ≠ ⊥ := by
    rcases hout with hsup | ⟨hne, -⟩
    · have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
      have haK := mem_coreActionKernel_of_sup_eq hKM hKc (le_normalizer.trans hNJ) hJper
        (GrS4.not_odd_card_of_isPComponent hJa hJc) hsup haM hJa
      intro hbot
      have : a ∈ Q' := mem_inf.mpr ⟨mem_inf.mpr ⟨haT, (mem_coreActionKernel.mp haK).1⟩, haK⟩
      rw [hbot, mem_bot] at this
      exact ha1 this
    · have hTK := isSylowTwoIn_inf_of_isPComponent hT hKM hKc
      have h64 := GrS4.sixtyFour_le_card hKL hTK
      obtain ⟨p, hp, hp1⟩ : ∃ p ∈ T ⊓ K, p ≠ 1 := by
        by_contra hall
        push Not at hall
        have : T ⊓ K = ⊥ := eq_bot_iff.mpr fun y hy => mem_bot.mpr (hall y hy)
        rw [this, card_bot] at h64
        omega
      have hq : a⁻¹ * p * a ∈ conjugate K a := by
        rw [UnbalancedLayer.mem_conjugate_iff, show a * (a⁻¹ * p * a) * a⁻¹ = p by group]
        exact (mem_inf.mp hp).2
      have hqC := conjugate_le_coreActionKernel hKM hKc haM hne hq
      have hqT : a⁻¹ * p * a ∈ T := mul_mem (mul_mem (inv_mem haT) (mem_inf.mp hp).1) haT
      intro hbot
      have : a⁻¹ * p * a ∈ Q' :=
        mem_inf.mpr ⟨mem_inf.mpr ⟨hqT, (mem_coreActionKernel.mp hqC).1⟩, hqC⟩
      rw [hbot, mem_bot] at this
      apply hp1
      have h1 : p = a * (a⁻¹ * p * a) * a⁻¹ := by group
      rw [h1, this, mul_one, mul_inv_cancel]
  have hS'2 : IsPGroup 2 S' := hT2.to_le inf_le_left
  have hS'Q : S' ≤ normalizer (Q' : Set G) := fun s hs =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hs,
      UnbalancedLayer.normalizer_le_normalizer_coreActionKernel K (mem_inf.mp hs).2⟩
  obtain ⟨b, hbQ, hbb, hb1, hbc⟩ :=
    exists_involution_inf_centralizer hS'2 inf_le_left le_rfl hS'Q hQ'ne
  exact ⟨b, (mem_inf.mp hbQ).1, orderOf_eq_prime (by rw [pow_two]; exact hbb) hb1,
    fun s hs => (hbc s hs).symm, (mem_inf.mp hbQ).2⟩

theorem wGroup_eq_of_inf_zStarIn_eq_bot {a x : G} {J S W : Subgroup G}
    (hset : L34Sec4Setting G a x J S)
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hout : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) ∨
      (conjugate K a ≠ K ∧ J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G))))
    {T : Subgroup G} (hT : IsSylowTwoIn T (normalizer (W : Set G))) (hST : S ≤ T)
    (hTK : ∀ e ∈ T, ∀ e' ∈ T, conjugate K e = K ∨ conjugate K e' = K ∨
      conjugate K e = conjugate K e')
    (hZK : T ⊓ zStarIn K = ⊥) {F : Subgroup G} (hFT : F ≤ T) (hF : IsEightGroup F)
    (hns : ∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) : wGroup F = W := by
  have hGW : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hset.1.2.2.2.2.2.1
  obtain ⟨-, hU3, hL34, -, hSyl, haS, -⟩ := id hset
  obtain ⟨-, -, -, hJa, hJc, -, -⟩ := hU3
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  set M : Subgroup G := normalizer (W : Set G) with hM
  set S' : Subgroup G := T ⊓ normalizer (K : Set G) with hS'
  have haM : a ∈ M := hNJ (hSyl.1 haS)
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hT
  have hS'2 : IsPGroup 2 S' := hT2.to_le inf_le_left
  have hS'N : S' ≤ normalizer (K : Set G) := inf_le_right
  have hKper : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hKM hKc
  have hTKs := isSylowTwoIn_inf_of_isPComponent hT hKM hKc
  have hS'K : IsSylowTwoIn (S' ⊓ K) K := by
    rwa [hS', inf_assoc, inf_of_le_right (le_normalizer : K ≤ normalizer (K : Set G))]
  have hZ' : S' ⊓ zStarIn K = ⊥ :=
    eq_bot_iff.mpr fun z hz => hZK ▸ mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hz).1).1,
      (mem_inf.mp hz).2⟩
  obtain ⟨b, hbS', hb2, hbc, hbK⟩ :=
    exists_central_involution_of_outcome hset hNJ hKM hKc hKL hout hT hST
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hb1 : b ≠ 1 := by rintro rfl; simp at hb2
  obtain ⟨DJ⟩ := exists_wStd hJper hL34 (GrS4.isSylowTwoIn_inf hSyl) hSyl.1
  obtain ⟨D, -, hDSJ, -, hD, -, -⟩ := DJ.exists_two_eights (GrS4.isPGroup_of_isSylowTwoIn hSyl)
  have hWD : wGroup D = W :=
    hWB D (hDSJ.trans (inf_le_inf_left _ le_sup_left)) (hD.1.isAbelianTwoOfRank hD.2.ge)
  have hJW : J ≤ withKernel K := by
    rcases hout with hsup | ⟨hne, hJle⟩
    · exact (GrS4.le_of_sup_oddIn_eq (le_normalizer.trans hNJ) hKM hKc hJper hsup).trans
        le_sup_left
    · exact le_withKernel_of_le_sup hKM hKc haM hne hJle
  have hDS' : D ≤ S' ⊓ withKernel K := fun d hd => by
    have hdS := (mem_inf.mp (hDSJ hd)).1
    have hdJ := (mem_inf.mp (hDSJ hd)).2
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hST hdS, GrS4.withKernel_le_normalizer K (hJW hdJ)⟩, hJW hdJ⟩
  obtain ⟨DK⟩ := exists_wStd hKper hKL hS'K hS'N
  obtain ⟨A, -, hA, hAc⟩ := exists_central_eight DK hKper hS'2 hZ' hbS' hbb hb1 hbc hbK
  have hWB' : ∀ B : Subgroup G, B ≤ S' ⊓ withKernel K → IsAbelianTwoOfRank 3 B →
      wGroup B = W := fun B hBS hB =>
    wGroup_eq_of_central_eight hGW hA hAc hDS' hD hWD hBS hB
  obtain ⟨t, htT, htt, htF, htn⟩ := hns
  by_cases hEN : F ≤ normalizer (K : Set G) ∧ t ∈ normalizer (K : Set G)
  · exact wGroup_eq_of_not_stronglyIsolated_gen hGW hKper hKL hS'K hS'2 hS'N hbS' hb2 hbc hbK
      hWB' (le_inf hFT hEN.1) hF ⟨t, mem_inf.mpr ⟨htT, hEN.2⟩, htt, htF, htn⟩
  obtain ⟨hE, hEc⟩ := GrS4.isElemTwo_sup_zpowers hF.1 htt htn fun e he => (htF e he).symm
  set E : Subgroup G := F ⊔ zpowers t with hEdef
  have hE16 : Nat.card E = 16 := by rw [hEc, hF.2]
  have hET : E ≤ T := sup_le hFT (zpowers_le.mpr htT)
  obtain ⟨f, hfE, hfN⟩ : ∃ f ∈ E, f ∉ normalizer (K : Set G) := by
    by_contra hall
    push Not at hall
    exact hEN ⟨fun e he => hall e (mem_sup_left he), hall t (mem_sup_right (mem_zpowers t))⟩
  have hfK : conjugate K f ≠ K := fun h =>
    hfN (UnbalancedLayer.mem_normalizer_of_conjugate_eq h)
  set E₀ : Subgroup G := E ⊓ normalizer (K : Set G) with hE₀
  have hE₀e : IsElemTwo E₀ := hE.mono inf_le_left
  have hfE₀ : f ∉ E₀ := fun h => hfN (mem_inf.mp h).2
  obtain ⟨hE₀f, hE₀fc⟩ := GrS4.isElemTwo_sup_zpowers hE₀e (hE.2 f hfE) hfE₀
    fun e he => hE.1 e (mem_inf.mp he).1 f hfE
  have hEle : E ≤ E₀ ⊔ zpowers f := by
    intro e he
    by_cases heN : e ∈ normalizer (K : Set G)
    · exact mem_sup_left (mem_inf.mpr ⟨he, heN⟩)
    have heK : conjugate K e ≠ K := fun h =>
      heN (UnbalancedLayer.mem_normalizer_of_conjugate_eq h)
    rcases hTK e (hET he) f (hET hfE) with h | h | h
    · exact absurd h heK
    · exact absurd h hfK
    · have hef : e * f⁻¹ ∈ normalizer (K : Set G) := by
        rw [mem_normalizer_iff]
        intro y
        have h1 : f⁻¹ * y * f ∈ conjugate K f ↔ y ∈ K := by
          rw [UnbalancedLayer.mem_conjugate_iff, show f * (f⁻¹ * y * f) * f⁻¹ = y by group]
        rw [← h1, ← h, UnbalancedLayer.mem_conjugate_iff,
          show e * (f⁻¹ * y * f) * e⁻¹ = e * f⁻¹ * y * (e * f⁻¹)⁻¹ by group]
      have hefE : e * f⁻¹ ∈ E₀ := mem_inf.mpr ⟨mul_mem he (inv_mem hfE), hef⟩
      have : e = e * f⁻¹ * f := by group
      rw [this]
      exact mul_mem (mem_sup_left hefE) (mem_sup_right (mem_zpowers f))
  have hE₀8 : IsEightGroup E₀ := by
    refine ⟨hE₀e, ?_⟩
    have h1 : Nat.card ↥(E₀ ⊔ zpowers f) ≤ 16 :=
      hE16 ▸ Subgroup.card_le_of_le (sup_le inf_le_left (zpowers_le.mpr hfE))
    have h2 : 16 ≤ Nat.card ↥(E₀ ⊔ zpowers f) := hE16 ▸ Subgroup.card_le_of_le hEle
    omega
  have hE₀S' : E₀ ≤ S' := fun e he => mem_inf.mpr ⟨hET (mem_inf.mp he).1, (mem_inf.mp he).2⟩
  have hTKne : T ⊓ K ≠ ⊥ := by
    intro hbot
    have h64 := GrS4.sixtyFour_le_card hKL hTKs
    rw [hbot, card_bot] at h64
    omega
  have hE₀N : E₀ ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := fun e he =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer (hET (mem_inf.mp he).1), (mem_inf.mp he).2⟩
  obtain ⟨c, hcTK, hcc, hc1, hcE₀⟩ :=
    exists_involution_inf_centralizer hT2 inf_le_left (hE₀S'.trans inf_le_left) hE₀N hTKne
  have hcE₀n : c ∉ E₀ := fun hc => hc1 (eq_one_of_commute_of_conjugate_ne hKM hKc hZK
    (hT.1 (hET hfE)) hfK (mem_inf.mp hcTK).1 (mem_inf.mp hcTK).2
    (hE.1 c (mem_inf.mp hc).1 f hfE))
  have hcS' : c ∈ S' :=
    mem_inf.mpr ⟨(mem_inf.mp hcTK).1, le_normalizer (mem_inf.mp hcTK).2⟩
  have hWE₀ : wGroup E₀ = W := wGroup_eq_of_not_stronglyIsolated_gen hGW hKper hKL hS'K hS'2
    hS'N hbS' hb2 hbc hbK hWB' hE₀S' hE₀8 ⟨c, hcS', hcc, hcE₀, hcE₀n⟩
  rw [← hWE₀]
  exact wGroup_eq_of_commute hGW (hF.1.isAbelianTwoOfRank hF.2.ge)
    (hE₀8.1.isAbelianTwoOfRank hE₀8.2.ge)
    (fun u hu v hv => hE.1 u (mem_sup_left hu) v (mem_inf.mp hv).1)

end CFSG.ComponentClassification.GrSLit.GrS5S
