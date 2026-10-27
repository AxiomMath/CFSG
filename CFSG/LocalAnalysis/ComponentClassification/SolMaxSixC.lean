module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightH
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightPerm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE32End
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightK

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

private theorem eq_of_mem_zpowers_of_orderOf_eq_two {X : Type} [Group X] {t y : X}
    (ht : orderOf t = 2) (hy : y ∈ zpowers t) (hyo : orderOf y = 2) : y = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, ht] at hyo ⊢
  simp only [Nat.cast_ofNat] at hyo ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero, orderOf_one] at hyo
    exact absurd hyo (by norm_num)
  · rw [h, zpow_one]

theorem signalizerNineEightLiftInput_of_perm_unique (hP : EightLiftPermInput)
    (hL2 : SignalizerNineTwoPointCentralizerUniqueInput) (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput) :
    SignalizerNineEightLiftInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit hQt f hfH
    hfs hft hf2 hfN hf2pt
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := (hQK htQ).1
  have htK : t ∈ UnbalancedLayer.coreActionKernel M := (hQK htQ).2
  have hto : orderOf t = 2 := S₀.pair.1.1
  have ht2 : t * t = 1 := by rw [← sq, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hQ2' : Nat.card Q = 2 := by rw [hQt, Nat.card_zpowers, hto]
  have hQu : ∀ y ∈ Q, orderOf y = 2 → y = t := fun y hy hyo =>
    eq_of_mem_zpowers_of_orderOf_eq_two hto (hQt ▸ hy) hyo
  have hK2 : ∀ P : Subgroup X, P ≤ H ⊓ UnbalancedLayer.coreActionKernel M → IsPGroup 2 P →
      Nat.card P ≤ 2 := by
    intro P hPK hP2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP2
    have hdvd : 2 ^ k ∣ Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M) := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hPK
    have hkle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      Nat.card_pos.ne').mp hdvd
    have h1 : 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 = 2 := by
      rw [← hQcard, hQ2']
    rw [hk]
    calc 2 ^ k ≤ 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 :=
          Nat.pow_le_pow_right (by norm_num) hkle
      _ = 2 := h1
  obtain ⟨N, hNK, hNodd, hNt⟩ := exists_oddPart_of_card_le_two
    (K := H ⊓ UnbalancedLayer.coreActionKernel M) ⟨htH, htK⟩ ht2 ht1 hK2
  have hCt : centralizer ({t} : Set X) ≤ H := hCQ t htQ hto
  have hsH : s ∈ H := hSH hsS
  have hst : s * t = t * s := htZ s hsS
  have hρt : ρ ⟨t, hHN htH⟩ = 1 := hρ.eq_one_of_mem_coreActionKernel (by norm_num) htK
  have hf4 : f * f * (f * f) = 1 := by
    rcases hf2 with h | h <;> rw [h]
    · exact one_mul 1
    · exact ht2
  have hσ8 : (ρ ⟨s, hsN⟩).support.card = 8 :=
    card_support_eq_eight_of_mem_alternatingGroup hρs2 h5 hsA
  have hτσ : ρ ⟨f, hfN⟩ * ρ ⟨s, hsN⟩ = ρ ⟨s, hsN⟩ * ρ ⟨f, hfN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hfs
  obtain ⟨w, hw0, hwσ, hww, hw2, hwc, hwA, hwne⟩ := exists_eight_swap_frame hρs2 hσ8 hf2pt hτσ
  obtain ⟨μ, hμM, -, hμs, hμt, hμf, hμμ, hμ2, hμρ⟩ := hρ.exists_commuting_lifts hsN (hHN htH)
    hfN hs2 ht2 hf4 hst hfs hft hρt (v := w) hw0 hwσ hww hw2
    (fun i => by rw [hw0]; exact hwA i) (fun i hi => (hwne i 0 hi).1)
  have hcs : ∀ y z : X, y * s = s * y → z * s = s * z → y * z * s = s * (y * z) := by
    intro y z hy hz
    calc y * z * s = y * (z * s) := mul_assoc _ _ _
      _ = y * (s * z) := by rw [hz]
      _ = y * s * z := (mul_assoc _ _ _).symm
      _ = s * y * z := by rw [hy]
      _ = s * (y * z) := mul_assoc _ _ _
  have hct2 : ∀ y z : X, y * t = t * y → z * t = t * z → y * z * t = t * (y * z) := by
    intro y z hy hz
    calc y * z * t = y * (z * t) := mul_assoc _ _ _
      _ = y * (t * z) := by rw [hz]
      _ = y * t * z := (mul_assoc _ _ _).symm
      _ = t * y * z := by rw [hy]
      _ = t * (y * z) := mul_assoc _ _ _
  have hsqp : ∀ y z : X, y * z = z * y → y * z * (y * z) = y * y * (z * z) := by
    intro y z hyz
    calc y * z * (y * z) = y * (z * y) * z := by simp only [mul_assoc]
      _ = y * (y * z) * z := by rw [← hyz]
      _ = y * y * (z * z) := by simp only [mul_assoc]
  have hsqt : ∀ y : X, y * t = t * y → y * y = 1 → y * t * (y * t) = 1 := by
    intro y hyt hy2
    rw [hsqp _ _ hyt, hy2, ht2, one_mul]
  have hrH : ∀ i, μ i * f ∈ H := fun i => H.mul_mem (hMH (hμM i)) hfH
  have hrs : ∀ i, μ i * f * s = s * (μ i * f) := fun i => hcs _ _ (hμs i) hfs
  have hrt : ∀ i, μ i * f * t = t * (μ i * f) := fun i => hct2 _ _ (hμt i) hft
  have hrr : ∀ i j, μ i * f * (μ j * f) = μ j * f * (μ i * f) := fun i j => by
    calc μ i * f * (μ j * f) = μ i * (f * μ j) * f := by simp only [mul_assoc]
      _ = μ i * (μ j * f) * f := by rw [← hμf j]
      _ = μ i * μ j * f * f := by simp only [mul_assoc]
      _ = μ j * μ i * f * f := by rw [hμμ i j]
      _ = μ j * (μ i * f) * f := by simp only [mul_assoc]
      _ = μ j * (f * μ i) * f := by rw [hμf i]
      _ = μ j * f * (μ i * f) := by simp only [mul_assoc]
  have hr2 : ∀ i, μ i * f * (μ i * f) = f * f := fun i => by
    rw [hsqp _ _ (hμf i), hμ2 i, one_mul]
  have hrρ : ∀ i, ρ ⟨μ i * f, hHN (hrH i)⟩ = w i := fun i => by
    have h1 : (⟨μ i * f, hHN (hrH i)⟩ : ↥(normalizer (M : Set X))) =
        ⟨μ i, le_normalizer (hμM i)⟩ * ⟨f, hfN⟩ := rfl
    rw [h1, map_mul, hμρ i, ← hw0, mul_assoc, hw2 0, mul_one]
  have hts : t = g * s * g⁻¹ := by rw [← hgs]; group
  have hψN : ∀ y : X, y * s = s * y → g * y * g⁻¹ ∈ normalizer (M : Set X) := fun y hy => by
    refine hHN (hCt ?_)
    rw [mem_centralizer_singleton_iff, hts]
    calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hy]
      _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
  have hψmul : ∀ (y z : X) (hy : g * y * g⁻¹ ∈ normalizer (M : Set X))
      (hz : g * z * g⁻¹ ∈ normalizer (M : Set X))
      (hyz : g * (y * z) * g⁻¹ ∈ normalizer (M : Set X)),
      ρ ⟨g * y * g⁻¹, hy⟩ * ρ ⟨g * z * g⁻¹, hz⟩ = ρ ⟨g * (y * z) * g⁻¹, hyz⟩ := by
    intro y z hy hz hyz
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹
    group
  have hψeq : ∀ (y z : X) (hy : g * y * g⁻¹ ∈ normalizer (M : Set X))
      (hz : g * z * g⁻¹ ∈ normalizer (M : Set X)), y = z →
      ρ ⟨g * y * g⁻¹, hy⟩ = ρ ⟨g * z * g⁻¹, hz⟩ := by
    rintro y z hy hz rfl
    rfl
  have hψone : ∀ (y : X) (hy : g * y * g⁻¹ ∈ normalizer (M : Set X)), y = 1 →
      ρ ⟨g * y * g⁻¹, hy⟩ = 1 := by
    rintro y hy rfl
    have h1 : (⟨g * 1 * g⁻¹, hy⟩ : ↥(normalizer (M : Set X))) = 1 :=
      Subtype.ext (show g * 1 * g⁻¹ = 1 by group)
    rw [h1, map_one]
  have hu2 : ρ ⟨g * t * g⁻¹, hψN t hst.symm⟩ * ρ ⟨g * t * g⁻¹, hψN t hst.symm⟩ = 1 := by
    rw [hψmul _ _ _ _ (hψN _ (hcs t t hst.symm hst.symm))]
    exact hψone _ _ ht2
  refine hP (ρ ⟨g * t * g⁻¹, hψN t hst.symm⟩)
    (fun i => ρ ⟨g * (μ i * f) * g⁻¹, hψN _ (hrs i)⟩) hu2 (hd4 t htQ hst.symm ht1 _)
    (fun i => ?_) (fun i j => ?_) (fun i => ?_) (fun i j hij => ?_)
  · rw [hψmul _ _ _ _ (hψN _ (hcs _ _ (hrs i) hst.symm)),
      hψmul _ _ _ _ (hψN _ (hcs _ _ hst.symm (hrs i)))]
    exact hψeq _ _ _ _ (hrt i)
  · rw [hψmul _ _ _ _ (hψN _ (hcs _ _ (hrs i) (hrs j))),
      hψmul _ _ _ _ (hψN _ (hcs _ _ (hrs j) (hrs i)))]
    exact hψeq _ _ _ _ (hrr i j)
  · rcases hf2 with hff | hff
    · right
      have hri2 : μ i * f * (μ i * f) = 1 := by rw [hr2 i, hff]
      have hCr : centralizer ({μ i * f} : Set X) ≤ H :=
        hL2 X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
          hSH hS2 hScard htZ hCQ hd3 hQu (μ i * f) (hrH i) hri2 (hrt i) (hHN (hrH i))
          (by rw [hrρ i]; exact hwc i)
      have hrtH : μ i * f * t ∈ H := H.mul_mem (hrH i) htH
      have hrt2 : μ i * f * t * (μ i * f * t) = 1 := hsqt _ (hrt i) hri2
      have hrtρ : ρ ⟨μ i * f * t, hHN hrtH⟩ = w i := by
        have h1 : (⟨μ i * f * t, hHN hrtH⟩ : ↥(normalizer (M : Set X))) =
            ⟨μ i * f, hHN (hrH i)⟩ * ⟨t, hHN htH⟩ := rfl
        rw [h1, map_mul, hrρ i, hρt, mul_one]
      have hCrt : centralizer ({μ i * f * t} : Set X) ≤ H :=
        hL2 X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
          hSH hS2 hScard htZ hCQ hd3 hQu (μ i * f * t) hrtH hrt2 (hct2 _ _ (hrt i) rfl)
          (hHN hrtH) (by rw [hrtρ]; exact hwc i)
      refine ⟨?_, S₀.five_le_card_support_of_centralizer_le hT13 hML hSch hJM hsup hρ hHN hNK
        hNodd hgs hsH hρs2 hσ8 hri2 (hrs i) hCr _, ?_⟩
      · rw [hψmul _ _ _ _ (hψN _ (hcs _ _ (hrs i) (hrs i)))]
        exact hψone _ _ hri2
      · rw [hψmul _ _ _ _ (hψN _ (hcs _ _ (hrs i) hst.symm))]
        exact S₀.five_le_card_support_of_centralizer_le hT13 hML hSch hJM hsup hρ hHN hNK hNodd
          hgs hsH hρs2 hσ8 hrt2 (hcs _ _ (hrs i) hst.symm) hCrt _
    · left
      rw [hψmul _ _ _ _ (hψN _ (hcs _ _ (hrs i) (hrs i)))]
      exact hψeq _ _ _ _ (by rw [hr2 i, hff])
  · have hyH : μ i * f * (μ j * f) ∈ H := H.mul_mem (hrH i) (hrH j)
    have hy2 : μ i * f * (μ j * f) * (μ i * f * (μ j * f)) = 1 := by
      rw [hsqp _ _ (hrr i j), hr2 i, hr2 j]
      exact hf4
    have hys := hcs _ _ (hrs i) (hrs j)
    have hyt := hct2 _ _ (hrt i) (hrt j)
    have hyρ : ρ ⟨μ i * f * (μ j * f), hHN hyH⟩ = w i * w j := by
      have h1 : (⟨μ i * f * (μ j * f), hHN hyH⟩ : ↥(normalizer (M : Set X))) =
          ⟨μ i * f, hHN (hrH i)⟩ * ⟨μ j * f, hHN (hrH j)⟩ := rfl
      rw [h1, map_mul, hrρ i, hrρ j]
    have hne := S₀.rho_conj_ne_one_of_support_le_four h33 h35 hT13 hML hSch hMH hMpc hJM hHN
      hsup θ hρ hQK hQ2 htQ hCt hNodd hNt hgs hyH hy2 hys hyt
      (by rw [hyρ]; exact (hwne i j hij).1) (by rw [hyρ]; exact (hwne i j hij).2) (hψN _ hys)
    refine ⟨?_, fun h => ?_⟩
    · rw [hψmul _ _ _ _ (hψN _ hys)]
      exact hne
    · have hy'H : μ i * f * (μ j * f) * t ∈ H := H.mul_mem hyH htH
      have hy's := hcs _ _ hys hst.symm
      have hy'ρ : ρ ⟨μ i * f * (μ j * f) * t, hHN hy'H⟩ = w i * w j := by
        have h1 : (⟨μ i * f * (μ j * f) * t, hHN hy'H⟩ : ↥(normalizer (M : Set X))) =
            ⟨μ i * f * (μ j * f), hHN hyH⟩ * ⟨t, hHN htH⟩ := rfl
        rw [h1, map_mul, hyρ, hρt, mul_one]
      refine S₀.rho_conj_ne_one_of_support_le_four h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup
        θ hρ hQK hQ2 htQ hCt hNodd hNt hgs hy'H (hsqt _ hyt hy2) hy's (hct2 _ _ hyt rfl)
        (by rw [hy'ρ]; exact (hwne i j hij).1) (by rw [hy'ρ]; exact (hwne i j hij).2)
        (hψN _ hy's) ?_
      rw [← hψmul _ _ (hψN _ hys) (hψN t hst.symm) (hψN _ hy's),
        ← hψmul _ _ (hψN _ (hrs i)) (hψN _ (hrs j)) (hψN _ hys), h, hu2]

theorem signalizerNineFusionCountEightInput_holds
    (hbal : Sol78.BalanceTwoComponentInput) (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) :
    SignalizerNineFusionCountEightInput :=
  signalizerNineFusionCountEightInput_of_steps
    (signalizerNineEightKernelCentralizerInput_holds hT13 hML hSch hPump hN1)
    (signalizerNineEightEvenInput_of_lift
      (signalizerNineEightLiftInput_of_perm_unique eightLiftPermInput_holds
        (signalizerNineTwoPointCentralizerUniqueInput_holds hbal h33 h35 hT13 hML hSch hPump hN1)
        h33 h35 hT13 hML hSch))
    (signalizerNineEightFusionCaseInput_of_fusion signalizerNineEightFusionInput_holds h33 h35 hT13
      hML hSch)

end CFSG.ComponentClassification.SolMax
