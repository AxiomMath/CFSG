module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCN

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem signalizerNineFusionCountSplitInput_of_six_local
    (hbal : Sol78.BalanceTwoComponentInput) (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hL8 : SignalizerNineFusionCountEightInput) (hD : SignalizerNineSixDihedralLocalInput) :
    SignalizerNineFusionCountSplitInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsplit
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  by_cases hsA : ρ ⟨s, hsN⟩ ∈ alternatingGroup (Fin 9)
  · exact hL8 X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
      hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA (hsplit hsA)
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S₀.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htK := S₀.t_mem_coreActionKernel_of_sup h33 h35 hT13 hML hSch hHN hsup
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S₀.pair.1.1, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := S₀.pair.1.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hts : t * s = s * t := (htZ s hsS).symm
  have hsH : s ∈ H := hSH hsS
  have htN : t ∈ normalizer (M : Set X) := hHN htH
  have hρt : ρ ⟨t, htN⟩ = 1 := hρ.eq_one_of_mem_coreActionKernel (by norm_num) htK
  set σ := ρ ⟨s, hsN⟩ with hσdef
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hρs1 (Equiv.ext h)
  have hσa : σ (σ a) = a := by rw [← Perm.mul_apply, hρs2, Perm.one_apply]
  have hτσ : σ * swap a (σ a) = swap a (σ a) * σ := by
    rw [Equiv.mul_swap_eq_swap_mul, hσa, swap_comm]
  obtain ⟨b, hbdef⟩ : ∃ b, b = σ * swap a (σ a) := ⟨_, rfl⟩
  have hbA : b ∈ alternatingGroup (Fin 9) := by
    have hsσ : Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Perm.sign σ) with h | h
      · exact absurd (Perm.mem_alternatingGroup.mpr h) hsA
      · exact h
    rw [Perm.mem_alternatingGroup, hbdef, Perm.sign_mul, Perm.sign_swap (Ne.symm ha), hsσ]
    decide
  have hb2 : b * b = 1 := by
    rw [hbdef]
    calc σ * swap a (σ a) * (σ * swap a (σ a)) = σ * (swap a (σ a) * σ) * swap a (σ a) := by
          group
      _ = σ * (σ * swap a (σ a)) * swap a (σ a) := by rw [hτσ]
      _ = (σ * σ) * (swap a (σ a) * swap a (σ a)) := by group
      _ = 1 := by rw [hρs2, swap_mul_self, one_mul]
  have hsNQ : s ∈ normalizer (Q : Set X) :=
    le_normalizer_of_sylow_kernel hHN hQK hQcard hQS hSH hS2 hsS
  set B₀ := Q ⊔ zpowers s with hB₀def
  have hB₀2 : IsPGroup 2 B₀ :=
    hQ2.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self hs2) (zpowers_le.mpr hsNQ)
  have hB₀H : B₀ ≤ H := sup_le (hQK.trans inf_le_left) (zpowers_le.mpr hsH)
  have hB₀N : B₀ ≤ normalizer (M : Set X) := hB₀H.trans hHN
  have hbB : ∀ (y : X) (hy : y ∈ B₀), b * ρ ⟨y, hB₀N hy⟩ = ρ ⟨y, hB₀N hy⟩ * b := by
    set Z : Subgroup X := ((centralizer ({b} : Set (Perm (Fin 9)))).comap ρ).map
      (normalizer (M : Set X)).subtype with hZdef
    have hQZ : Q ≤ Z := fun q hq => by
      refine ⟨⟨q, hHN (hQK hq).1⟩, ?_, rfl⟩
      have h1 : ρ ⟨q, hHN (hQK hq).1⟩ = 1 :=
        hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK hq).2
      show ρ ⟨q, hHN (hQK hq).1⟩ ∈ centralizer ({b} : Set (Perm (Fin 9)))
      rw [h1]
      exact one_mem _
    have hsZ : s ∈ Z := by
      refine ⟨⟨s, hsN⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr ?_), rfl⟩
      change σ * b = b * σ
      rw [hbdef]
      calc σ * (σ * swap a (σ a)) = σ * (swap a (σ a) * σ) := by rw [hτσ]
        _ = σ * swap a (σ a) * σ := by group
    intro y hy
    obtain ⟨y', hy', hyy⟩ := sup_le hQZ (zpowers_le.mpr hsZ) hy
    have h1 : (⟨y, hB₀N hy⟩ : ↥(normalizer (M : Set X))) = y' := Subtype.ext hyy.symm
    rw [h1]
    exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hy')).symm
  obtain ⟨x, hxM, hxC, hx2, hρx⟩ := exists_lift_involution hρ hB₀N hB₀2 hbA hb2 hbB
  have hxs : s * x = x * s := mem_centralizer_iff.mp hxC s (mem_sup_right (mem_zpowers s))
  have hxt : t * x = x * t := mem_centralizer_iff.mp hxC t (mem_sup_left htQ)
  obtain ⟨f, hfdef⟩ : ∃ f, f = s * x := ⟨_, rfl⟩
  have hfH : f ∈ H := by rw [hfdef]; exact mul_mem hsH (hMH hxM)
  have hfN : f ∈ normalizer (M : Set X) := hHN hfH
  have hf2 : f * f = 1 := by
    rw [hfdef]
    calc s * x * (s * x) = s * (x * s) * x := by group
      _ = s * (s * x) * x := by rw [hxs]
      _ = (s * s) * (x * x) := by group
      _ = 1 := by rw [hs2, hx2, one_mul]
  have hft : f * t = t * f := by
    rw [hfdef]
    calc s * x * t = s * (x * t) := by group
      _ = s * (t * x) := by rw [hxt]
      _ = (s * t) * x := by group
      _ = (t * s) * x := by rw [hts]
      _ = t * (s * x) := by group
  have hρf : ρ ⟨f, hfN⟩ = swap a (σ a) := by
    have h1 : (⟨f, hfN⟩ : ↥(normalizer (M : Set X))) = ⟨s, hsN⟩ * ⟨x, le_normalizer hxM⟩ :=
      Subtype.ext hfdef
    rw [h1, map_mul, hρx, hbdef, ← mul_assoc]
    change σ * σ * swap a (σ a) = swap a (σ a)
    rw [hρs2, one_mul]
  have hf2pt : (ρ ⟨f, hfN⟩).support.card = 2 := by
    rw [hρf]
    exact Perm.card_support_swap (Ne.symm ha)
  have hftH : f * t ∈ H := mul_mem hfH htH
  have hftN : f * t ∈ normalizer (M : Set X) := hHN hftH
  have hft2 : f * t * (f * t) = 1 := by
    calc f * t * (f * t) = f * (t * f) * t := by group
      _ = f * (f * t) * t := by rw [hft]
      _ = (f * f) * (t * t) := by group
      _ = 1 := by rw [hf2, ht2, one_mul]
  have hftt : f * t * t = t * (f * t) := by
    calc f * t * t = t * f * t := by rw [hft]
      _ = t * (f * t) := by group
  have hft2pt : (ρ ⟨f * t, hftN⟩).support.card = 2 := by
    have h1 : (⟨f * t, hftN⟩ : ↥(normalizer (M : Set X))) = ⟨f, hfN⟩ * ⟨t, htN⟩ := Subtype.ext rfl
    rw [h1, map_mul, hρt, mul_one]
    exact hf2pt
  have hags : t = g * s * g⁻¹ := by rw [← hgs]; group
  have hconjC : ∀ y : X, y * s = s * y → (g * y * g⁻¹) * t = t * (g * y * g⁻¹) := by
    intro y hy
    rw [hags]
    calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hy]
      _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
  have hfs : f * s = s * f := by
    rw [hfdef]
    calc s * x * s = s * (x * s) := by group
      _ = s * (s * x) := by rw [hxs]
  set t₁ := g * t * g⁻¹ with ht₁def
  set f₁ := g * f * g⁻¹ with hf₁def
  have ht₁t : t₁ * t = t * t₁ := hconjC t hts
  have hf₁t : f₁ * t = t * f₁ := hconjC f hfs
  have ht₁H : t₁ ∈ H := hCt (mem_centralizer_singleton_iff.mpr ht₁t)
  have hf₁H : f₁ ∈ H := hCt (mem_centralizer_singleton_iff.mpr hf₁t)
  have hconj2 : ∀ y : X, y * y = 1 → g * y * g⁻¹ * (g * y * g⁻¹) = 1 := fun y hy => by
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy]; group
  have h12 : t₁ * f₁ = f₁ * t₁ := by
    rw [ht₁def, hf₁def]
    calc g * t * g⁻¹ * (g * f * g⁻¹) = g * (t * f) * g⁻¹ := by group
      _ = g * (f * t) * g⁻¹ := by rw [hft]
      _ = g * f * g⁻¹ * (g * t * g⁻¹) := by group
  have hback : ∀ y z : X, y * (g * z * g⁻¹) = (g * z * g⁻¹) * y →
      (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) := by
    intro y z h
    calc g⁻¹ * y * g * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * y) * g := by rw [h]
      _ = z * (g⁻¹ * y * g) := by group
  have hC₁ : ∀ y ∈ centralizer ({t₁} : Set X), g⁻¹ * y * g ∈ H := fun y hy =>
    hCt (mem_centralizer_singleton_iff.mpr (hback y t (mem_centralizer_singleton_iff.mp hy)))
  have ht₁N : t₁ ∈ normalizer (M : Set X) := hHN ht₁H
  have h6le : 6 ≤ (ρ ⟨t₁, ht₁N⟩).support.card := hd4 t htQ hts ht1 ht₁N
  have ht₁2 : t₁ * t₁ = 1 := hconj2 t ht2
  have hρt₁2 : ρ ⟨t₁, ht₁N⟩ ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, ← map_mul]
    have h1 : (⟨t₁, ht₁N⟩ : ↥(normalizer (M : Set X))) * ⟨t₁, ht₁N⟩ = 1 := Subtype.ext ht₁2
    rw [h1, map_one]
  have hev := two_dvd_card_support_of_pow_two_pow hρt₁2
  have hle9 : (ρ ⟨t₁, ht₁N⟩).support.card ≤ 9 := by
    have := Finset.card_le_univ (ρ ⟨t₁, ht₁N⟩).support
    rwa [Fintype.card_fin] at this
  have hne8 : (ρ ⟨t₁, ht₁N⟩).support.card ≠ 8 := fun h8 =>
    S₀.false_of_eight_of_conj h33 h35 hT13 hML hSch hL8 hW hMH hMpc hJM hHN hsup θ hρ
      hNoA9 hQK hQ2 hQcard htQ hQS hSH hS2 hScard htZ hCQ hd3 ht₁H ht₁2
      (by rw [inv_inv]) (fun h => hgH (by simpa using inv_mem h)) h8
  have h6 : (ρ ⟨t₁, hHN ht₁H⟩).support.card = 6 := by omega
  by_cases hKloc : KernelBalanceAt t J e (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)
  ·
    have hL2 := signalizerNineTwoPointCentralizerLocalInput_holds hbal h33 h35 hT13 hML hSch hPump
      hN1
    have hCf := hL2 X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ
      hQS hSH hS2 hScard htZ hCQ hd3 hKloc f hfH hf2 hft hfN hf2pt
    have hCft := hL2 X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard
      htQ hQS hSH hS2 hScard htZ hCQ hd3 hKloc (f * t) hftH hft2 hftt hftN hft2pt
    have hC₂ : ∀ y ∈ centralizer ({f₁} : Set X), g⁻¹ * y * g ∈ H := fun y hy =>
      hCf (mem_centralizer_singleton_iff.mpr (hback y f (mem_centralizer_singleton_iff.mp hy)))
    have hC₁₂ : ∀ y ∈ centralizer ({t₁ * f₁} : Set X), g⁻¹ * y * g ∈ H := by
      intro y hy
      have h1 : t₁ * f₁ = g * (f * t) * g⁻¹ := by
        rw [h12, ht₁def, hf₁def]
        group
      rw [h1] at hy
      exact hCft (mem_centralizer_singleton_iff.mpr
        (hback y (f * t) (mem_centralizer_singleton_iff.mp hy)))
    exact S₀.false_of_cover_of_six h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ hsH hρs1
      hgs ht₁H hf₁H ht₁t hf₁t ht₁2 (hconj2 f hf2) h12 hC₁ hC₂ hC₁₂ h6
  ·
    have hQu : ∃ y ∈ Q, orderOf y = 2 ∧ y ≠ t := by
      by_contra hno
      push Not at hno
      exact hKloc (kernelBalanceAt_of_uniqueInvolution ht2 ht1 ⟨htH, htK⟩ hQK hQcard hno)
    have hσ6 : (ρ ⟨s, hHN hsH⟩).support.card = 6 :=
      card_support_eq_six_of_not_mem_alternatingGroup hρs2 h5 hsA
    have hR6 := S₀.inf_centralizer_le_zpowers_of_six hT13 hML hSch hPump hN1 hJM hsup hρ hNoA9 hHN
      hQK hQ2 htQ hCt hsH hts.symm hs2 hgs hd4 hρs2 hσ6
    have hR6' : ∀ R : Subgroup X, R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → R ≤ centralizer ({s} : Set X) →
        R ≤ centralizer ({t} : Set X) → IsPGroup 2 R → R ≤ zpowers t :=
      fun R hRK hRs hRt hR2 => S₀.le_zpowers_of_le_centralizer_six h33 h35 hT13 hML hSch hPump
        hN1 hMH hMpc hJM hHN hsup θ hρ hNoA9 hQK hQ2 hQcard htQ hQS hSH hS2 hScard htZ hCQ hsS hsQ
        hgs hs2 (fun _ => hσ6) hRK hRs hRt hR2
    exact hD X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
      hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hσ6 hQu hR6
      (fun _ => h6) hR6' hKloc

end CFSG.ComponentClassification.SolMax
