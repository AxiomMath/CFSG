module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L58C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57L

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem mem_S_of_commute_t_of_lemmas (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ : 4 < Nat.card Q) {y : G}
    (hyT : y ∈ T) (hyt : y * t = t * y) : y ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hyS
  set Sst := T ⊓ centralizer ({t} : Set G) with hSst
  have hSS : S < Sst := by
    refine lt_of_le_of_ne (le_inf h.ST fun x hx => mem_centralizer_singleton_iff.mpr
      (h.tZ x hx)) fun h1 => hyS ?_
    have h2 : y ∈ Sst := mem_inf.mpr ⟨hyT, mem_centralizer_singleton_iff.mpr hyt⟩
    rwa [← h1] at h2
  obtain ⟨s, hsSst, hsS, hsN⟩ :=
    exists_mem_normalizer_not_mem_of_lt (h.sylT.isPGroup.to_le inf_le_left) hSS
  have hsT := (mem_inf.mp hsSst).1
  have hst : s * t = t * s := mem_centralizer_singleton_iff.mp (mem_inf.mp hsSst).2
  have hsQ := h.not_mem_normalizer_Q hsT hsS
  have hQsS := h.conjugate_Q_le hsN
  have hQsR : conjugate Q s ⊓ (S ⊓ L) = ⊥ := by
    by_contra hne
    have hSN : S ≤ normalizer ((conjugate Q s ⊓ (S ⊓ L) : Subgroup G) : Set G) :=
      le_normalizer_of_conj_mem fun g hg w hw => mem_inf.mpr
        ⟨h.conj_mem_conjugate_Q hsN hg (mem_inf.mp hw).1, h.conj_mem_R hg (mem_inf.mp hw).2⟩
    obtain ⟨u, huN, hu2, huS⟩ :=
      exists_involution_center h.isPGroup_S (inf_le_left.trans hQsS) hSN hne
    rcases h.center_R hna (mem_inf.mp huN).2 (fun r hr => (huS r (mem_inf.mp hr).1).symm)
      with h1 | h1
    · rw [h1, orderOf_one] at hu2
      omega
    · apply h.t_not_mem_Q
      have h2 := mem_conjugate_iff.mp (h1 ▸ (mem_inf.mp huN).1 : t ∈ conjugate Q s)
      rwa [hst, mul_inv_cancel_right] at h2
  have hcent : ∀ a ∈ conjugate Q s, ∀ r ∈ S ⊓ L, a * r = r * a := by
    intro a ha r hr
    have haS := hQsS ha
    have h1 : a * r * a⁻¹ * r⁻¹ ∈ conjugate Q s ⊓ (S ⊓ L) := by
      refine mem_inf.mpr ⟨?_, mul_mem (h.conj_mem_R haS hr) (inv_mem hr)⟩
      rw [show a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) by group]
      exact mul_mem ha (h.conj_mem_conjugate_Q hsN (mem_inf.mp hr).1 (inv_mem ha))
    rw [hQsR, mem_bot] at h1
    calc a * r = a * r * a⁻¹ * r⁻¹ * (r * a) := by group
      _ = r * a := by rw [h1, one_mul]
  obtain ⟨q, hq, hqq⟩ := h.exists_mul_self_ne_one_Q hQ
  have hq' : s⁻¹ * q * s ∈ conjugate Q s := by
    rw [mem_conjugate_iff]
    group
    exact hq
  have hPN : conjugate Q s ≤ normalizer (L : Set G) := hQsS.trans h.S_le
  have hfix : ∀ α ∈ actImage L ε (conjugate Q s), ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
    intro α hα ρ hρ
    obtain ⟨p, hp, rfl⟩ := (mem_actImage ε hPN).mp hα
    exact (h.actG_fix_iff ε (hQsS hp)).mpr (hcent p hp) ρ hρ
  have hsq := (hD.centralizer_sylow (h.Rbar ε) _
    (isPGroup_actImage ε (h.isPGroup_S.to_le hQsS)) hfix).1 _ (actG_mem_actImage ε hPN hq')
  have hq'S := hQsS hq'
  have h1 : s⁻¹ * q * s * (s⁻¹ * q * s) ∈ Q := by
    rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem hq'S hq'S), actG_mul ε (h.S_le hq'S) (h.S_le hq'S)]
    exact hsq
  have h2 : s⁻¹ * q * s * (s⁻¹ * q * s) ∈ Q ⊓ conjugate Q s :=
    mem_inf.mpr ⟨h1, mul_mem hq' hq'⟩
  rw [h.inf_conjugate_Q_eq_bot_of_ne hsT (fun h3 => hsQ (mem_normalizer_of_conjugate_eq h3)),
    mem_bot] at h2
  apply hqq
  calc q * q = s * (s⁻¹ * q * s * (s⁻¹ * q * s)) * s⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem mem_S_of_commute_t_of_inputs (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure) (hMW : MacWilliamsStatement)
    (hFC : Foote5FieldCentralizer) {y : G} (hyT : y ∈ T)
    (hyt : y * t = t * y) : y ∈ S := by
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  exact h.mem_S_of_commute_t_of_lemmas ε hD (h.nonabelian_R_of_not_sylow hGH hKG hAut hMW hST)
    (h.four_lt_card_Q hGH hKG hB4 hAut hMW hFC) hyT hyt

end Sec5

end CFSG.ComponentClassification.Foote5
