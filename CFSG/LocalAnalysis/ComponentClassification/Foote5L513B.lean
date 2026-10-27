module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L513A

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem inner_conj_s_L513 (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hT2 : Nat.card T = 2 * Nat.card S)
    {s : G} (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s) {u : G} (hzu : IsConj z u)
    (huR : ∀ r ∈ S ⊓ L, u * r = r * u) (hut : u ≠ t) :
    actG L ε (s * u * s⁻¹) ∈ innAut5 𝕊 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hszs : s * z * s⁻¹ = t := by rw [hz]; group
  have hs'zs : s⁻¹ * z * s = t := by
    rw [hz]
    have h1 := h.tZ _ hss
    calc s⁻¹ * (s⁻¹ * t * s) * s = (s * s)⁻¹ * (t * (s * s)) := by group
      _ = (s * s)⁻¹ * ((s * s) * t) := by rw [← h1]
      _ = t := by group
  obtain ⟨g, hg⟩ := isConj_iff.mp hzu
  have hRg : conjugate (S ⊓ L) g ≤ centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := huR _ hx
    refine mem_centralizer_singleton_iff.mpr ?_
    calc x * z = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hg, ← h1]
      _ = z * x := by group
  have hSz : IsSylowOf 2 S (centralizer ({z} : Set G)) :=
    h.sylS.of_le (fun x hx => mem_centralizer_singleton_iff.mpr (h.zS x hx))
      h.centralizer_le_normalizer
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf hSz hRg (h.R_sylow.isPGroup.map _)
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.mp hcC
  obtain ⟨g', hg'⟩ : ∃ w, w = g * c := ⟨_, rfl⟩
  have hR₂S : conjugate (S ⊓ L) g' ≤ S := by
    intro x hx
    rw [mem_conjugate_iff, hg'] at hx
    have h1 : c * x * c⁻¹ ∈ conjugate (S ⊓ L) g := by
      rw [mem_conjugate_iff, show g * (c * x * c⁻¹) * g⁻¹ = g * c * x * (g * c)⁻¹ by group]
      exact hx
    have h2 := hc _ h1
    rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at h2
  have hug' : g' * z * g'⁻¹ = u := by
    rw [hg', show g * c * z * (g * c)⁻¹ = g * (c * z) * c⁻¹ * g⁻¹ by group, hcz,
      show g * (z * c) * c⁻¹ * g⁻¹ = g * z * g⁻¹ by group, hg]
  have hR₃S : conjugate (S ⊓ L) (g' * s) ≤ S := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 : s * x * s⁻¹ ∈ conjugate (S ⊓ L) g' := by
      rw [mem_conjugate_iff, show g' * (s * x * s⁻¹) * g'⁻¹ = g' * s * x * (g' * s)⁻¹ by group]
      exact hx
    have h2 := (mem_normalizer_iff.mp (inv_mem hsN) _).mp (hR₂S h1)
    rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at h2
  have h1 := h.conj_t_mem_Qt_L513 ε hD hna hR₂S
  have h2 := h.conj_t_mem_Qt_L513 ε hD hna hR₃S
  obtain ⟨t₂, ht₂⟩ : ∃ w, w = g'⁻¹ * t * g' := ⟨_, rfl⟩
  rw [← ht₂] at h1
  rw [show (g' * s)⁻¹ * t * (g' * s) = s⁻¹ * t₂ * s by rw [ht₂]; group] at h2
  have hQ'bot := h.inf_conjugate_Q_inv_L513 hsT hz
  have htQ' := t_mem_conjugate_Q_L513 h.zQ hz
  have hQ'1 : ∀ w : G, w ∈ Q → w ∈ conjugate Q s⁻¹ → w = 1 := fun w hw hw' => by
    have h3 : w ∈ Q ⊓ conjugate Q s⁻¹ := mem_inf.mpr ⟨hw, hw'⟩
    rwa [hQ'bot, mem_bot] at h3
  have h2' : t₂ ∈ conjugate Q s⁻¹ ∨ t₂ * z ∈ conjugate Q s⁻¹ := by
    rcases h2 with h3 | h3
    · left
      rw [mem_conjugate_iff, inv_inv]
      exact h3
    · right
      rw [mem_conjugate_iff, inv_inv, show s⁻¹ * (t₂ * z) * s = s⁻¹ * t₂ * s * (s⁻¹ * z * s) by
        group, hs'zs]
      exact h3
  have ht₂1 : t₂ ≠ 1 := fun h3 => h.t_ne_one (by
    calc t = g' * t₂ * g'⁻¹ := by rw [ht₂]; group
      _ = 1 := by rw [h3]; group)
  have ht₂zt : t₂ ≠ z * t := by
    have h3 := h.conj_z_ne_zt hT2 hsT hsS hz (s⁻¹ * g')
    rwa [show (s⁻¹ * g')⁻¹ * z * (s⁻¹ * g') = g'⁻¹ * (s * z * s⁻¹) * g' by group, hszs,
      ← ht₂] at h3
  have htz := h.zS t h.tS
  have ht₂t : t₂ = t := by
    rcases h1 with h3 | h3 <;> rcases h2' with h4 | h4
    · exact absurd (hQ'1 _ h3 h4) ht₂1
    · have h5 := hQ'1 _ (mul_mem h3 h.zQ) h4
      exfalso
      apply hut
      rw [← hug', eq_inv_of_mul_eq_one_right h5, ht₂,
        show g' * (g'⁻¹ * t * g')⁻¹ * g'⁻¹ = t⁻¹ by group,
        inv_eq_of_mul_eq_one_left h.t_mul_self]
    · have h5 := hQ'1 _ h3 (mul_mem h4 htQ')
      rw [eq_inv_of_mul_eq_one_left h5, inv_eq_of_mul_eq_one_left h.t_mul_self]
    · exfalso
      have h5 : t₂ * t * z ∈ Q := mul_mem h3 h.zQ
      have h6 : t₂ * t * z ∈ conjugate Q s⁻¹ := by
        rw [mul_assoc, htz, ← mul_assoc]
        exact mul_mem h4 htQ'
      have h7 := hQ'1 _ h5 h6
      apply ht₂zt
      calc t₂ = t₂ * t * z * (z * t) := by
            rw [show t₂ * t * z * (z * t) = t₂ * t * (z * z) * t by group, h.z_mul_self,
              mul_one, mul_assoc, h.t_mul_self, mul_one]
        _ = z * t := by rw [h7, one_mul]
  have hg't : g' * t = t * g' := by
    calc g' * t = g' * t₂ := by rw [ht₂t]
      _ = t * g' := by rw [ht₂]; group
  obtain ⟨n, hn⟩ : ∃ w, w = s * g' * s⁻¹ := ⟨_, rfl⟩
  have hnz : n * z = z * n := by
    calc n * z = s * (g' * (s⁻¹ * z * s)) * s⁻¹ := by rw [hn]; group
      _ = s * (g' * t) * s⁻¹ := by rw [hs'zs]
      _ = s * (t * g') * s⁻¹ := by rw [hg't]
      _ = (s * t * s⁻¹) * n := by rw [hn]; group
      _ = z * n := by rw [h.conj_t_eq_z hss hz]
  have hnN : n ∈ normalizer (L : Set G) :=
    h.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr hnz)
  have hsus : s * u * s⁻¹ = n * t * n⁻¹ := by
    rw [← hug', hn, ← hszs]
    group
  have htN : t ∈ normalizer (L : Set G) := le_normalizer h.tL
  rw [hsus, actG_mul ε (mul_mem hnN htN) (inv_mem hnN), actG_mul ε hnN htN, actG_inv ε hnN]
  refine conj_mem_innAut5_L513 _ ?_
  rw [actG_of_mem_self ε h.tL]
  exact ⟨_, rfl⟩

end Sec5

end CFSG.ComponentClassification.Foote5
