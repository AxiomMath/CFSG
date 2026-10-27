module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511B
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510G

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

theorem conj_t_commute {s : G} (hsN : s ∈ normalizer (S : Set G)) :
    ∀ g ∈ S, g * (s⁻¹ * t * s) = (s⁻¹ * t * s) * g := by
  intro g hg
  have h1 := h.tZ _ (conj_mem_of_mem_normalizer (inv_mem hsN) hg)
  rw [inv_inv] at h1
  calc g * (s⁻¹ * t * s) = s⁻¹ * ((s * g * s⁻¹) * t) * s := by group
    _ = s⁻¹ * (t * (s * g * s⁻¹)) * s := by rw [h1]
    _ = (s⁻¹ * t * s) * g := by group

theorem orderOf_conj_t (s : G) : orderOf (s⁻¹ * t * s) = 2 := by
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  refine orderOf_eq_prime ?_ fun h1 => h.t_ne_one ?_
  · rw [sq, show s⁻¹ * t * s * (s⁻¹ * t * s) = s⁻¹ * (t * t) * s by group, ht22]
    group
  · calc t = s * (s⁻¹ * t * s) * s⁻¹ := by group
      _ = 1 := by rw [h1]; group

include ε in
theorem repoint_conj_t_of_lemmas (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S)
    (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S) :
    Sec5 G L₀ (footeF L₀ (s⁻¹ * t * s)) Q S T (s⁻¹ * t * s) t ∧
      S ⊓ footeF L₀ (s⁻¹ * t * s) = S ⊓ L := by
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have huQ := h.conj_t_mem_Q ε hD hna hCt hT2 hsT hsS
  exact ⟨h.repoint huQ (h.orderOf_conj_t s) (h.conj_t_commute hsN),
    h.inf_footeF_eq huQ (h.orderOf_conj_t s) (h.conj_t_commute hsN)⟩

theorem repoint_conj_t
    (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups) (hB4 : GoldschmidtCorB4)
    (hAut : Foote5AutStructure) (hMW : MacWilliamsStatement)
    (hFC : Foote5FieldCentralizer) {s : G} (hsT : s ∈ T) (hsS : s ∉ S) :
    Sec5 G L₀ (footeF L₀ (s⁻¹ * t * s)) Q S T (s⁻¹ * t * s) t ∧
      S ⊓ footeF L₀ (s⁻¹ * t * s) = S ⊓ L := by
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  exact h.repoint_conj_t_of_lemmas ε hD (h.nonabelian_R_of_not_sylow hGH hKG hAut hMW hST)
    (fun y hyT hyt => h.mem_S_of_commute_t_of_inputs hGH hKG hB4 hAut hMW hFC hyT hyt)
    (h.card_T_eq_two_mul hGH hKG hB4 hAut hMW hFC) hsT hsS

end Sec5

end CFSG.ComponentClassification.Foote5
