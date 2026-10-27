module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Types

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
theorem card_S_le_of_center_R (hD : Foote5AutData 𝕊 Lin)
    (hSR : ∀ y ∈ S, ∀ r ∈ S ⊓ L, y * r = r * y) : Nat.card S ≤ 4 * Nat.card Q := by
  have h1 := card_eq_card_inf_mul_card_actImage ε h.S_le
  rw [h.inf_coreActionKernel] at h1
  have hfix : ∀ α ∈ actImage L ε S, ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
    intro α hα ρ hρ
    obtain ⟨y, hy, rfl⟩ := (mem_actImage ε h.S_le).mp hα
    exact (h.actG_fix_iff ε hy).mpr (hSR y hy) ρ hρ
  have h2 := (hD.centralizer_sylow (h.Rbar ε) _ (isPGroup_actImage ε h.isPGroup_S) hfix).2
  rw [h1]
  calc Nat.card Q * Nat.card (actImage L ε S) ≤ Nat.card Q * 4 := Nat.mul_le_mul_left _ h2
    _ = 4 * Nat.card Q := mul_comm _ _

end Sec5

end CFSG.ComponentClassification.Foote5
