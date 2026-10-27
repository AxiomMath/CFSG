module

public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonInvolutionPackage

public section

namespace CFSG.ComponentClassification.BlockCommonSylowNontrivial

theorem image_ne_bot {G : Type*} [Group G] [Finite G]
    {component opposite elementary : Subgroup G} {rank : ℕ}
    (properties : BlockCommonInvolutionPackage.Common component opposite rank elementary) (hpositive : 1 ≤ rank)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (sylow : Sylow 2 ↥(factor ⊓ opposite)) :
    (sylow : Subgroup ↥(factor ⊓ opposite)).map (factor ⊓ opposite).subtype ≠ ⊥ := by
  have hcontained : elementary ≤ (sylow : Subgroup ↥(factor ⊓ opposite)).map (factor ⊓ opposite).subtype := by
    rw [← properties.omega factor hfactor sylow]
    exact InvolutionGeneratedSubgroup.le _
  intro hbot
  have heq : elementary = ⊥ := le_antisymm (hbot ▸ hcontained) bot_le
  exact (elementary.nontrivial_iff_ne_bot.mp (properties.nontrivial hpositive)) heq

end CFSG.ComponentClassification.BlockCommonSylowNontrivial
