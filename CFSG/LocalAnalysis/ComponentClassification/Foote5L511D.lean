module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsC

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
theorem exists_field_involution_of_not_le_Q (hDiag : Foote5DiagonalNotInQ)
    (hAut : Foote5AutStructure) (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ : 4 < Nat.card Q)
    (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S) (hT2 : Nat.card T = 2 * Nat.card S) {s : G}
    (hsT : s ∈ T) (hsS : s ∉ S) (hnot : ¬ conjugate (S ⊓ L) s ≤ Q) :
    ∃ r ∈ conjugate (S ⊓ L) s, r * r = 1 ∧ actG L ε r ∉ Lin := by
  rcases h.cases_of_not_le_Q ε hD hna hCt hT2 hsT hsS with h1 | h1
  · exact h1
  · refine absurd (h.conjugate_R_le_of_involutions fun b hb hb2 => ?_) hnot
    rcases h1 b hb with h2 | h2
    · exact h2
    · exact absurd h2 (hDiag G L₀ L Q S T z t h hAut hna hQ hCt hT2 s hsT hsS b hb hb2)

end Sec5

end CFSG.ComponentClassification.Foote5
