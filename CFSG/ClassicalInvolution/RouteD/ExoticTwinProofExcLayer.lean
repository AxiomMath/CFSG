module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerSC

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwistedE6Layer (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ n : ℕ, StatedLieAdmissible .twistedE6 n p f →
    HasQuasisimpleLayer p .twistedE6 n f

theorem excLayer_of_twistedE6 (h : TwistedE6Layer p f) : ExcLayer p f := by
  intro hp2 hq t n hexc hadm
  rcases hexc with rfl | rfl | rfl | rfl | rfl
  · exact hasQuasisimpleLayer_F4 hp2 hq hadm
  · exact hasQuasisimpleLayer_E6 hp2 hq hadm
  · exact hasQuasisimpleLayer_E7 hp2 hq hadm
  · exact hasQuasisimpleLayer_E8 hp2 hq hadm
  · exact h hp2 hq n hadm

theorem mfTwin_of_twistedE6 (h : TwistedE6Layer p f) : MFTwin p f :=
  mfTwin_of_layer (excLayer_of_twistedE6 h)

end CFSG.ClassicalInvolution.RouteD.Exotic
