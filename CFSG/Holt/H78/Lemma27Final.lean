module

public import CFSG.Holt.H78.Lemma27
import CFSG.Holt.H78.KernelSplit

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise


theorem socInvFixesBlocksStatement : SocInvFixesBlocksStatement := by
  intro G _ _ Ω _ _ _ hG hB D v hv hv2 ω hvω ω' hω'
  by_cases h1 : v = 1
  · rw [h1, one_smul]
  exact (D.lemma_2_4_iv hG hB (D.socPre_le_jHull hv)
    (orderOf_eq_prime (by rw [sq]; exact hv2) h1) hvω).1 hv ω' hω'

section Final

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

theorem card_longInvSwap_eq (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {α β : Ω} (hαβ : α ≠ β) :
    Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) :=
  card_longInvSwap_eq_of_socInvFixesBlocks socInvFixesBlocksStatement hG hB hαβ

theorem holtDelta'_eq_orbit (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {α β γ : Ω} (hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta' G Ω α β) :
    holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ :=
  holtDelta'_eq_orbit_of_socInvFixesBlocks socInvFixesBlocksStatement hG hB hαβ hγ

end Final

end CFSG.Holt.H78
