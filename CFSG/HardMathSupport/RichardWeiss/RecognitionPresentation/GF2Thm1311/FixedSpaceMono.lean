module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.GF2Thm1311

variable {V : Type} [CommGroup V] [Finite V]

theorem card_le_four_mul_fixed_of_mem {A : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A)
    (h : Nat.card V ≤ 4 * Nat.card {v : V | ∀ b ∈ A, b v = v}) :
    Nat.card V ≤ 4 * Nat.card {v : V | a v = v} := by
  refine h.trans (Nat.mul_le_mul_left 4 (Nat.card_mono (Set.toFinite _) ?_))
  intro v hv
  exact hv a ha

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.GF2Thm1311
