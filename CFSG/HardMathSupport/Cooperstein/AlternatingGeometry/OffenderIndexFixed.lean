module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderFix

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {E : Subgroup (Perm Ω)}

theorem two_mul_card_FixUp_le_of_fixed {p : Ω} (hp : ∀ g ∈ E, g p = p) :
    2 * Nat.card (FixUp E) ≤ 2 ^ Nat.card (Orb E) := by
  have h1 : Nat.card (FixUp E) = Nat.card (twistFix E p).ker := by
    rw [card_FixUp_eq (i0 := p), range_twistFix_trivial hp, mul_one]
  have h2 := card_ker_twistFix_le (E := E) (i0 := p)
  have h3 := card_FixEven_mul_two_le hp
  have h4 := card_FixP_le E
  omega

theorem two_pow_le_offIdx_mul_of_fixed {p : Ω} (hp : ∀ g ∈ E, g p = p) :
    2 ^ Nat.card Ω ≤ offIdx E * 2 ^ Nat.card (Orb E) := by
  have h1 := two_mul_card_FixUp_le_of_fixed hp
  have h2 := pow_le_two_mul_card_evenVec (Ω := Ω)
  have h3 : offIdx E * Nat.card (FixUp E) = Nat.card (evenVec Ω) := offIdx_mul_card
  calc 2 ^ Nat.card Ω ≤ 2 * Nat.card (evenVec Ω) := h2
    _ = offIdx E * (2 * Nat.card (FixUp E)) := by rw [← h3]; ring
    _ ≤ offIdx E * 2 ^ Nat.card (Orb E) := Nat.mul_le_mul_left _ h1

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
