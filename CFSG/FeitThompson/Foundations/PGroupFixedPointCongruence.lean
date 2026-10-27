module

import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex
import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Prime.Defs

open MulAction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p a : ℕ} {P : Type*} [Group P] {X : Type*} [MulAction P X]

theorem natCard_orbit_dvd_natCard (x : X) : Nat.card (orbit P x) ∣ Nat.card P :=
  ⟨Nat.card (stabilizer P x), (natCard_orbit_mul_natCard_stabilizer x).symm⟩

theorem exists_natCard_orbit_eq_pow (hp : p.Prime) (hP : Nat.card P = p ^ a) (x : X) :
    ∃ b ≤ a, Nat.card (orbit P x) = p ^ b :=
  (Nat.dvd_prime_pow hp).mp (hP ▸ natCard_orbit_dvd_natCard x)

theorem natCard_fixedPoints_le [Finite X] : Nat.card (fixedPoints P X) ≤ Nat.card X :=
  Nat.card_le_card_of_injective _ Subtype.val_injective

variable [Fact p.Prime]

theorem natCard_modEq_natCard_fixedPoints (hP : Nat.card P = p ^ a) [Finite X] :
    Nat.card X ≡ Nat.card (fixedPoints P X) [MOD p] :=
  (IsPGroup.of_card hP).card_modEq_card_fixedPoints X

theorem dvd_natCard_sub_natCard_fixedPoints (hP : Nat.card P = p ^ a) [Finite X] :
    p ∣ Nat.card X - Nat.card (fixedPoints P X) :=
  (Nat.modEq_iff_dvd' natCard_fixedPoints_le).mp
    (natCard_modEq_natCard_fixedPoints hP).symm

theorem nonempty_fixedPoints_of_not_dvd_natCard (hP : Nat.card P = p ^ a)
    (hX : ¬ p ∣ Nat.card X) : (fixedPoints P X).Nonempty :=
  (IsPGroup.of_card hP).nonempty_fixed_point_of_prime_not_dvd_card X hX

end

end CFSG.FeitThompson
