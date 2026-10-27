module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.GroupTwoPart

@[expose] noncomputable def value (order : ℕ) : ℕ := 2 ^ order.factorization 2

theorem mul {first second : ℕ} (hfirst : first ≠ 0) (hsecond : second ≠ 0) :
    value (first * second) = value first * value second := by
  unfold value
  rw [Nat.factorization_mul hfirst hsecond, Finsupp.add_apply, pow_add]

theorem mono {first second : ℕ} (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hdivides : first ∣ second) :
    value first ≤ value second := by
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  exact (Nat.factorization_le_iff_dvd hfirst hsecond).mpr hdivides 2

theorem subgroup_le {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G) :
    value (Nat.card subgroup) ≤ value (Nat.card G) :=
  mono (ne_of_gt Nat.card_pos) (ne_of_gt Nat.card_pos) subgroup.card_subgroup_dvd_card

end CFSG.ComponentClassification.GroupTwoPart
