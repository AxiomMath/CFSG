module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bProduct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bNormalizer

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K]

theorem ne_three_of_orderOf_two {ℓ : ℕ} (hf : 1 ≤ f) (hord : orderOf (2 : ZMod ℓ) = 6 * f) :
    ℓ ≠ 3 := by
  rintro rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h20 : (2 : ZMod 3) ≠ 0 := by
    intro h0
    have h2d : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp (by exact_mod_cast h0)
    omega
  have h4 : orderOf (2 : ZMod 3) ∣ 3 - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h20)
  rw [hord] at h4
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem threeInvolutionProduct_holds : ThreeInvolutionProduct := by
  intro f hf K _ h ℓ hℓ hℓ2 _ hord
  exact exists_three_involutions hf h hℓ hord

end CFSG.QuasithinUnique.Setup.X5
