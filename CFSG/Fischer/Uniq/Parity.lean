module

public import CFSG.Fischer.Uniq.F23Local

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {Y : Type} [Group Y] {F : Set Y}

theorem exists_fixed_of_odd {α : Type*} [Finite α] (hodd : Odd (Nat.card α)) (g : Equiv.Perm α)
    (hg : ∀ x, g (g x) = x) : ∃ x, g x = x := by
  classical
  have := Fintype.ofFinite α
  by_contra h
  push Not at h
  have hσ : g ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two, hg x]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) hσ
  have hsupp : (Equiv.Perm.support g)ᶜ = ∅ := by
    ext x
    simp [Equiv.Perm.mem_support, h x]
  rw [hsupp, Finset.card_empty] at this
  rw [Nat.card_eq_fintype_card] at hodd
  obtain ⟨k, hk⟩ := hodd
  rw [hk] at this
  unfold Nat.ModEq at this
  omega

theorem hasFixedPointProperty_of_odd (hF : Pair Y F) (hodd : Odd (Nat.card F)) :
    HasFixedPointProperty hF := by
  have := Pair.finite hF
  exact fun g hg _ _ => exists_fixed_of_odd hodd g hg

end CFSG.Fischer
