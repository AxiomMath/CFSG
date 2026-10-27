module

public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SevenCensus

variable {G : Type*} [Group G]

section Exponents

variable {p₁ p₂ : G} (h₁ : p₁ ^ 7 = 1) (h₂ : p₂ ^ 7 = 1) (hc : Commute p₁ p₂)
include h₁ h₂ hc

theorem pw_mod (a b : ℕ) : p₁ ^ a * p₂ ^ b = p₁ ^ (a % 7) * p₂ ^ (b % 7) := by
  conv_lhs => rw [← Nat.mod_add_div a 7, ← Nat.mod_add_div b 7]
  rw [pow_add, pow_add, pow_mul, pow_mul, h₁, h₂, one_pow, one_pow, mul_one, mul_one]

theorem pw_mul (a b c d : ℕ) :
    p₁ ^ a * p₂ ^ b * (p₁ ^ c * p₂ ^ d) = p₁ ^ (a + c) * p₂ ^ (b + d) := by
  rw [pow_add, pow_add, mul_assoc, ← mul_assoc (p₂ ^ b), ((hc.pow_pow c b).eq).symm]
  group

theorem pw_pow (a b k : ℕ) : (p₁ ^ a * p₂ ^ b) ^ k = p₁ ^ (a * k) * p₂ ^ (b * k) := by
  rw [(hc.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul]

end Exponents

theorem card_sup_of_le_normalizer {H N : Subgroup G}
    (hle : H ≤ Subgroup.normalizer (N : Set G)) (hd : H ⊓ N = ⊥) :
    Nat.card (H ⊔ N : Subgroup G) = Nat.card H * Nat.card N := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H N hle
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : H × N => (⟨(p.1 : G) * p.2, by
    rw [← SetLike.mem_coe, hset]; exact Set.mul_mem_mul p.1.2 p.2.2⟩ : ↥(H ⊔ N))) ⟨?_, ?_⟩)
  · rintro ⟨h, n⟩ ⟨h', n'⟩ heq
    have heq' : (h : G) * n = h' * n' := congrArg Subtype.val heq
    have hmem : (h' : G)⁻¹ * h ∈ H ⊓ N := by
      refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem h'.2) h.2, ?_⟩
      have : (h' : G)⁻¹ * h = n' * (n : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
      rw [this]
      exact N.mul_mem n'.2 (N.inv_mem n.2)
    rw [hd, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hh : h = h' := Subtype.ext hmem.symm
    subst hh
    have hn : (n : G) = n' := mul_left_cancel heq'
    exact Prod.ext rfl (Subtype.ext hn)
  · rintro ⟨z, hz⟩
    rw [← SetLike.mem_coe, hset] at hz
    obtain ⟨h, hh, n, hn, rfl⟩ := hz
    exact ⟨(⟨h, hh⟩, ⟨n, hn⟩), rfl⟩

variable [Finite G]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SevenCensus
