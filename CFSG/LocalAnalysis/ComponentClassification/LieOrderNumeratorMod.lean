module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG.Assembly.LowTwoRank

theorem lieOrderNumerator_natCast_congr (t : StatedLieTag) (n : ℕ) {m a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (h : (a : ZMod m) = (b : ZMod m)) :
    (lieOrderNumerator t n a : ZMod m) = (lieOrderNumerator t n b : ZMod m) := by
  have ha' : ∀ i : ℕ, ((a ^ i - 1 : ℕ) : ZMod m) = (a : ZMod m) ^ i - 1 := by
    intro i
    rw [Nat.cast_sub (Nat.one_le_pow i a ha), Nat.cast_pow, Nat.cast_one]
  have hb' : ∀ i : ℕ, ((b ^ i - 1 : ℕ) : ZMod m) = (b : ZMod m) ^ i - 1 := by
    intro i
    rw [Nat.cast_sub (Nat.one_le_pow i b hb), Nat.cast_pow, Nat.cast_one]
  have ha1 : ((a - 1 : ℕ) : ZMod m) = (a : ZMod m) - 1 := by
    rw [Nat.cast_sub ha, Nat.cast_one]
  have hb1 : ((b - 1 : ℕ) : ZMod m) = (b : ZMod m) - 1 := by
    rw [Nat.cast_sub hb, Nat.cast_one]
  cases t <;>
    simp only [lieOrderNumerator, ha', hb', ha1, hb1, h, Nat.cast_pow, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ite, Nat.cast_prod, Nat.cast_ofNat, Nat.cast_one]

theorem lieOrderNumerator_pow_natCast_zmod_eq (t : StatedLieTag) (n : ℕ) {p ℓ f : ℕ}
    (hp : p.Prime) (hℓ : 1 ≤ ℓ) (hpf : p ∣ f) :
    (lieOrderNumerator t n (ℓ ^ f) : ZMod p) =
      (lieOrderNumerator t n (ℓ ^ (f / p)) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  have h : ((ℓ ^ f : ℕ) : ZMod p) = ((ℓ ^ (f / p) : ℕ) : ZMod p) := by
    rw [hq, Nat.cast_pow, ZMod.pow_card]
  exact lieOrderNumerator_natCast_congr t n (Nat.one_le_pow f ℓ hℓ)
    (Nat.one_le_pow (f / p) ℓ hℓ) h

theorem prime_dvd_lieOrderNumerator_pow_iff (t : StatedLieTag) (n : ℕ) {p ℓ f : ℕ}
    (hp : p.Prime) (hℓ : 1 ≤ ℓ) (hpf : p ∣ f) :
    p ∣ lieOrderNumerator t n (ℓ ^ f) ↔ p ∣ lieOrderNumerator t n (ℓ ^ (f / p)) := by
  rw [← ZMod.natCast_eq_zero_iff (lieOrderNumerator t n (ℓ ^ f)) p,
    ← ZMod.natCast_eq_zero_iff (lieOrderNumerator t n (ℓ ^ (f / p))) p,
    lieOrderNumerator_pow_natCast_zmod_eq t n hp hℓ hpf]

end CFSG.ComponentClassification.CatLeaf
