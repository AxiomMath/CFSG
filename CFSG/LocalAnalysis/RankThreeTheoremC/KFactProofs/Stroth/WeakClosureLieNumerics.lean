module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.CrossNum

@[expose] noncomputable def crossE (p q : ℕ) : ℕ := orderOf (q : ZMod p)

@[expose] noncomputable def crossA (p q : ℕ) : ℕ := padicValNat p (q ^ crossE p q - 1)

theorem crossE_pos {p q : ℕ} [Fact p.Prime] (hpq : ¬ p ∣ q) : 0 < crossE p q := by
  have hq : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).mp h)
  have h1 : (q : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hq
  have h2 : crossE p q ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.mpr h1
  have h3 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rcases Nat.eq_zero_or_pos (crossE p q) with h | h
  · rw [h, zero_dvd_iff] at h2
    omega
  · exact h

theorem dvd_pow_sub_one_iff {p q m : ℕ} [Fact p.Prime] (hpq : ¬ p ∣ q) :
    p ∣ q ^ m - 1 ↔ crossE p q ∣ m := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact hpq (dvd_zero p))
  have hq1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq0
  have hcast : ((q ^ m - 1 : ℕ) : ZMod p) = (q : ZMod p) ^ m - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
  rw [crossE, orderOf_dvd_iff_pow_eq_one, ← sub_eq_zero, ← hcast, ZMod.natCast_eq_zero_iff]

theorem dvd_pow_crossE_sub_one {p q : ℕ} [Fact p.Prime] (hpq : ¬ p ∣ q) :
    p ∣ q ^ crossE p q - 1 :=
  (dvd_pow_sub_one_iff hpq).mpr dvd_rfl

theorem one_le_crossA {p q : ℕ} [Fact p.Prime] (hpq : ¬ p ∣ q) (hq : 1 < q) : 1 ≤ crossA p q := by
  have hlt : 1 < q ^ crossE p q := Nat.one_lt_pow (crossE_pos hpq).ne' hq
  exact one_le_padicValNat_of_dvd (Nat.sub_ne_zero_of_lt hlt) (dvd_pow_crossE_sub_one hpq)

theorem pow_crossA_dvd {p q : ℕ} [Fact p.Prime] (hpq : ¬ p ∣ q) :
    p ^ crossA p q ∣ q ^ crossE p q - 1 :=
  pow_padicValNat_dvd

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.CrossNum
