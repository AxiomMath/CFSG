module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.HSp4A

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V] [Finite V]

theorem orderOf_two_dvd_rk_of_inf_fixV_eq_bot {p : ℕ} [Fact p.Prime]
    (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)} (hY : IsPGroup p Y)
    {W : Subgroup V} (hW : ∀ y ∈ Y, ∀ w ∈ W, y w ∈ W)
    (hfix : W ⊓ fixV Y = ⊥) :
    orderOf (2 : ZMod p) ∣ rk W := by
  have hmod := CFSG.Quasithin.H.Sp4.card_modEq_card_inf_fixV hY hW
  rw [hfix] at hmod
  rw [show Nat.card ↥(⊥ : Subgroup V) = 1 by simp] at hmod
  rw [card_eq_two_pow hV W] at hmod
  have h2 : (2 : ZMod p) ^ rk W = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (2 ^ rk W) 1 p).2 hmod
    simpa using this
  exact orderOf_dvd_of_pow_eq_one h2

theorem prime_dvd_two_pow_sub_one_of_orderOf_dvd {p n : ℕ} [Fact p.Prime]
    (h : orderOf (2 : ZMod p) ∣ n) : p ∣ 2 ^ n - 1 := by
  have h2 : ((2 : ZMod p) ^ n) = 1 := orderOf_dvd_iff_pow_eq_one.1 h
  have hcast : ((2 ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, h2, Nat.cast_one]
  have hmod : 2 ^ n ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff (2 ^ n) 1 p).1 hcast
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow' n 1)).mp hmod.symm

end CFSG.GroupTheory
