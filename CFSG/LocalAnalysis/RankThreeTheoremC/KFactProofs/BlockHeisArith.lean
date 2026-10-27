module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem heis_sq_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    (p : ℤ) ^ 2 ∣ (c ^ p) ^ (orderOf (((c ^ p : ℤ)) : ZMod p)) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcz : ((c : ℤ) : ZMod p) ≠ 0 := by
    intro h
    exact hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 h)
  have hbc : (((c ^ p : ℤ)) : ZMod p) = (c : ZMod p) := by
    push_cast
    exact ZMod.pow_card _
  rw [hbc]
  set e := orderOf (c : ZMod p) with he
  have hce : (c : ZMod p) ^ e = 1 := pow_orderOf_eq_one _
  have hdvd : (p : ℤ) ∣ c ^ e - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hce, sub_self]
  obtain ⟨t, ht⟩ := hdvd
  have hx : c ^ e = 1 + p * t := by linarith
  have h1 := sq_dvd_add_pow_sub_sub ((p : ℤ) * t) 1 p
  rw [one_pow, one_pow, one_mul, ← hx] at h1
  have h2 : (p : ℤ) ^ 2 ∣ (c ^ e) ^ p - 1 := by
    have h3 : (p : ℤ) ^ 2 ∣ (p * t) ^ 2 := by
      rw [mul_pow]
      exact dvd_mul_right _ _
    have h4 : (p : ℤ) ^ 2 ∣ (p : ℤ) * t * p := ⟨t, by ring⟩
    have h5 := dvd_add (h3.trans h1) h4
    have : (c ^ e) ^ p - 1 = ((c ^ e) ^ p - (p : ℤ) * t * p - 1) + (p : ℤ) * t * p := by ring
    rw [this]
    exact h5
  rw [← pow_mul, mul_comm, pow_mul]
  exact h2

theorem heis_orderOf_pos {p : ℕ} (hp : p.Prime) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    0 < orderOf (((c ^ p : ℤ)) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcz : ((c : ℤ) : ZMod p) ≠ 0 := by
    intro h
    exact hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 h)
  have hbc : (((c ^ p : ℤ)) : ZMod p) = (c : ZMod p) := by
    push_cast
    exact ZMod.pow_card _
  rw [hbc, orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
  exact ⟨p - 1, Nat.sub_pos_of_lt hp.one_lt, ZMod.pow_card_sub_one_eq_one hcz⟩

theorem heis_two_le_padicValNat {p c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c) (hc1 : 2 ≤ c) :
    2 ≤ padicValNat p ((c ^ p) ^ (orderOf (((c ^ p : ℕ)) : ZMod p)) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc' : ¬ (p : ℤ) ∣ (c : ℤ) := by
    intro h
    exact hc (Int.natCast_dvd_natCast.1 h)
  have hcast : (((c ^ p : ℕ)) : ZMod p) = (((c : ℤ) ^ p : ℤ) : ZMod p) := by push_cast; rfl
  have hepos : 0 < orderOf (((c ^ p : ℕ)) : ZMod p) := by
    rw [hcast]
    exact heis_orderOf_pos hp (c : ℤ) hc'
  have hlt : 1 < (c ^ p) ^ (orderOf (((c ^ p : ℕ)) : ZMod p)) := by
    have h1 : 1 < c ^ p := Nat.one_lt_pow hp.ne_zero (by omega)
    exact Nat.one_lt_pow hepos.ne' h1
  have hz := heis_sq_dvd_pow_sub_one hp (c : ℤ) hc'
  rw [← hcast] at hz
  set e := orderOf (((c ^ p : ℕ)) : ZMod p) with he
  have hcastsub : ((((c ^ p) ^ e - 1 : ℕ)) : ℤ) = ((c : ℤ) ^ p) ^ e - 1 := by
    rw [Nat.cast_sub hlt.le]
    push_cast
    rfl
  have hdvd : p ^ 2 ∣ (c ^ p) ^ e - 1 := by
    have h2 : ((p ^ 2 : ℕ) : ℤ) ∣ ((((c ^ p) ^ e - 1 : ℕ)) : ℤ) := by
      rw [hcastsub]
      push_cast
      exact hz
    exact Int.natCast_dvd_natCast.1 h2
  exact (padicValNat_dvd_iff_le (by omega)).1 hdvd

theorem heis_two_le_padicValInt {p : ℕ} (hp : p.Prime) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (hne : (c ^ p) ^ (orderOf (((c ^ p : ℤ)) : ZMod p)) - 1 ≠ 0) :
    2 ≤ padicValInt p ((c ^ p) ^ (orderOf (((c ^ p : ℤ)) : ZMod p)) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz := heis_sq_dvd_pow_sub_one hp c hc
  rw [padicValInt]
  have hn : ((c ^ p) ^ (orderOf (((c ^ p : ℤ)) : ZMod p)) - 1).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.2 hne
  refine (padicValNat_dvd_iff_le hn).1 ?_
  have : ((p : ℤ) ^ 2).natAbs ∣ ((c ^ p) ^ (orderOf (((c ^ p : ℤ)) : ZMod p)) - 1).natAbs :=
    Int.natAbs_dvd_natAbs.2 hz
  simpa [Int.natAbs_pow] using this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
