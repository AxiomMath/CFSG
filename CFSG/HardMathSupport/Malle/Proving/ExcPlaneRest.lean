module

public import CFSG.HardMathSupport.Malle.SeitzCube.E7High
public import CFSG.HardMathSupport.Malle.SeitzCube.E8High

public section

namespace CFSG.HardMathSupport.Malle.Proving

open CFSG.LieType.SeitzGeneration

theorem excRest_dvd_sq_sub_one {p q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) ∣ 2) : p ∣ q ^ 2 - 1 := by
  have hsq : ((q : ℕ) : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow,
    Nat.cast_one, hsq, sub_self]

theorem excRest_dvd_sq_sub_one_of_order {p q e : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) = e) (he : e ∣ 2) : p ∣ q ^ 2 - 1 :=
  excRest_dvd_sq_sub_one hq (by rw [h]; exact he)

theorem excRest_dvd_three {p q : ℕ} (hp : p.Prime) (h : orderOf ((q : ℕ) : ZMod p) = 3) :
    p ∣ q ^ 2 + q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := ((q : ℕ) : ZMod p) with hx
  have hpow : ∀ k, orderOf x = k → x ^ k = 1 := fun k hk => hk ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at h; omega
  have h0 : (x - 1) * (x ^ 2 + x + 1) = 0 := by
    rw [show (x - 1) * (x ^ 2 + x + 1) = x ^ 3 - 1 by ring, hpow 3 h, sub_self]
  have hpoly : x ^ 2 + x + 1 = 0 := (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hx1)
  refine (ZMod.natCast_eq_zero_iff _ p).1 ?_
  push_cast
  rw [← hx]
  exact hpoly

theorem excRest_dvd_four {p q : ℕ} (hp : p.Prime) (h : orderOf ((q : ℕ) : ZMod p) = 4) :
    p ∣ q ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := ((q : ℕ) : ZMod p) with hx
  have hpow : ∀ k, orderOf x = k → x ^ k = 1 := fun k hk => hk ▸ pow_orderOf_eq_one x
  have h4 : x ^ 4 = 1 := hpow 4 h
  have hsq : x ^ 2 ≠ 1 := fun h2 => by
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h] at this
    norm_num at this
  have h0 : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
    rw [show (x ^ 2 - 1) * (x ^ 2 + 1) = x ^ 4 - 1 by ring, h4, sub_self]
  have hpoly : x ^ 2 + 1 = 0 := (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hsq)
  refine (ZMod.natCast_eq_zero_iff _ p).1 ?_
  push_cast
  rw [← hx]
  exact hpoly

theorem excRest_dvd_six {p q : ℕ} (hp : p.Prime) (h : orderOf ((q : ℕ) : ZMod p) = 6) :
    p ∣ q ^ 2 - q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := ((q : ℕ) : ZMod p) with hx
  have hpow : ∀ k, orderOf x = k → x ^ k = 1 := fun k hk => hk ▸ pow_orderOf_eq_one x
  have h6 : x ^ 6 = 1 := hpow 6 h
  have hx3 : x ^ 3 ≠ 1 := fun h3 => by
    have := orderOf_dvd_of_pow_eq_one h3
    rw [h] at this
    norm_num at this
  have hsq : x ^ 2 ≠ 1 := fun h2 => by
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h] at this
    norm_num at this
  have hxm : x + 1 ≠ 0 := fun h1 => hsq (by
    have h2 : x ^ 2 - 1 = (x + 1) * (x - 1) := by ring
    rwa [h1, zero_mul, sub_eq_zero] at h2)
  have h0 : (x ^ 3 - 1) * ((x + 1) * (x ^ 2 - x + 1)) = 0 := by
    rw [show (x ^ 3 - 1) * ((x + 1) * (x ^ 2 - x + 1)) = x ^ 6 - 1 by ring, h6, sub_self]
  have hpoly : x ^ 2 - x + 1 = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hx3))).resolve_left hxm
  refine (ZMod.natCast_eq_zero_iff _ p).1 ?_
  rw [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q), Nat.cast_pow, Nat.cast_one,
    ← hx]
  exact hpoly

theorem excRest_orderOf_E6 {e : ℕ} (h : 3 ≤ degCount .E6 e) : e = 1 ∨ e = 2 ∨ e = 3 := by
  have h30 : e ≤ 30 := le_thirty_of_degCount_pos (Or.inr (Or.inl rfl)) (by omega)
  interval_cases e <;> first | decide | (exfalso; revert h; decide)


theorem excRest_rankLE2_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p)
    (h1 : ¬ p ∣ q.card ^ 2 - 1) (h2 : ¬ p ∣ q.card ^ 2 + q.card + 1)
    (h3 : ¬ p ∣ q.card ^ 2 + 1) (h4 : ¬ p ∣ q.card ^ 2 - q.card + 1) :
    RankLE2 p (Cat ⟨.E8 q, hv⟩) := by
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hcnt : degCount .E8 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 2 := by
    by_contra hlt
    rcases CFSG.HardMathSupport.Malle.SeitzCube.orderOf_eq_E8
        (show 3 ≤ degCount .E8 (orderOf ((q.card : ℕ) : ZMod p)) by omega) with h | h | h | h | h
    · exact h1 (excRest_dvd_sq_sub_one_of_order hq1 h (by norm_num))
    · exact h1 (excRest_dvd_sq_sub_one_of_order hq1 h (by norm_num))
    · exact h2 (excRest_dvd_three hp h)
    · exact h3 (excRest_dvd_four hp h)
    · exact h4 (excRest_dvd_six hp h)
  rcases (show degCount .E8 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 ∨
      degCount .E8 (orderOf ((q.card : ℕ) : ZMod p)) = 2 by omega) with h | h
  · exact (rankLE1_cat_E8 q hv hp hpq h).rankLE2
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_E8 q hv hp h

theorem excRest_rankLE2_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p)
    (h1 : ¬ p ∣ q.card ^ 2 - 1) (h2 : ¬ p ∣ q.card ^ 2 + q.card + 1)
    (h3 : ¬ p ∣ q.card ^ 2 - q.card + 1) :
    RankLE2 p (Cat ⟨.E7 q, hv⟩) := by
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hcnt : degCount .E7 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 2 := by
    by_contra hlt
    rcases CFSG.HardMathSupport.Malle.SeitzCube.orderOf_eq_E7
        (show 3 ≤ degCount .E7 (orderOf ((q.card : ℕ) : ZMod p)) by omega) with h | h | h | h
    · exact h1 (excRest_dvd_sq_sub_one_of_order hq1 h (by norm_num))
    · exact h1 (excRest_dvd_sq_sub_one_of_order hq1 h (by norm_num))
    · exact h2 (excRest_dvd_three hp h)
    · exact h3 (excRest_dvd_six hp h)
  rcases (show degCount .E7 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 ∨
      degCount .E7 (orderOf ((q.card : ℕ) : ZMod p)) = 2 by omega) with h | h
  · exact (rankLE1_cat_E7 q hv hp hpq h).rankLE2
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_E7 q hv hp h

theorem excRest_rankLE2_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q.p)
    (h1 : ¬ p ∣ q.card ^ 2 - 1) (h2 : ¬ p ∣ q.card ^ 2 + q.card + 1) :
    RankLE2 p (Cat ⟨.E6 q, hv⟩) := by
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hcnt : degCount .E6 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 2 := by
    by_contra hlt
    rcases excRest_orderOf_E6
        (show 3 ≤ degCount .E6 (orderOf ((q.card : ℕ) : ZMod p)) by omega) with h | h | h
    · exact h1 (excRest_dvd_sq_sub_one_of_order hq1 h (by norm_num))
    · exact h1 (excRest_dvd_sq_sub_one_of_order hq1 h (by norm_num))
    · exact h2 (excRest_dvd_three hp h)
  rcases (show degCount .E6 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 ∨
      degCount .E6 (orderOf ((q.card : ℕ) : ZMod p)) = 2 by omega) with h | h
  · exact (rankLE1_cat_E6 q hv hp hpq h).rankLE2
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_E6 q hv hp h

theorem excPlaneE8Rest_proved : CFSG.LieType.SeitzGeneration.ExcPlaneE8Rest := by
  unfold CFSG.LieType.SeitzGeneration.ExcPlaneE8Rest CFSG.LieType.SeitzGeneration.ExcParabolicPlaneOn
  intro d p hp _ hpd _ hS hr
  rcases d with ⟨τ, hv⟩
  obtain ⟨q, hd, h1, h2, h3, h4⟩ := hS
  have hd' : τ = .E8 q := hd
  subst hd'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (TauCeti.LieTypeIndex.characteristic_E8 q).symm)
  exact (hr (excRest_rankLE2_E8 q hv hp hpq h1 h2 h3 h4)).elim

theorem excPlaneE7Rest_proved : CFSG.LieType.SeitzGeneration.ExcPlaneE7Rest := by
  unfold CFSG.LieType.SeitzGeneration.ExcPlaneE7Rest CFSG.LieType.SeitzGeneration.ExcParabolicPlaneOn
  intro d p hp _ hpd _ hS hr
  rcases d with ⟨τ, hv⟩
  obtain ⟨q, hd, h1, h2, h3⟩ := hS
  have hd' : τ = .E7 q := hd
  subst hd'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (TauCeti.LieTypeIndex.characteristic_E7 q).symm)
  exact (hr (excRest_rankLE2_E7 q hv hp hpq h1 h2 h3)).elim

theorem excPlaneE6Rest_proved : CFSG.LieType.SeitzGeneration.ExcPlaneE6Rest := by
  unfold CFSG.LieType.SeitzGeneration.ExcPlaneE6Rest CFSG.LieType.SeitzGeneration.ExcParabolicPlaneOn
  intro d p hp _ hpd _ hS hr
  rcases d with ⟨τ, hv⟩
  obtain ⟨q, hd, h1, h2⟩ := hS
  have hd' : τ = .E6 q := hd
  subst hd'
  have hpq : p ≠ q.p := fun h => hpd (h.trans (TauCeti.LieTypeIndex.characteristic_E6 q).symm)
  exact (hr (excRest_rankLE2_E6 q hv hp hpq h1 h2)).elim

end CFSG.HardMathSupport.Malle.Proving

end
