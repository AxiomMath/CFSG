module

public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Timmesfeld.ExceptionalOrders

theorem sq_eq_one_zmod_of_dvd_sq_sub_one {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q ^ 2 - 1) :
    (q : ZMod p) ^ 2 = 1 := by
  have := (ZMod.natCast_eq_zero_iff (q ^ 2 - 1) p).2 h
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
  exact this

theorem geomSum_cast_of_cast_eq_one {R : Type*} [CommRing R] (n s q : ℕ) (h : (q : R) = 1) :
    ((geomSum n s q : ℕ) : R) = n := by
  simp [geomSum, h]

theorem geomSum_cast_nine_of_sq_eq_one {R : Type*} [CommRing R] (q : ℕ) (h : (q : R) ^ 2 = 1) :
    ((geomSum 9 1 q : ℕ) : R) = 5 + 4 * q := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination (((4 : R) + 3 * (q : R) ^ 2 + 2 * (q : R) ^ 4 + (q : R) ^ 6) +
    (q : R) * (3 + 2 * (q : R) ^ 2 + (q : R) ^ 4)) * h

theorem geomSum_cast_three_four_of_sq_eq_one {R : Type*} [CommRing R] (q : ℕ)
    (h : (q : R) ^ 2 = 1) : ((geomSum 3 4 q : ℕ) : R) = 3 := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination ((2 : R) + 2 * (q : R) ^ 2 + (q : R) ^ 4 + (q : R) ^ 6) * h

theorem not_dvd_index_E6_of_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (h : p ∣ q ^ 2 - 1) : ¬ p ∣ geomSum 9 1 q * geomSum 3 4 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hx := sq_eq_one_zmod_of_dvd_sq_sub_one hq h
  have h0 : (3 : ZMod p) * (5 + 4 * (q : ZMod p)) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hd
    push_cast at this
    rw [geomSum_cast_nine_of_sq_eq_one q hx, geomSum_cast_three_four_of_sq_eq_one q hx] at this
    linear_combination this
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h3
    have : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h3)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h1 : 5 + 4 * (q : ZMod p) = 0 := (mul_eq_zero.1 h0).resolve_left h3
  have h9 : (9 : ZMod p) = 0 ∨ (1 : ZMod p) = 0 := by
    have hq1 : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.1 hq1 with h | h
    · left
      linear_combination h1 - 4 * h
    · right
      linear_combination h1 - 4 * h
  rcases h9 with h9 | h9
  · have h9' : p ∣ 3 ^ 2 := by
      norm_num
      exact (ZMod.natCast_eq_zero_iff 9 p).1 (by exact_mod_cast h9)
    have h3p : p ∣ 3 := hp.dvd_of_dvd_pow h9'
    have := Nat.le_of_dvd (by norm_num) h3p
    omega
  · exact one_ne_zero h9

theorem dvd_sq_sub_one_of_orderOf_dvd_two {p q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) ∣ 2) : p ∣ q ^ 2 - 1 := by
  have hsq : ((q : ℕ) : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow,
    Nat.cast_one, hsq, sub_self]

section Certified


set_option maxHeartbeats 800000 in
theorem normalizesRSubgroup_E6_of_dvd_sq_sub_one (q : PrimePower)
    (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q.card ^ 2 - 1) {E : Subgroup (MulAut (Cat ⟨.E6 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.E6 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.E6 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hidx : ¬ p ∣ (parabolicSubgroup .E6 K (maskSet .E6 31)).relIndex (adjointGroup .E6 K) := by
    rw [relIndex_parabolicSubgroup_E6, hK]
    exact not_dvd_index_E6_of_dvd_sq_sub_one hp hp5 (by
      rw [PrimePower.card_def]
      exact Nat.one_le_pow _ _ q.prime_p.pos) hpq
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr maskSet_E6_ne_univ hidx hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

theorem seitzExcHighE6_of_orderOf_dvd_two (e : ℕ) (he : e ∣ 2) :
    SeitzExcHighClass IsE6Index LieTypeIndex.E6 e := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hp5, q, hdq, -, hord⟩, hr, hn⟩
  obtain rfl : d = .E6 q := hdq
  refine absurd (normalizesRSubgroup_E6_of_dvd_sq_sub_one q hv hp hp5
    (dvd_sq_sub_one_of_orderOf_dvd_two ?_ (hord ▸ he)) (IsPGroup.of_card hc) hin) hn
  rw [PrimePower.card_def]
  exact Nat.one_le_pow _ _ q.prime_p.pos

theorem seitzExcHighE6One : SeitzExcHighE6One :=
  seitzExcHighE6_of_orderOf_dvd_two 1 (one_dvd 2)

theorem seitzExcHighE6Two : SeitzExcHighE6Two :=
  seitzExcHighE6_of_orderOf_dvd_two 2 dvd_rfl

theorem seitzExcHighE6_geFive_of_three (h3 : SeitzExcHighE6Three) :
    SeitzExcHighForAt IsE6Index PrimeRange.geFive :=
  seitzExcHighE6_geFive_of_classes seitzExcHighE6One seitzExcHighE6Two h3

end Certified

end CFSG.LieType.SeitzGeneration.ExcHigh
