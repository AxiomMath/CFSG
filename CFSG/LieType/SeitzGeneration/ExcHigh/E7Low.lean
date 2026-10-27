module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E6Low

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Timmesfeld.ExceptionalOrders

theorem geomSum_cast_two_five_of_cube {R : Type*} [CommRing R] (q : ℕ) (h : (q : R) ^ 3 = 1) :
    ((geomSum 2 5 q : ℕ) : R) = 1 + (q : R) ^ 2 := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination (q : R) ^ 2 * h

theorem geomSum_cast_two_nine_of_cube {R : Type*} [CommRing R] (q : ℕ) (h : (q : R) ^ 3 = 1) :
    ((geomSum 2 9 q : ℕ) : R) = 2 := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination ((q : R) ^ 6 + (q : R) ^ 3 + 1) * h

theorem geomSum_cast_fourteen_of_cube {R : Type*} [CommRing R] (q : ℕ) (h : (q : R) ^ 3 = 1)
    (h1 : 1 + (q : R) + (q : R) ^ 2 = 0) : ((geomSum 14 1 q : ℕ) : R) = 1 + (q : R) := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination (1 + (q : R) ^ 3 + (q : R) ^ 6 + (q : R) ^ 9) * h1 +
    ((1 + (q : R)) * (1 + (q : R) ^ 3 + (q : R) ^ 6 + (q : R) ^ 9)) * h

theorem one_add_add_sq_eq_zero_of_orderOf_eq_three {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 3) : 1 + (q : ZMod p) + (q : ZMod p) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h3 : (q : ZMod p) ^ 3 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h1 : (q : ZMod p) - 1 ≠ 0 := by
    intro h0
    have h1 : (q : ZMod p) = 1 := sub_eq_zero.1 h0
    rw [h1, orderOf_one] at h
    norm_num at h
  have hm : ((q : ZMod p) - 1) * (1 + (q : ZMod p) + (q : ZMod p) ^ 2) = 0 := by
    linear_combination h3
  exact (mul_eq_zero.1 hm).resolve_left h1

theorem not_dvd_index_E7_of_orderOf_eq_three {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : orderOf ((q : ℕ) : ZMod p) = 3) :
    ¬ p ∣ geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have h3 : (q : ZMod p) ^ 3 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h1 := one_add_add_sq_eq_zero_of_orderOf_eq_three hp h
  have h0 : (2 : ZMod p) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hd
    push_cast at this
    rw [geomSum_cast_two_five_of_cube q h3, geomSum_cast_two_nine_of_cube q h3,
      geomSum_cast_fourteen_of_cube q h3 h1] at this
    linear_combination this - 2 * h3 - 2 * h1
  have h2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h0)
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_dvd_56 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≠ 7) : ¬ p ∣ 56 := by
  intro h
  have h' : p ∣ 2 ^ 3 * 7 := by
    norm_num
    exact h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h2)

theorem not_dvd_index_E7_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≠ 7)
    (hq : 1 ≤ q) (h : p ∣ q - 1) :
    ¬ p ∣ geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hq1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast at h0
  rw [geomSum_cast_of_cast_eq_one 2 5 q hq1, geomSum_cast_of_cast_eq_one 2 9 q hq1,
    geomSum_cast_of_cast_eq_one 14 1 q hq1] at h0
  have h56 : ((56 : ℕ) : ZMod p) = 0 := by
    push_cast at h0 ⊢
    linear_combination h0
  exact not_dvd_56 hp hp5 hp7 ((ZMod.natCast_eq_zero_iff 56 p).1 h56)

section Certified


theorem normalizesRSubgroup_E7_of_not_dvd_index (q : PrimePower)
    (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ geomSum 2 5 q.card * geomSum 2 9 q.card * geomSum 14 1 q.card)
    {E : Subgroup (MulAut (Cat ⟨.E7 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.E7 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.E7 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hidx' : ¬ p ∣ (parabolicSubgroup .E7 K (maskSet .E7 63)).relIndex (adjointGroup .E7 K) := by
    rw [relIndex_parabolicSubgroup_E7, hK]
    exact hidx
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr maskSet_E7_ne_univ hidx' hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

theorem seitzExcHighE7Three : SeitzExcHighE7Three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hp5, q, hdq, -, hord⟩, hr, hn⟩
  obtain rfl : d = .E7 q := hdq
  exact absurd (normalizesRSubgroup_E7_of_not_dvd_index q hv hp
    (not_dvd_index_E7_of_orderOf_eq_three hp hp5 hord) (IsPGroup.of_card hc) hin) hn

theorem seitzExcHighE7One_of_ne_seven : SeitzExcHighForAt IsE7Index fun d p => ClassRange LieTypeIndex.E7 (fun _ => True) 1 d p ∧ p ≠ 7 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨⟨hp5, q, hdq, -, hord⟩, hp7⟩, hr, hn⟩
  obtain rfl : d = .E7 q := hdq
  have hq : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  exact absurd (normalizesRSubgroup_E7_of_not_dvd_index q hv hp
    (not_dvd_index_E7_of_dvd_sub_one hp hp5 hp7 hq (dvd_sub_one_of_orderOf_eq_one hq hord))
    (IsPGroup.of_card hc) hin) hn

end Certified

end CFSG.LieType.SeitzGeneration.ExcHigh
