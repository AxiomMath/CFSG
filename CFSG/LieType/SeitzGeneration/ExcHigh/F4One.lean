module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E6Low
public import CFSG.LieType.SeitzGeneration.ExcHigh.F4Two

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Timmesfeld.ExceptionalOrders

theorem not_dvd_1152 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 1152 := by
  intro h
  have h2 : p ∣ 2 ^ 7 * 3 ^ 2 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega

theorem not_dvd_sumLength_F4_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (h : p ∣ q - 1) :
    ¬ p ∣ geomSum 2 1 q * geomSum 3 1 q * (geomSum 4 1 q * geomSum 2 3 q) *
        (geomSum 8 1 q * geomSum 3 4 q) := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hq1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast at h0
  rw [geomSum_cast_of_cast_eq_one 2 1 q hq1, geomSum_cast_of_cast_eq_one 3 1 q hq1,
    geomSum_cast_of_cast_eq_one 4 1 q hq1, geomSum_cast_of_cast_eq_one 2 3 q hq1,
    geomSum_cast_of_cast_eq_one 8 1 q hq1, geomSum_cast_of_cast_eq_one 3 4 q hq1] at h0
  have h1152 : ((1152 : ℕ) : ZMod p) = 0 := by
    push_cast at h0 ⊢
    linear_combination h0
  exact not_dvd_1152 hp hp5 ((ZMod.natCast_eq_zero_iff 1152 p).1 h1152)

section Certified


theorem relIndex_borel_F4 {K : Type} [Field K] [Finite K] [Fintype (WeylGroup .F4)] :
    (parabolicSubgroup .F4 K (∅ : Set (Fin Tag.F4.rank))).relIndex (adjointGroup .F4 K) =
      geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
        (geomSum 4 1 (Nat.card K) * geomSum 2 3 (Nat.card K)) *
          (geomSum 8 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) := by
  have h := parabolicSum_univ_eq_mul_index (τ := .F4) (K := K) (∅ : Set (Fin Tag.F4.rank))
  rw [parabolicSum_empty, one_mul, parabolicSum_univ, sum_length_F4] at h
  exact h.symm

theorem normalizesRSubgroup_F4_of_dvd_sub_one (q : PrimePower)
    (hv : (LieTypeIndex.F4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q.card - 1) {E : Subgroup (MulAut (Cat ⟨.F4 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.F4 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.F4 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hJ : (∅ : Set (Fin Tag.F4.rank)) ≠ Set.univ := by
    intro h
    have : (0 : Fin Tag.F4.rank) ∈ (∅ : Set (Fin Tag.F4.rank)) := by rw [h]; trivial
    exact this
  have hidx : ¬ p ∣ (parabolicSubgroup .F4 K (∅ : Set (Fin Tag.F4.rank))).relIndex
      (adjointGroup .F4 K) := by
    rw [relIndex_borel_F4, hK]
    exact not_dvd_sumLength_F4_of_dvd_sub_one hp hp5 (by
      rw [PrimePower.card_def]
      exact Nat.one_le_pow _ _ q.prime_p.pos) hpq
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr hJ hidx hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

theorem seitzExcHighF4One : SeitzExcHighF4One := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hp5, q, hdq, -, hord⟩, hr, hn⟩
  obtain rfl : d = .F4 q := hdq
  refine absurd (normalizesRSubgroup_F4_of_dvd_sub_one q hv hp hp5
    (dvd_sub_one_of_orderOf_eq_one ?_ hord) (IsPGroup.of_card hc) hin) hn
  rw [PrimePower.card_def]
  exact Nat.one_le_pow _ _ q.prime_p.pos

theorem seitzExcHighF4_geFive : SeitzExcHighForAt IsF4Index PrimeRange.geFive :=
  seitzExcHighF4_geFive_of_one seitzExcHighF4One

end Certified

end CFSG.LieType.SeitzGeneration.ExcHigh
