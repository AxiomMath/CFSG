module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E6Low

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Timmesfeld.ExceptionalOrders

theorem e8Chain_tail_check : chainCheck e8Chain.tail 127 = true := by
  have h := e8Chain_check
  change (_ && _ && chainCheck e8Chain.tail 127) = true at h
  exact (Bool.and_eq_true_iff.1 h).2

theorem maskSet_E8_ne_univ : (maskSet .E8 127 : Set (Fin Tag.E8.rank)) ≠ Set.univ := by
  intro h
  have h7 : (⟨7, by decide⟩ : Fin Tag.E8.rank) ∈ (maskSet .E8 127 : Set (Fin Tag.E8.rank)) := by
    rw [h]
    exact Set.mem_univ _
  exact absurd (mem_maskSet.1 (Finset.mem_coe.1 h7)) (by decide)

theorem not_dvd_240 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ¬ p ∣ 240 := by
  intro h
  have h2 : p ∣ 2 ^ 4 * 3 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem not_dvd_index_E8_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hq : 1 ≤ q)
    (h : p ∣ q - 1) : ¬ p ∣ geomSum 24 1 q * geomSum 2 10 q * geomSum 5 6 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hq1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast at h0
  rw [geomSum_cast_of_cast_eq_one 24 1 q hq1, geomSum_cast_of_cast_eq_one 2 10 q hq1,
    geomSum_cast_of_cast_eq_one 5 6 q hq1] at h0
  have h240 : ((240 : ℕ) : ZMod p) = 0 := by
    push_cast at h0 ⊢
    linear_combination h0
  exact not_dvd_240 hp hp7 ((ZMod.natCast_eq_zero_iff 240 p).1 h240)

section Index


theorem parabolicSum_E8_univ [Fintype (WeylGroup .E8)] (q : ℕ) :
    parabolicSum .E8 Set.univ q = parabolicSum .E8 (maskSet .E8 127) q *
      (geomSum 24 1 q * geomSum 2 10 q * geomSum 5 6 q) := by
  have h255 := parabolicSum_eq_of_chainCheck q _ _ e8Chain_check
  have h127 := parabolicSum_eq_of_chainCheck q _ _ e8Chain_tail_check
  rw [maskSet_full (m := 255) (by decide)] at h255
  rw [h255, h127]
  simp only [e8Chain, ChainStep.value, List.tail_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  ring

end Index

section RelIndex

variable {K : Type} [Field K] [Finite K]

theorem relIndex_parabolicSubgroup_E8 [Fintype (WeylGroup .E8)] :
    (parabolicSubgroup .E8 K (maskSet .E8 127)).relIndex (adjointGroup .E8 K) =
      geomSum 24 1 (Nat.card K) * geomSum 2 10 (Nat.card K) * geomSum 5 6 (Nat.card K) := by
  have h := parabolicSum_univ_eq_mul_index (τ := .E8) (K := K) (maskSet .E8 127)
  rw [parabolicSum_E8_univ] at h
  exact (Nat.eq_of_mul_eq_mul_left (parabolicSum_pos _ Nat.card_pos) h).symm

end RelIndex

section Certified


set_option maxHeartbeats 800000 in
theorem normalizesRSubgroup_E8_of_dvd_sub_one (q : PrimePower)
    (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ q.card - 1) {E : Subgroup (MulAut (Cat ⟨.E8 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.E8 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.E8 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (WeylGroup .E8) := Fintype.ofFinite _
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hidx : ¬ p ∣
      (parabolicSubgroup .E8 K (maskSet .E8 127)).relIndex (adjointGroup .E8 K) := by
    rw [relIndex_parabolicSubgroup_E8, hK]
    exact not_dvd_index_E8_of_dvd_sub_one hp hp7 (by
      rw [PrimePower.card_def]
      exact Nat.one_le_pow _ _ q.prime_p.pos) hpq
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr maskSet_E8_ne_univ hidx hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

theorem seitzExcHighE8One_of_ge_seven :
    SeitzExcHighForAt IsE8Index
      (fun d p => ClassRange LieTypeIndex.E8 (fun _ => True) 1 d p ∧ 7 ≤ p) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨⟨-, q, hdq, -, hord⟩, hp7⟩, hr, hn⟩
  obtain rfl : d = .E8 q := hdq
  refine absurd (normalizesRSubgroup_E8_of_dvd_sub_one q hv hp hp7
    (dvd_sub_one_of_orderOf_eq_one ?_ hord) (IsPGroup.of_card hc) hin) hn
  rw [PrimePower.card_def]
  exact Nat.one_le_pow _ _ q.prime_p.pos

end Certified

end CFSG.LieType.SeitzGeneration.ExcHigh
