module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Low

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Timmesfeld.ExceptionalOrders

@[expose] def e7A6Cert1 : OrbitCert .E7 where
  lam := 141973095
  pts := [
    159942776, 127436920, 142182520, 143104120, 143161736, 143165321, 143165575]
  parents := [
    6, 21, 36, 51, 66, 80]
  table := [
    281474976710656, 2203335065601, 564062383636482, 847732122255363, 1130315183882244,
    1412894000676870, 1695472800890885]
  lens := [
    0, 1, 2, 3, 4, 5, 6]

@[expose] def e7A6Cert2 : OrbitCert .E7 where
  lam := 126388360
  pts := [
    110659720, 125405320, 126326920, 126384536, 126388121, 126388375]
  parents := [
    5, 20, 35, 50, 64]
  table := [
    1099511627776, 8606777345, 2203368685570, 3311453601795, 4415293685765, 5519117189124]
  lens := [
    0, 1, 2, 3, 4, 5]

@[expose] def e7A6Chain : List (ChainStep .E7) := [
  ⟨125, 61, e7A6Cert1, [(7, 1)]⟩,
  ⟨61, 29, e7A6Cert2, [(6, 1)]⟩,
  ⟨29, 13, e7Cert4, [(5, 1)]⟩,
  ⟨13, 5, e7Cert3, [(4, 1)]⟩,
  ⟨5, 1, e7Cert2, [(3, 1)]⟩,
  ⟨1, 0, e7Cert1, [(2, 1)]⟩]

theorem e7A6Chain_check : chainCheck e7A6Chain 125 = true := by
  decide +kernel

section Index


theorem parabolicSum_E7_A6_univ [Fintype (WeylGroup .E7)] (q : ℕ) :
    parabolicSum .E7 Set.univ q = parabolicSum .E7 (maskSet .E7 125) q *
      (geomSum 2 4 q * geomSum 2 5 q * geomSum 2 7 q * geomSum 4 3 q * geomSum 18 1 q) := by
  have h127 := parabolicSum_eq_of_chainCheck q _ _ e7Chain_check
  have h125 := parabolicSum_eq_of_chainCheck q _ _ e7A6Chain_check
  rw [maskSet_full (m := 127) (by decide)] at h127
  rw [h127, h125]
  simp only [e7Chain, e7A6Chain, ChainStep.value, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

end Index

theorem maskSet_E7_125_ne_univ : (maskSet .E7 125 : Set (Fin Tag.E7.rank)) ≠ Set.univ := by
  intro h
  have h1 : (⟨1, by decide⟩ : Fin Tag.E7.rank) ∈ (maskSet .E7 125 : Set (Fin Tag.E7.rank)) := by
    rw [h]
    exact Set.mem_univ _
  exact absurd (mem_maskSet.1 (Finset.mem_coe.1 h1)) (by decide)

theorem not_dvd_576 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 576 := by
  intro h
  have h' : p ∣ 2 ^ 6 * 3 ^ 2 := by
    norm_num
    exact h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega

theorem not_dvd_index_A6_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (h : p ∣ q - 1) :
    ¬ p ∣ geomSum 2 4 q * geomSum 2 5 q * geomSum 2 7 q * geomSum 4 3 q * geomSum 18 1 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hq1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast at h0
  rw [geomSum_cast_of_cast_eq_one 2 4 q hq1, geomSum_cast_of_cast_eq_one 2 5 q hq1,
    geomSum_cast_of_cast_eq_one 2 7 q hq1, geomSum_cast_of_cast_eq_one 4 3 q hq1,
    geomSum_cast_of_cast_eq_one 18 1 q hq1] at h0
  have h576 : ((576 : ℕ) : ZMod p) = 0 := by
    push_cast at h0 ⊢
    linear_combination h0
  exact not_dvd_576 hp hp5 ((ZMod.natCast_eq_zero_iff 576 p).1 h576)

section RelIndex

variable {K : Type} [Field K] [Finite K]

theorem relIndex_parabolicSubgroup_E7_A6 [Fintype (WeylGroup .E7)] :
    (parabolicSubgroup .E7 K (maskSet .E7 125)).relIndex (adjointGroup .E7 K) =
      geomSum 2 4 (Nat.card K) * geomSum 2 5 (Nat.card K) * geomSum 2 7 (Nat.card K) *
        geomSum 4 3 (Nat.card K) * geomSum 18 1 (Nat.card K) := by
  have h := parabolicSum_univ_eq_mul_index (τ := .E7) (K := K) (maskSet .E7 125)
  rw [parabolicSum_E7_A6_univ] at h
  exact (Nat.eq_of_mul_eq_mul_left (parabolicSum_pos _ Nat.card_pos) h).symm

end RelIndex

section Certified


theorem normalizesRSubgroup_E7_A6_of_not_dvd_index (q : PrimePower)
    (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ geomSum 2 4 q.card * geomSum 2 5 q.card * geomSum 2 7 q.card *
      geomSum 4 3 q.card * geomSum 18 1 q.card)
    {E : Subgroup (MulAut (Cat ⟨.E7 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.E7 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.E7 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hidx' : ¬ p ∣ (parabolicSubgroup .E7 K (maskSet .E7 125)).relIndex (adjointGroup .E7 K) := by
    rw [relIndex_parabolicSubgroup_E7_A6, hK]
    exact hidx
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr maskSet_E7_125_ne_univ hidx' hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

theorem seitzExcHighE7One_seven :
    SeitzExcHighForAt IsE7Index fun d p => ClassRange LieTypeIndex.E7 (fun _ => True) 1 d p ∧
      p = 7 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨⟨hp5, q, hdq, -, hord⟩, -⟩, hr, hn⟩
  obtain rfl : d = .E7 q := hdq
  have hq : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  exact absurd (normalizesRSubgroup_E7_A6_of_not_dvd_index q hv hp
    (not_dvd_index_A6_of_dvd_sub_one hp hp5 hq (dvd_sub_one_of_orderOf_eq_one hq hord))
    (IsPGroup.of_card hc) hin) hn

theorem seitzExcHighE7One : SeitzExcHighE7One :=
  SeitzExcHighForAt.union (Q₁ := fun d p => ClassRange LieTypeIndex.E7 (fun _ => True) 1 d p ∧ p ≠ 7)
    (Q₂ := fun d p => ClassRange LieTypeIndex.E7 (fun _ => True) 1 d p ∧ p = 7)
    (fun _ p _ _ hQ => by
      by_cases h7 : p = 7
      · exact Or.inr ⟨hQ, h7⟩
      · exact Or.inl ⟨hQ, h7⟩)
    seitzExcHighE7One_of_ne_seven seitzExcHighE7One_seven

end Certified

end CFSG.LieType.SeitzGeneration.ExcHigh
