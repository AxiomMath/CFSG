module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU2Cell
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5InvP
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Pair
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Tr
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3U3
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Typ

public section

namespace CFSG.OddStandard.GH71.S55.C5U

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)

theorem index_blkGU_two :
    (blkGU h 2).range.index = (r ^ f) ^ 2 * ((r ^ f) ^ 2 - r ^ f + 1) := by
  have e1 := Subgroup.card_mul_index (blkGU h 2).range
  change _ = Nat.card (StatedSU 3 (r ^ f) K) at e1
  rw [← Nat.card_congr (MonoidHom.ofInjective (blkGU_injective h 2)).toEquiv, card_uU_two h]
    at e1
  have e2 := card_statedSU_three_int h
  have hq2 : 2 ≤ r ^ f := h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) r)
  generalize (blkGU h 2).range.index = N at e1 ⊢
  generalize Nat.card (StatedSU 3 (r ^ f) K) = C at e1 e2
  generalize r ^ f = q at e1 e2 hq2 ⊢
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero _
  zify [hq1, hqq] at e1 ⊢
  rw [e2] at e1
  have hq : (2 : ℤ) ≤ q := by exact_mod_cast hq2
  have hne : (q : ℤ) * ((q + 1) * (q ^ 2 - 1)) ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
    positivity
  apply mul_left_cancel₀ hne
  rw [e1]
  ring

include h in
theorem not_dvd_index_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hrp : r ≠ p)
    (hpq : p ∣ r ^ f - 1 ∨ p ∣ r ^ f + 1) : ¬ p ∣ (r ^ f) ^ 2 * ((r ^ f) ^ 2 - r ^ f + 1) := by
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ h.prime.pos
  have h6 : ¬ p ∣ (r ^ f) ^ 2 - r ^ f + 1 := by
    rcases hpq with h1 | h1
    · exact (C5.cyc1_excl hp5 hq1 h1).2.2.2.2.1
    · exact (C5.cyc2_excl hp5 hq1 h1).2.2.2.2.1
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
  · exact C5.not_dvd_pow hp h.prime hrp (by rw [← pow_mul] at hd; exact hd)
  · exact h6 hd

include h in
theorem comp5Concl_psu3_block (hr2 : r ≠ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hrp : r ≠ p)
    (hpq : p ∣ r ^ f - 1 ∨ p ∣ r ^ f + 1) {y : StatedProj (StatedSU 3 (r ^ f) K)}
    (hy : orderOf y = p) (hyr : RFree r y) : Comp5Concl r y := by
  have := h.finite
  have : Fact r.Prime := ⟨h.prime⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K r := h.charP
  have hK := h.card_eq_sq
  have hq3 : r ^ f ≠ 3 := by
    intro h3
    rw [h3] at hpq
    rcases hpq with h1 | h1
    · exact absurd (Nat.le_of_dvd (by norm_num) h1) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h1) (by omega)
  obtain ⟨e0⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two hK
  obtain ⟨hq, hc, hrL⟩ := typ_sl h.prime hr2 h.one_le (Or.inl rfl)
    (CFSG.LieType.Steinberg.card_fixedSubfield hK) (Or.inr hq3)
    (e0.trans (blkLEquiv h 2 3 (by norm_num)))
  refine comp5Concl_of_le_normalizer h (by norm_num) ?_ (range_blkGU_le_normalizer h 2) hq hc hrL
    ?_ hy hyr
  · rw [index_blkGU_two h]
    exact not_dvd_index_two h hp hp5 hrp hpq
  · have e3 := card_statedSU_three_int h
    rw [CFSG.RankThree.SubgroupLists.card_statedSU_two hK]
    have hq3' := C5.three_le_pow h.prime hr2 h.one_le
    generalize r ^ f = q at e3 hq3' ⊢
    have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hq1]
    rw [e3]
    have hq : (3 : ℤ) ≤ q := by exact_mod_cast hq3'
    have h8 : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
    have h9 : (0 : ℤ) < (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by positivity
    have h10 : (0 : ℤ) < (q : ℤ) ^ 2 * ((q : ℤ) ^ 3 + 1) - 3 := by nlinarith
    nlinarith [mul_pos h9 h10]

include h in
theorem dvd_card_three {p : ℕ} {y : StatedProj (StatedSU 3 (r ^ f) K)} (hy : orderOf y = p) :
    p ∣ (r ^ f) ^ 3 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 + 1)) := by
  have := h.finite
  have h1 : p ∣ Nat.card (StatedSU 3 (r ^ f) K) :=
    (hy ▸ orderOf_dvd_natCard y).trans (Subgroup.card_quotient_dvd_card _)
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ h.prime.pos
  have e : Nat.card (StatedSU 3 (r ^ f) K) =
      (r ^ f) ^ 3 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 + 1)) := by
    have e3 := card_statedSU_three_int h
    zify [Nat.one_le_pow 2 _ hq1]
    exact_mod_cast e3
  rwa [e] at h1

theorem dvd_cases_three {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q)
    (h : p ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    p ∣ q - 1 ∨ p ∣ q + 1 ∨ p ∣ q ^ 2 - q + 1 := by
  have e : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) =
      q ^ 3 * ((q - 1) * (q + 1) * ((q + 1) * (q ^ 2 - q + 1))) := by
    zify [hq, Nat.one_le_pow 2 _ hq, Nat.le_self_pow two_ne_zero q]
    ring
  rw [e] at h
  rcases hp.dvd_mul.1 h with h | h
  · exact absurd (hp.dvd_of_dvd_pow h) hpq
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rcases hp.dvd_mul.1 h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

include h in
theorem comp5Concl_psu3
    (hr2 : r ≠ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrp : r ≠ p) {y g : StatedProj (StatedSU 3 (r ^ f) K)} (hy : orderOf y = p)
    (hyr : RFree r y) (hJ : PairSL2 p y g) : Comp5Concl r y := by
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K r := h.charP
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ h.prime.pos
  rcases dvd_cases_three hp hq1 (C5.not_dvd_pow hp h.prime hrp) (dvd_card_three h hy) with
    h1 | h2 | h6
  · exact comp5Concl_psu3_block h hr2 hp hp5 hrp (Or.inl h1) hy hyr
  · exact comp5Concl_psu3_block h hr2 hp hp5 hrp (Or.inr h2) hy hyr
  · have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K r]; exact hr2)
    exact absurd hJ (not_pairSL2_of_no_two_p hp (by omega)
      (fun w => orderOf_ne_two_mul_psu3 hp5 h2K h.card_eq_sq h6 w) (noR_two_of_psu3 h hr2) y g)

end CFSG.OddStandard.GH71.S55.C5U

namespace CFSG.OddStandard.GH71.S55

open CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.Blueprint C5U

theorem comp5_fu3d : Comp5 FU3d := by
  refine comp5_of fun r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hyr hJ => ?_
  obtain ⟨f, hf, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSU 3 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have h : UnitaryFieldData r f K := ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  exact comp5Concl_of_mulEquiv e
    (fun hy' hyr' hJ' => comp5Concl_psu3 h hr2 hp hp5 hrp hy' hyr' hJ') hy hyr hJ

end CFSG.OddStandard.GH71.S55
