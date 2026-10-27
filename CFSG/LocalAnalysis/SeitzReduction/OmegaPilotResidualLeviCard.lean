module

public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Assembly.LowTwoRank

section TwoPart

theorem odd_pow_sub_one {q k : ℕ} (hq : Even q) (hq1 : 1 ≤ q) (hk : 1 ≤ k) : Odd (q ^ k - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) ((Nat.even_pow' (by omega)).mpr hq) odd_one

theorem odd_prod_pow_sub_one {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q) (s : Finset ℕ) (e : ℕ → ℕ)
    (he : ∀ i ∈ s, 1 ≤ e i) : Odd (∏ i ∈ s, (q ^ e i - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (odd_pow_sub_one hq hq1 (he a (Finset.mem_insert_self a s))).mul
      (ih fun i hi => he i (Finset.mem_insert_of_mem hi))

theorem eq_of_two_pow_mul_odd {a b O O' : ℕ} (hO : Odd O) (hO' : Odd O')
    (h : 2 ^ a * O = 2 ^ b * O') : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    have h' : 2 ^ a * O = 2 ^ a * (2 ^ (b - a) * O') := by
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
    have hO2 := Nat.eq_of_mul_eq_mul_left (by positivity) h'
    have hdvd : 2 ∣ O := hO2 ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)
  · exact hab
  · exfalso
    have h' : 2 ^ b * O' = 2 ^ b * (2 ^ (a - b) * O) := by
      rw [← h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
    have hO2 := Nat.eq_of_mul_eq_mul_left (by positivity) h'
    have hdvd : 2 ∣ O' := hO2 ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    exact (Nat.not_even_iff_odd.mpr hO') (even_iff_two_dvd.mpr hdvd)

theorem mul_pred_ne_sq {m : ℕ} (hm : 2 ≤ m) (r : ℕ) : m * (m - 1) ≠ r ^ 2 := by
  intro h
  have h1 : r ^ 2 < m ^ 2 := by
    rw [← h, sq]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have h2 : (m - 1) ^ 2 < r ^ 2 := by
    rw [← h, sq]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have h3 : r < m := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h1
  have h4 : m - 1 < r := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
  omega

end TwoPart

section Charts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem card_statedProj_statedSp_eq_mul_odd (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (r : ℕ) :
    ∃ O, Odd O ∧ Nat.card (StatedProj (StatedSp r K)) = Nat.card K ^ (r ^ 2) * O := by
  refine ⟨_, ?_, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo r⟩
  have hq : Even (Nat.card K) := by
    rw [hK]
    exact (Nat.even_pow' (by omega)).mpr even_two
  exact odd_prod_pow_sub_one hq Nat.card_pos _ _ fun j hj => by
    simp only [Finset.mem_Icc] at hj
    omega

theorem isEmpty_mulEquiv_statedSp_of_card (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) {G : Type*}
    [Group G] {a O : ℕ} (hG : Nat.card G = Nat.card K ^ a * O) (hO : Odd O)
    (ha : ∀ r : ℕ, a ≠ r ^ 2) (r : ℕ) : IsEmpty (G ≃* StatedProj (StatedSp r K)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨O', hO', hcard⟩ := card_statedProj_statedSp_eq_mul_odd hK hf r
  have h := (Nat.card_congr e.toEquiv).symm.trans hG
  rw [hcard, hK, ← pow_mul, ← pow_mul] at h
  have h' := eq_of_two_pow_mul_odd hO' hO h
  exact ha r (Nat.eq_of_mul_eq_mul_left (by omega) h').symm

theorem card_statedProj_statedOmega_quadPlus_eq_mul_odd (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {m : ℕ} (hm : 4 ≤ m) :
    ∃ O, Odd O ∧ Nat.card (StatedProj (StatedOmega (StatedQuadPlus m K))) =
      Nat.card K ^ (m * (m - 1)) * O := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq : Even (Nat.card K) := by
    rw [hK]
    exact (Nat.even_pow' (by omega)).mpr even_two
  refine ⟨(Nat.card K ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1),
    (odd_pow_sub_one hq hq1 (by omega)).mul
      (odd_prod_pow_sub_one hq hq1 _ _ fun i hi => by simp only [Finset.mem_Icc] at hi; omega), ?_⟩
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K) hm
  have e1 : ((Nat.card K ^ m - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
    push_cast
    ring
  have e2 : ((∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
    push_cast
    ring
  have key : (Nat.card (StatedProj (StatedOmega (StatedQuadPlus m K))) : ℤ) =
      ((Nat.card K ^ (m * (m - 1)) * ((Nat.card K ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1)) : ℕ) : ℤ) := by
    rw [h, Nat.cast_mul, Nat.cast_mul, e1, e2]
    push_cast
    ring
  exact_mod_cast key

end Charts

end CFSG.SeitzReduction.OmegaPilot
