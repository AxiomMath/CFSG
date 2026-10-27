module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusInner
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSmall
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.HardMathSupport.Curtis.Coordinator

theorem pow_four_dvd_card_mulAut {p r : ℕ} {S : Type*} [Group S] {E : Subgroup (MulAut S)}
    {ζ γ : MulAut S} (h : SPLAutData p r S E ζ γ) : p ^ 4 ∣ Nat.card (MulAut S) := by
  rw [← h.card]
  exact Subgroup.card_subgroup_dvd_card E

theorem not_pow_four_dvd_336 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 4 ∣ 336 := by
  intro h
  have h1 : p ^ 4 ≤ 336 := Nat.le_of_dvd (by norm_num) h
  have h2 : p ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 5 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hlt 4
    omega
  have h3 := hp.two_le
  interval_cases p <;> first | exact hp2 rfl | (norm_num at h)

theorem not_pow_four_dvd_12096 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 4 ∣ 12096 := by
  intro h
  have h1 : p ^ 4 ≤ 12096 := Nat.le_of_dvd (by norm_num) h
  have h2 : p ≤ 10 := by
    by_contra hlt
    push Not at hlt
    have : 11 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hlt 4
    omega
  have h3 := hp.two_le
  interval_cases p <;> first | exact hp2 rfl | (norm_num at h)

theorem false_of_psu_three_three_family {S : Type} [Group S] [Finite S]
    (hnab : ∃ a b : S, a * b ≠ b * a) [IsSimpleGroup S] (h : StatedClassicalModel S .PSU 3 3 1)
    {p r : ℕ} {E : Subgroup (MulAut S)} {ζ γ : MulAut S} (hd : SPLAutData p r S E ζ γ) : False := by
  have hinj := conj_injective_of_center_eq_bot'
    (CFSG.LocalAnalysis.RankThreeTheoremC.center_eq_bot_of_simple hnab)
  obtain ⟨K, _, hU3, hq, hn3, ⟨e⟩⟩ := CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_primeFormP_gen h
  obtain ⟨⟨eP⟩, -, -, hOutT, -⟩ := unitary_full_diagonal_outer_order hU3 hn3 hq
  have hOut : Nat.card (Outer S) = 2 := by
    obtain ⟨⟨e', -⟩, -⟩ := (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e)
    rw [Nat.card_congr e'.toEquiv, hOutT]
    norm_num
  have hY : Nat.card S = 6048 := by
    have h1 := CFSG.AGLEmbedding.ParabAutIrr.card_unitaryPSU_three_mul_gcd hU3
    rw [← Nat.card_congr (e.trans eP).toEquiv] at h1
    norm_num at h1
    exact h1
  have hAut : Nat.card (MulAut S) = 12096 := by
    rw [CFSG.AGLEmbedding.ParabAutIrr.card_mulAut_eq_card_outer_mul hinj, hOut, hY]
  exact not_pow_four_dvd_12096 hd.prime_p hd.ne_two (hAut ▸ pow_four_dvd_card_mulAut hd)

theorem false_of_psl_seven_family {S : Type} [Group S] [Finite S]
    (hnab : ∃ a b : S, a * b ≠ b * a) [IsSimpleGroup S] (h : StatedClassicalModel S .PSL 2 7 1)
    {p r : ℕ} {E : Subgroup (MulAut S)} {ζ γ : MulAut S} (hd : SPLAutData p r S E ζ γ) : False := by
  have hinj := conj_injective_of_center_eq_bot'
    (CFSG.LocalAnalysis.RankThreeTheoremC.center_eq_bot_of_simple hnab)
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hdvd := (linear_two_outer_order_divisor (p := 7) (f := 1) (by norm_num) F
    (by simpa using hcard)).2 S ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  have hOut : Nat.card (Outer S) ∣ 2 := by simpa using hdvd
  have hY : Nat.card S = 168 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
      hcard]
    norm_num
  have hAut : Nat.card (MulAut S) ∣ 336 := by
    rw [CFSG.AGLEmbedding.ParabAutIrr.card_mulAut_eq_card_outer_mul hinj, hY]
    exact (Nat.mul_dvd_mul_right hOut 168)
  exact not_pow_four_dvd_336 hd.prime_p hd.ne_two ((pow_four_dvd_card_mulAut hd).trans hAut)

end CFSG.HardMathSupport.Curtis.Coordinator
