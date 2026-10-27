module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall
public import CFSG.Assembly.OrderReductions.PermutationReduction
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.BenderSuzuki CFSG.GH74.Uniqueness.Bender Subgroup

namespace TwinThmEW

theorem simple_sylow_split {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ¬ IsMulCommutative L) (p : ℕ) [hp : Fact p.Prime] (hdvd : p ∣ Nat.card L) :
    ∃ c ∈ (Nat.card L).divisors, p ∣ c ∧ ¬ p ∣ Nat.card L / c ∧ 5 * c ≤ Nat.card L := by
  obtain ⟨P⟩ : Nonempty (Sylow p L) := inferInstance
  have h5 := CFSG.OrderReductions.PermutationReduction.simple_noncommutative_sylow_card_mul_five_le_card
    L hnab p hdvd P
  have hmul : Nat.card P * (P : Subgroup L).index = Nat.card L := (P : Subgroup L).card_mul_index
  have hpos : 0 < Nat.card L := Nat.card_pos
  refine ⟨Nat.card P, Nat.mem_divisors.mpr ⟨⟨_, hmul.symm⟩, hpos.ne'⟩, ?_, ?_, h5⟩
  · rw [P.card_eq_multiplicity]
    exact dvd_pow_self p (Nat.ne_of_gt ((Nat.Prime.factorization_pos_of_dvd hp.out hpos.ne' hdvd)))
  · have hidx : Nat.card L / Nat.card P = (P : Subgroup L).index := by
      rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
    rw [hidx]
    exact P.not_dvd_index

theorem no_simple_nonab_le_sixteen {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ¬ IsMulCommutative L) (hle : Nat.card L ≤ 16) : False := by
  have hpos : 0 < Nat.card L := Nat.card_pos
  have h2 : 2 ≤ Nat.card L := by
    by_contra h
    have h1 : Nat.card L = 1 := by omega
    have : Subsingleton L := (Nat.card_eq_one_iff_unique.mp h1).1
    exact hnab (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
  have table : ∀ N ∈ Finset.Icc 2 16, ∃ p ∈ Finset.range 17, p.Prime ∧ p ∣ N ∧
      ∀ c ∈ N.divisors, p ∣ c → ¬ p ∣ N / c → N < 5 * c := by
    decide
  obtain ⟨p, -, hp, hpN, hall⟩ := table (Nat.card L) (Finset.mem_Icc.mpr ⟨h2, hle⟩)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc, hpc, hpi, h5⟩ := simple_sylow_split hnab p hpN
  have := hall c hc hpc hpi
  omega

theorem psu3_two_le {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ¬ IsMulCommutative L) {n : ℕ} (e : L ≃* PSU3Model n) : 2 ≤ n := by
  by_contra h
  have hcard : Nat.card L = Nat.card (PSU3Model n) := Nat.card_congr e.toEquiv
  have hn : n < 2 := by omega
  interval_cases n
  · exact no_simple_nonab_le_sixteen hnab
      (hcard ▸ CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_zero_le)
  · exact CFSG.OrderReductions.PermutationReduction.simple_noncommutative_not_card_72 L hnab
      (hcard.trans CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_one)

theorem psu3_benderType {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ¬ IsMulCommutative L) {n : ℕ} (e : L ≃* PSU3Model n) :
    BenderType L n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
  BenderType.unitary n (psu3_two_le hnab e) e

theorem psu3_sylow_nonabelian {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ¬ IsMulCommutative L) {n : ℕ} (e : L ≃* PSU3Model n) (Q : Sylow 2 L) :
    ∃ x ∈ (Q : Subgroup L), ∃ y ∈ (Q : Subgroup L), x * y ≠ y * x := by
  have hB := psu3_benderType hnab e
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  by_contra hcon
  push Not at hcon
  have hZ : rootCenter (Q : Subgroup L) = (Q : Subgroup L) := by
    apply le_antisymm inf_le_left
    intro x hx
    refine mem_rootCenter_iff.mpr ⟨hx, fun g hg => hcon g hg x hx⟩
  have h1 := hc.card_eq
  have h2 := hc.card_center
  rw [hZ, h1] at h2
  have hn := psu3_two_le hnab e
  have h4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  generalize 2 ^ n = q at h2 h4
  nlinarith [Nat.mul_le_mul h4 h4]

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
