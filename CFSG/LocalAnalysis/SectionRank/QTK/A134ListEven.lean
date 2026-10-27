module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.RankThree.PartOne.KF.ClsSpWit
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.A3Facts
open CFSG.SectionRank.ClassicalEven
open CFSG.Assembly.RankThreeEven (localRank)

variable {S : Type} [Group S] [Finite S]

theorem not_dvd_three_of_ne {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) : ¬ r ∣ 3 := fun h =>
  hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)

theorem oddLocalWitness_psl_three_even {f : ℕ} (hf : 2 ≤ f)
    (hm : StatedClassicalModel S .PSL 3 2 f) : OddLocalWitness S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  set e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
  rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
  · refine ⟨3, Nat.prime_three, by norm_num, ?_, ?_⟩
    · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
      exact psl_three_four_two_le_pRank hK
    · rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e' Nat.prime_three]
      exact CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (m := 1) Nat.prime_three
        (by rw [Nat.card_units, hK]; norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  · obtain ⟨r, hr, hrd, hr3⟩ := exists_prime_dvd_two_pow_sub_one hf3
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have h0 : 0 < 2 ^ f := by positivity
      omega
    refine oddLocalWitness_of_two_le_localRank hr hr2 ?_
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e' hr]
    exact CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (m := 2) hr
      (by rw [Nat.card_units, hK]; exact hrd) (by norm_num) (by norm_num)
      (Or.inr (not_dvd_three_of_ne hr hr3))

theorem oddLocalWitness_psu_three_even {f : ℕ} (hf : 2 ≤ f) (hf3 : f ≠ 3)
    (hm : StatedClassicalModel S .PSU 3 2 f) : OddLocalWitness S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  obtain ⟨r, hr, hrd, hr3⟩ := exists_prime_dvd_two_pow_add_one hf hf3
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h0 : 0 < 2 ^ f := by positivity
    omega
  refine ⟨r, hr, hr2, ?_, ?_⟩
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    have := Fact.mk hr
    have hq : 2 ^ f ≠ 0 := by positivity
    have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
      rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
      (by rw [hcard]; exact hrd.mul_right _)
    have hζq : ζ ^ (2 ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hrd)
    exact two_le_pRank_torus_shared hr3 hζ (i₀ := 0) (i₁ := 1) (i₂ := 2) (by decide) (by decide)
      (by decide)
      (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
      (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
  · rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
    exact CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (k := 0) hr hrd
      (by norm_num) (Or.inr (not_dvd_three_of_ne hr hr3))

theorem oddLocalWitness_psp_two_even {f : ℕ} (hf : 2 ≤ f)
    (hm : StatedClassicalModel S .PSp 2 2 f) : OddLocalWitness S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨r, hr, hr2, -, hrd⟩ :=
    CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one hf
  refine oddLocalWitness_of_two_le_localRank hr hr2 ?_
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
  exact CFSG.RankThree.PartOne.KFU.le_localRank_statedSp_torus hr hr2
    (by rw [Nat.card_units, hK]; exact hrd) (by norm_num)

end CFSG.SectionRank.QTK
