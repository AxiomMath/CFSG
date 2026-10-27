module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
import CFSG.RankThree.PartOne.KLC.EigE8
import CFSG.RankThree.PartOne.KE.CTCasesE8Coxeter
import CFSG.RankThree.PartOne.KE.CTCasesE8Explicit
import CFSG.RankThree.PartOne.KE.CTMain
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors small_prime_geom_sum_guard
  exhaustionPhi_twenty_mod_five)


theorem zmod5_phi7_ne : ∀ x : ZMod 5, x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 ≠ 0 := by
  decide

theorem zmod5_phi9_ne : ∀ x : ZMod 5, x ^ 6 + x ^ 3 + 1 ≠ 0 := by decide

theorem zmod5_phi14_ne : ∀ x : ZMod 5, x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1 ≠ 0 := by
  decide

theorem zmod5_phi18_ne : ∀ x : ZMod 5, x ^ 6 - x ^ 3 + 1 ≠ 0 := by decide

theorem zmod7_phi9_ne : ∀ x : ZMod 7, x ^ 6 + x ^ 3 + 1 ≠ 0 := by decide

theorem zmod7_phi18_ne : ∀ x : ZMod 7, x ^ 6 - x ^ 3 + 1 ≠ 0 := by decide

theorem E8_prime_five_or_seven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h7 : ¬ 7 < p) :
    p = 5 ∨ p = 7 := by
  have hle : p ≤ 7 := by omega
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num) | simp

section


theorem card_adjointGroup_E8_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (adjointGroup Tag.E8 K) ∣
      Nat.card K ^ 120 * ([30, 24, 20, 18, 14, 12, 8, 2].map fun d => Nat.card K ^ d - 1).prod := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, CFSG.Open.ordE8]
  generalize Nat.card K = q
  have hnum : q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) =
        q ^ 120 * ([30, 24, 20, 18, 14, 12, 8, 2].map fun d => q ^ d - 1).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  exact dvd_of_eq hnum

theorem untwCrossRankStep_E8 (g7 : CyclicSylowGap Tag.E8 7) (g9 : CyclicSylowGap Tag.E8 9)
    (g14 : CyclicSylowGap Tag.E8 14) (g18 : CyclicSylowGap Tag.E8 18) :
    UntwCrossRankStep Tag.E8 := by
  refine untwCrossRankStep_of_row (D := [30, 24, 20, 18, 14, 12, 8, 2]) (N := 120) (by decide)
    (fun K _ _ => card_adjointGroup_E8_dvd K) ?_
  intro ℓ f₀ p hℓ hf₀ hp hp5 hne K k _ _ _ _ hK hk m hm hpm hrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hcong := natCast_card_eq_of_pow (p := p) hK hk
  have hpk : ¬ p ∣ Nat.card k := by
    rw [hk]
    exact OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hlow : ∀ e : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12) →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 k)) := by
    intro e he h
    have h' := (dvd_eval_iff_of_natCast_eq (exhaustionPhi e) hcong).1 h
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_E8_of_sector hp hp5 hpk he h'
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨
      m = 12 ∨ m = 14 ∨ m = 15 ∨ m = 18 ∨ m = 20 ∨ m = 24 ∨ m = 30 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      exhaustionMinusFactors, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact hlow 1 (by simp) hpm
  · exact hlow 2 (by simp) hpm
  · exact hlow 3 (by simp) hpm
  · exact hlow 4 (by simp) hpm
  · exact hlow 5 (by simp) hpm
  · exact hlow 6 (by simp) hpm
  ·
    by_cases hp7 : 7 < p
    · have := g7 K hp hp7 hpm
      omega
    · rcases E8_prime_five_or_seven hp hp5 hp7 with rfl | rfl
      · exfalso
        have hz : (((exhaustionPhi 7).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact zmod5_phi7_ne _ hz
      · have hsum : ((7 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 7, (1 * (Nat.card K : ℤ)) ^ j := by
          have e : ∑ j ∈ Finset.range 7, (1 * (Nat.card K : ℤ)) ^ j =
              (exhaustionPhi 7).eval (Nat.card K : ℤ) := by
            simp only [exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero, one_mul,
              Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
              zero_add, pow_zero, pow_one]
            ring
          rw [e]
          exact hpm
        obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by omega)
          (fun h => hpK (Int.natCast_dvd_natCast.1 h)) (r := 7) (Or.inr rfl) (δ := 1)
          (Or.inl rfl) hsum le_rfl
        refine hlow 1 (by simp) ?_
        simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
  · exact hlow 8 (by simp) hpm
  ·
    by_cases hp7 : 7 < p
    · have := g9 K hp hp7 hpm
      omega
    · rcases E8_prime_five_or_seven hp hp5 hp7 with rfl | rfl
      · exfalso
        have hz : (((exhaustionPhi 9).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact zmod5_phi9_ne _ hz
      · exfalso
        have hz : (((exhaustionPhi 9).eval (Nat.card K : ℤ) : ℤ) : ZMod 7) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact zmod7_phi9_ne _ hz
  · exact hlow 10 (by simp) hpm
  · exact hlow 12 (by simp) hpm
  ·
    by_cases hp7 : 7 < p
    · have := g14 K hp hp7 hpm
      omega
    · rcases E8_prime_five_or_seven hp hp5 hp7 with rfl | rfl
      · exfalso
        have hz : (((exhaustionPhi 14).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
          Int.cast_one] at hz
        exact zmod5_phi14_ne _ hz
      · have hsum : ((7 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 7, (-1 * (Nat.card K : ℤ)) ^ j := by
          have e : ∑ j ∈ Finset.range 7, (-1 * (Nat.card K : ℤ)) ^ j =
              (exhaustionPhi 14).eval (Nat.card K : ℤ) := by
            simp only [exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero,
              Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
              Polynomial.eval_one, zero_add]
            ring
          rw [e]
          exact hpm
        obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by omega)
          (fun h => hpK (Int.natCast_dvd_natCast.1 h)) (r := 7) (Or.inr rfl) (δ := -1)
          (Or.inr rfl) hsum le_rfl
        refine hlow 2 (by simp) ?_
        simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
  ·
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ :=
      CFSG.RankThree.PartOne.KE.E8_fifteen_cyclic_sylow
        CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  ·
    by_cases hp7 : 7 < p
    · have := g18 K hp hp7 hpm
      omega
    · rcases E8_prime_five_or_seven hp hp5 hp7 with rfl | rfl
      · exfalso
        have hz : (((exhaustionPhi 18).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
          Int.cast_one] at hz
        exact zmod5_phi18_ne _ hz
      · exfalso
        have hz : (((exhaustionPhi 18).eval (Nat.card K : ℤ) : ℤ) : ZMod 7) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
          Int.cast_one] at hz
        exact zmod7_phi18_ne _ hz
  ·
    by_cases hp5' : 5 < p
    · obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ :=
        CFSG.RankThree.PartOne.KE.E8_twenty_cyclic_sylow
          CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp hp5' hpm
      have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
      omega
    · have hp5eq : p = 5 := by omega
      subst hp5eq
      have h5 : (5 : ℤ) ∣ (exhaustionPhi 20).eval (Nat.card K : ℤ) := by exact_mod_cast hpm
      have h4 := (exhaustionPhi_twenty_mod_five.2 (Nat.card K : ℤ)).1 h5
      exact hlow 4 (by simp) (by exact_mod_cast h4)
  ·
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ :=
      CFSG.RankThree.PartOne.KE.E8_twentyfour_cyclic_sylow
        CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  ·
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ :=
      CFSG.RankThree.PartOne.KE.E8_thirty_cyclic_sylow
        CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
