module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
import CFSG.RankThree.PartOne.KLC.EigE7
import CFSG.RankThree.PartOne.KE.CTCasesE7CoxNine
import CFSG.RankThree.PartOne.KE.CTCasesE7CoxEighteen
import CFSG.RankThree.PartOne.KE.CTCasesE7Sev
import CFSG.RankThree.PartOne.KE.CTMain
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors small_prime_geom_sum_guard)


theorem E7_zmod5_phi7_ne : ∀ x : ZMod 5, x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 ≠ 0 := by
  decide

theorem E7_zmod7_phi5_ne : ∀ x : ZMod 7, x ^ 4 + x ^ 3 + x ^ 2 + x + 1 ≠ 0 := by
  decide

theorem E7_zmod5_phi8_ne : ∀ x : ZMod 5, x ^ 4 + 1 ≠ 0 := by
  decide

theorem E7_zmod7_phi8_ne : ∀ x : ZMod 7, x ^ 4 + 1 ≠ 0 := by
  decide

theorem E7_zmod7_phi10_ne : ∀ x : ZMod 7, x ^ 4 - x ^ 3 + x ^ 2 - x + 1 ≠ 0 := by
  decide

theorem E7_zmod5_phi12_ne : ∀ x : ZMod 5, x ^ 4 - x ^ 2 + 1 ≠ 0 := by
  decide

theorem E7_zmod7_phi12_ne : ∀ x : ZMod 7, x ^ 4 - x ^ 2 + 1 ≠ 0 := by
  decide

theorem E7_zmod5_phi14_ne : ∀ x : ZMod 5, x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1 ≠ 0 := by
  decide

theorem E7_p_eq_five_or_seven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : ¬ 7 < p) :
    p = 5 ∨ p = 7 := by
  have : p ≤ 7 := by omega
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num) | simp

section


theorem card_adjointGroup_E7_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (adjointGroup Tag.E7 K) ∣
      Nat.card K ^ 63 * ([18, 14, 12, 10, 8, 6, 2].map fun d => Nat.card K ^ d - 1).prod := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, CFSG.Open.ordE7]
  generalize Nat.card K = q
  have hnum : q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1) =
        q ^ 63 * ([18, 14, 12, 10, 8, 6, 2].map fun d => q ^ d - 1).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  rw [← hnum]
  refine Nat.div_dvd_of_dvd ?_
  have h1 : Nat.gcd 2 (q - 1) ∣ q ^ 2 - 1 := by
    refine (Nat.gcd_dvd_right 2 (q - 1)).trans ?_
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  exact h1.trans (dvd_mul_left _ _)

theorem untwCrossRankStep_E7 (g5 : CyclicSylowGap Tag.E7 5) (g8 : CyclicSylowGap Tag.E7 8)
    (g10 : CyclicSylowGap Tag.E7 10) (g12 : CyclicSylowGap Tag.E7 12) :
    UntwCrossRankStep Tag.E7 := by
  refine untwCrossRankStep_of_row (D := [18, 14, 12, 10, 8, 6, 2]) (N := 63) (by decide)
    (fun K _ _ => card_adjointGroup_E7_dvd K) ?_
  intro ℓ f₀ p hℓ hf₀ hp hp5 hne K k _ _ _ _ hK hk m hm hpm hrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hcong := natCast_card_eq_of_pow (p := p) hK hk
  have hpk : ¬ p ∣ Nat.card k := by
    rw [hk]
    exact OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hlow : ∀ e : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E7 k)) := by
    intro e he h
    have h' := (dvd_eval_iff_of_natCast_eq (exhaustionPhi e) hcong).1 h
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_E7_of_sector hp hp5 hpk he h'
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨
      m = 12 ∨ m = 14 ∨ m = 18 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      exhaustionMinusFactors, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hlow 1 (by simp) hpm
  · exact hlow 2 (by simp) hpm
  · exact hlow 3 (by simp) hpm
  · exact hlow 4 (by simp) hpm
  ·
    by_cases hp7 : 7 < p
    · have := g5 K hp hp7 hpm
      omega
    · rcases E7_p_eq_five_or_seven hp hp5 hp7 with rfl | rfl
      ·
        have hsum_eq : ∑ j ∈ Finset.range 5, (1 * (Nat.card K : ℤ)) ^ j =
            (exhaustionPhi 5).eval (Nat.card K : ℤ) := by
          simp only [exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero,
            Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_one, one_mul, zero_add]
          ring
        have hsum : ((5 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 5, (1 * (Nat.card K : ℤ)) ^ j := by
          rw [hsum_eq]
          exact hpm
        obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by omega)
          (fun h => hpK (Int.natCast_dvd_natCast.1 h)) (r := 5) (Or.inl rfl) (δ := 1)
          (Or.inl rfl) hsum le_rfl
        refine hlow 1 (by simp) ?_
        simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
      ·
        exfalso
        have hz : (((exhaustionPhi 5).eval (Nat.card K : ℤ) : ℤ) : ZMod 7) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact E7_zmod7_phi5_ne _ hz
  · exact hlow 6 (by simp) hpm
  ·
    by_cases hp7 : 7 < p
    · have h := CFSG.RankThree.PartOne.KE.E7_seven_cyclic_sylow
        CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp hp7 hpm
      obtain ⟨-, T, -, -, -, -, hcyc, -⟩ := h
      have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
      omega
    · rcases E7_p_eq_five_or_seven hp hp5 hp7 with rfl | rfl
      ·
        exfalso
        have hz : (((exhaustionPhi 7).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact E7_zmod5_phi7_ne _ hz
      ·
        have hsum_eq : ∑ j ∈ Finset.range 7, (1 * (Nat.card K : ℤ)) ^ j =
            (exhaustionPhi 7).eval (Nat.card K : ℤ) := by
          simp only [exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero,
            Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_one, one_mul, zero_add]
          ring
        have hsum : ((7 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 7, (1 * (Nat.card K : ℤ)) ^ j := by
          rw [hsum_eq]
          exact hpm
        obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by omega)
          (fun h => hpK (Int.natCast_dvd_natCast.1 h)) (r := 7) (Or.inr rfl) (δ := 1)
          (Or.inl rfl) hsum le_rfl
        refine hlow 1 (by simp) ?_
        simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
  ·
    by_cases hp7 : 7 < p
    · have := g8 K hp hp7 hpm
      omega
    · rcases E7_p_eq_five_or_seven hp hp5 hp7 with rfl | rfl
      ·
        exfalso
        have hz : (((exhaustionPhi 8).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact E7_zmod5_phi8_ne _ hz
      ·
        exfalso
        have hz : (((exhaustionPhi 8).eval (Nat.card K : ℤ) : ℤ) : ZMod 7) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact E7_zmod7_phi8_ne _ hz
  ·
    have h := CFSG.RankThree.PartOne.KE.E7_nine_cyclic_sylow
      CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ := h
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  ·
    by_cases hp7 : 7 < p
    · have := g10 K hp hp7 hpm
      omega
    · rcases E7_p_eq_five_or_seven hp hp5 hp7 with rfl | rfl
      ·
        have hsum_eq : ∑ j ∈ Finset.range 5, (-1 * (Nat.card K : ℤ)) ^ j =
            (exhaustionPhi 10).eval (Nat.card K : ℤ) := by
          simp only [exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero,
            Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_one, zero_add]
          ring
        have hsum : ((5 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 5, (-1 * (Nat.card K : ℤ)) ^ j := by
          rw [hsum_eq]
          exact hpm
        obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by omega)
          (fun h => hpK (Int.natCast_dvd_natCast.1 h)) (r := 5) (Or.inl rfl) (δ := -1)
          (Or.inr rfl) hsum le_rfl
        refine hlow 2 (by simp) ?_
        simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
      ·
        exfalso
        have hz : (((exhaustionPhi 10).eval (Nat.card K : ℤ) : ℤ) : ZMod 7) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
          Int.cast_one] at hz
        exact E7_zmod7_phi10_ne _ hz
  ·
    by_cases hp7 : 7 < p
    · have := g12 K hp hp7 hpm
      omega
    · rcases E7_p_eq_five_or_seven hp hp5 hp7 with rfl | rfl
      ·
        exfalso
        have hz : (((exhaustionPhi 12).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
          Int.cast_one] at hz
        exact E7_zmod5_phi12_ne _ hz
      ·
        exfalso
        have hz : (((exhaustionPhi 12).eval (Nat.card K : ℤ) : ℤ) : ZMod 7) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
          Int.cast_one] at hz
        exact E7_zmod7_phi12_ne _ hz
  ·
    by_cases hp7 : 7 < p
    · have h := CFSG.RankThree.PartOne.KE.E7_fourteen_cyclic_sylow
        CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp hp7 hpm
      obtain ⟨-, T, -, -, -, -, hcyc, -⟩ := h
      have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
      omega
    · rcases E7_p_eq_five_or_seven hp hp5 hp7 with rfl | rfl
      ·
        exfalso
        have hz : (((exhaustionPhi 14).eval (Nat.card K : ℤ) : ℤ) : ZMod 5) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
          Int.cast_one] at hz
        exact E7_zmod5_phi14_ne _ hz
      ·
        have hsum_eq : ∑ j ∈ Finset.range 7, (-1 * (Nat.card K : ℤ)) ^ j =
            (exhaustionPhi 14).eval (Nat.card K : ℤ) := by
          simp only [exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero,
            Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_one, zero_add]
          ring
        have hsum : ((7 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 7, (-1 * (Nat.card K : ℤ)) ^ j := by
          rw [hsum_eq]
          exact hpm
        obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by omega)
          (fun h => hpK (Int.natCast_dvd_natCast.1 h)) (r := 7) (Or.inr rfl) (δ := -1)
          (Or.inr rfl) hsum le_rfl
        refine hlow 2 (by simp) ?_
        simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
  ·
    have h := CFSG.RankThree.PartOne.KE.E7_eighteen_cyclic_sylow
      CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ := h
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
