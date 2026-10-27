module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
import CFSG.RankThree.PartOne.KLC.EigE6
import CFSG.RankThree.PartOne.KE.CTCasesE6Eight
import CFSG.RankThree.PartOne.KE.CTCasesE6Nine
import CFSG.RankThree.PartOne.KE.CTCasesE6Twelve
import CFSG.RankThree.PartOne.KE.CTMain
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors small_prime_geom_sum_guard)


theorem zmod7_phi5_ne : ∀ x : ZMod 7, x ^ 4 + x ^ 3 + x ^ 2 + x + 1 ≠ 0 := by decide

section


theorem card_adjointGroup_E6_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (adjointGroup Tag.E6 K) ∣
      Nat.card K ^ 36 * ([12, 9, 8, 6, 5, 2].map fun d => Nat.card K ^ d - 1).prod := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, CFSG.Open.ordE6]
  generalize Nat.card K = q
  have hnum : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1) = q ^ 36 * ([12, 9, 8, 6, 5, 2].map fun d => q ^ d - 1).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  rw [← hnum]
  refine Nat.div_dvd_of_dvd ?_
  have h1 : Nat.gcd 3 (q - 1) ∣ q ^ 2 - 1 := by
    refine (Nat.gcd_dvd_right 3 (q - 1)).trans ?_
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  exact h1.trans (dvd_mul_left _ _)

theorem untwCrossRankStep_E6 (g5 : CyclicSylowGap Tag.E6 5) : UntwCrossRankStep Tag.E6 := by
  refine untwCrossRankStep_of_row (D := [12, 9, 8, 6, 5, 2]) (N := 36) (by decide)
    (fun K _ _ => card_adjointGroup_E6_dvd K) ?_
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
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 k)) := by
    intro e he h
    have h' := (dvd_eval_iff_of_natCast_eq (exhaustionPhi e) hcong).1 h
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_E6_of_sector hp hp5 hpk he h'
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 8 ∨ m = 9 ∨ m = 12 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      exhaustionMinusFactors, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hlow 1 (by simp) hpm
  · exact hlow 2 (by simp) hpm
  · exact hlow 3 (by simp) hpm
  · exact hlow 4 (by simp) hpm
  ·
    by_cases hp7 : 7 < p
    · have := g5 K hp hp7 hpm
      omega
    · have hp57 : p = 5 ∨ p = 7 := by
        have : p ≤ 7 := by omega
        interval_cases p <;> first | omega | (exfalso; revert hp; norm_num) | simp
      rcases hp57 with rfl | rfl
      · have hsum : ((5 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 5, (1 * (Nat.card K : ℤ)) ^ j := by
          simpa [exhaustionPhi, Finset.sum_range_succ, one_mul, add_assoc, add_comm, add_left_comm]
            using hpm
        obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by omega)
          (fun h => hpK (Int.natCast_dvd_natCast.1 h)) (r := 5) (Or.inl rfl) (δ := 1)
          (Or.inl rfl) hsum le_rfl
        refine hlow 1 (by simp) ?_
        simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
      · exfalso
        have hz : (((exhaustionPhi 5).eval (Nat.card K : ℤ) : ℤ) : ZMod 7) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 hpm
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one] at hz
        exact zmod7_phi5_ne _ hz
  · exact hlow 6 (by simp) hpm
  · have h := CFSG.RankThree.PartOne.KE.E6_eight_cyclic_sylow
      CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ := h
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  · have h := CFSG.RankThree.PartOne.KE.E6_nine_cyclic_sylow
      CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ := h
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  · have h := CFSG.RankThree.PartOne.KE.E6_twelve_cyclic_sylow
      CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers K hp (by omega) hpm
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ := h
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
