module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
import CFSG.RankThree.PartOne.KLC.EigF4
import CFSG.RankThree.PartOne.KE.CTCasesF4
import CFSG.RankThree.PartOne.KE.CTMain
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors)


section


theorem card_adjointGroup_F4_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (adjointGroup Tag.F4 K) ∣
      Nat.card K ^ 24 * ([12, 8, 6, 2].map fun d => Nat.card K ^ d - 1).prod := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, CFSG.Open.ordF4]
  generalize Nat.card K = q
  have hnum : q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) =
      q ^ 24 * ([12, 8, 6, 2].map fun d => q ^ d - 1).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  exact dvd_of_eq hnum

theorem untwCrossRankStep_F4 : UntwCrossRankStep Tag.F4 := by
  refine untwCrossRankStep_of_row (D := [12, 8, 6, 2]) (N := 24) (by decide)
    (fun K _ _ => card_adjointGroup_F4_dvd K) ?_
  intro ℓ f₀ p hℓ hf₀ hp hp5 hne K k _ _ _ _ hK hk m hm hpm hrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hcong := natCast_card_eq_of_pow (p := p) hK hk
  have hpk : ¬ p ∣ Nat.card k := by
    rw [hk]
    exact OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hlow : ∀ e : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.F4 k)) := by
    intro e he h
    have h' := (dvd_eval_iff_of_natCast_eq (exhaustionPhi e) hcong).1 h
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_F4_of_sector hp hp5 hpk he h'
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 12 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      exhaustionMinusFactors, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hlow 1 (by simp) hpm
  · exact hlow 2 (by simp) hpm
  · exact hlow 3 (by simp) hpm
  · exact hlow 4 (by simp) hpm
  · exact hlow 6 (by simp) hpm
  ·
    have h := CFSG.RankThree.PartOne.KE.F4_eight_cyclic_sylow
      CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers_F4 K hp (by omega) hpm
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ := h
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  ·
    have h := CFSG.RankThree.PartOne.KE.F4_twelve_cyclic_sylow
      CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers_F4 K hp (by omega) hpm
    obtain ⟨-, -, T, -, -, -, -, hcyc, -⟩ := h
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
