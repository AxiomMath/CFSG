module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRGlue
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankMain
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.RankThree.PartTwo.Sec4.Census
  (IsThreeCenterCover TripleCoverLieIndex tripleCoverLie_of_griess)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank
open TauCeti

theorem k37Rest₁_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) : K37Rest₁ := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨d, hc, q, hd, -⟩ := hO
  obtain ⟨φ, hφ, hker, h3, hodd⟩ := k37R_exists_cover hs.core hc
  have hidx := tripleCoverLie_of_griess hGA d ↥K hc
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .twistedE6 q := hd
  have h3q : 3 ∣ q.card + 1 := hidx
  have hp3 : q.p ≠ 3 := by
    intro hp
    have h1 : 3 ∣ q.card := by
      rw [PrimePower.card_def, hp]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    have h2 : 3 ∣ 1 := (Nat.dvd_add_right h1).1 h3q
    omega
  have hL := twistedE6_liftDatum q hv hp3
  have h4 := hL.cover_localRank (π := φ) hφ hker.le hodd (A := ⊥) bot_le
    (fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]) (k := 0) (by simp)
  exact k37R_false_of_four_le_localRank hs (show 4 ≤ localRank 3 ↥K by omega)

theorem k37Rest₁_holds
    : K37Rest₁ :=
  k37Rest₁_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
