module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement



section G3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem e4_data_of_yOrth {c : Y} (hΛ : Q3T7M.HM (liftFam (TwinDisc.secFam (Om R) c)))
    (hgen : omegaGen (liftFam (TwinDisc.secFam (Om R) c)) = ⊤)
    (hY : SecOrthLift R c 5 true ∨ SecOrthLift R c 6 (!piSign 3 1)) :
    ∃ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
      Nonempty (Q3T8.Asc77.Ih8Model (liftFam (TwinDisc.secFam (Om R) c)) tag k e') ∧
        ((tag = .PSp ∧ k = 2) ∨ (tag = .PSL ∧ k = 4 ∧ 3 % 4 = 3) ∨
          (tag = .PSU ∧ k = 4 ∧ 3 % 4 = 1)) := by
  have hε : (!piSign 3 1) = true := by decide
  rcases hY with ⟨D, hc, tag, k, hort, hcis⟩ | ⟨D, hc, tag, k, hort, hcis⟩
  · obtain ⟨e', hM⟩ := TwinDimTool.exists_model hΛ hgen D hc ⟨0, by omega⟩ hcis
    refine ⟨tag, k, e', hM, ?_⟩
    rcases hort with ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl ⟨h1, h2⟩
    all_goals omega
  · obtain ⟨e', hM⟩ := TwinDimTool.exists_model hΛ hgen D hc ⟨0, by omega⟩ hcis
    refine ⟨tag, k, e', hM, ?_⟩
    rw [hε] at hort
    rcases hort with ⟨h, -⟩ | ⟨-, -, h1, h2⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · exact Or.inr (Or.inl ⟨h1, h2, by norm_num⟩)
    · exact absurd h (by decide)
    all_goals omega

end G3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
