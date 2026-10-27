module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallExc

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall


theorem false_of_psl2Even_S {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypS n Y R S t) {f : ℕ}
    (hF : LieModel ↥(genFittingFStar Y) .PSL 2 2 f) : False := by
  haveI := h.core.simple
  rcases hF with ⟨-, hF⟩ | ⟨hF, -⟩ | ⟨hF, -⟩ | ⟨hF, -⟩
  · obtain ⟨hcyc, hout⟩ := twinCyc4_psl2Even hF
    exact false_of_outTwoCyclic_of_noTwinPair h hout (not_twinPair_of_twinCyc4 hcyc)
  all_goals exact absurd hF (by norm_num)

theorem leaf_exL2Even {n : ℕ} : TwinLeafS n ExL2Even :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hF => hF.elim (false_of_psl2Even_S h) (false_of_psl2Even_S h)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
