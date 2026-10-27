module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017MSevenGmat
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Monster.Generated (Gmat)


theorem twoRankLe_seven_M
    : TwoRankLe 7 .M 2 := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  rw [← CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr (by norm_num)
    (e.trans b.symm)]
  exact glaTwoLocalRank_seven_Gmat

end CFSG.LocalAnalysis.GLTheoremA.H1017
