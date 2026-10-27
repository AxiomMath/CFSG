module

public import CFSG.Quasithin.EmptyFaithful.SzMSWConcl
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.SkConcl

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] {M T L : Subgroup G}

@[expose] def MS93ASW_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (M T L : Subgroup G), PUHyp M T L → MS93ConclASW M T L

theorem ms93AS_of_ms93ASW_F4 (h : MS93ASW_F4) : MS93AS_F4 :=
  fun G _ _ M T L hP => (h G M T L hP).toConclAS

end CFSG.Quasithin.SzMSW
