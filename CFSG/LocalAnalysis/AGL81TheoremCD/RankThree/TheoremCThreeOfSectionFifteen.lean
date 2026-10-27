module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOfTwelveTen
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.TheoremCThree
public import CFSG.Yardstones.Me2c15c2c995a.Definitions
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModuleFacts
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.Final
public import CFSG.GroupTheory.HuppertProduct.RankBound

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankThree

open CFSG.LocalAnalysis.RankThreeUC

section TheoremD


theorem agl81TheoremD_of_sectionFifteen
    (h15 : CFSG.Yardstones.Me2c15c2c995a.AGL81SectionFifteen) :
    ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremD G :=
  fun G _ _ hS =>
    haveI := hS.simple
    agl81TheoremD_of_split CFSG.GroupTheory.HuppertProduct.kFactHuppertProductThree_holds
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.agl81I59
      (CFSG.LocalAnalysis.RankThreeTheoremC.d1NoXBlock3_of_inputsK
        CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
        CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
        CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds)
      hS (h15 G hS)
      (CFSG.Yardstones.M9cbf837c48cf.agl81TheoremDSection16_proved G hS.nonab hS.kProper
        hS.charTwo hS.rank)

end TheoremD

section TheoremC


theorem agl81TheoremC_of_twelveTenGen (h1210 : Section14.TwelveTenGen)
    (h15 : CFSG.Yardstones.Me2c15c2c995a.AGL81SectionFifteen) :
    ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G :=
  fun _ _ _ hS => agl81TheoremC_of_fourteenFifteen
    (Section14.agl81FourteenFifteen_of_twelveTenGen h1210) hS
    (agl81TheoremD_of_sectionFifteen h15 _ hS)

end TheoremC

end CFSG.LocalAnalysis.AGL81TheoremCD.RankThree
