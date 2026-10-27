module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SetupCenter
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YHyp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

section Certified

theorem centreDvdThree_of : CentreDvdThree := by
  intro G _ _ L hS hL
  haveI : Group.IsPerfect ↥L := ⟨hS.std.standard.1.1⟩
  exact Setup.card_center_dvd_three inferInstance hL

theorem oddCentre_of : OddCentre := by
  intro G _ _ L hS hL
  haveI : Group.IsPerfect ↥L := ⟨hS.std.standard.1.1⟩
  have h3 : Nat.card ↥(center ↥L) ∣ 3 := Setup.card_center_dvd_three inferInstance hL
  exact Odd.of_dvd_nat (by decide) h3

theorem outTwo_of : OutTwo := by
  intro Q _ hQ
  have hY : CFSG.Blueprint.ChevalleyExceptionalModel Q .G2 3 1 :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hQ (by decide)
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) = 2 :=
    CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.card_outer_G2_three Q hY
  exact h2

end Certified

end CFSG.OddStandard.HigherRank.YamadaG23
