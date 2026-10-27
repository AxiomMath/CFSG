module

public import CFSG.ClassicalInvolution.AschTight.S19RData
public import CFSG.ClassicalInvolution.AschTight.S1911E2c
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem c19_main_of (h11b : C19_11bTmp p f) (h16F : C19_16FTmp p f) : Asc77.C19_main p f := by
  intro G _ _ _ Ω K S R z hstd W hW hWS hS3
  have hd := sec19Data_of_std6 hstd hW hWS hS3
  have hE3 := normalizerQuotientTwoGeneratedStar_of_innerDiagonalTwo hd.tight.branch.odd
    hd.tight.branch.five hd.tight.branch.member (S1911.innerDiagonalTwo_of_c19_16F h16F hd)
  exact Or.inr
    (S1911.twoSubgroupsFourGenerated_of_e2Prime (S1911.c19_E2PrimeTmp_of p f h11b) hd hE3)

variable {p f} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19R
