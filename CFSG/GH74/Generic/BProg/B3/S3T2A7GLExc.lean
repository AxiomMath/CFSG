module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLBasic
public import CFSG.GH74.Generic.ExceptionalRank
public import CFSG.GH74.Generic.GKFRank3D4

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup


theorem cell125_g2 (hF : GenericKnownFacts) : Cell125 OddG2 := by
  intro Y _ _ L B X₀ z hs hP _ _
  obtain ⟨p, f, hp, hp2, -, hm⟩ := hP
  exact GLR.false_of_noTwoCover hs (rankCertified_of_lieModel_G2 hp hp2 hm)
    (hF.noTwoCover_g2 p f hp hp2 _ hm)

theorem cell125_3d4 (hF : GenericKnownFacts) : Cell125 Odd3D4 := by
  intro Y _ _ L B X₀ z hs hP _ _
  obtain ⟨p, f, hp, hp2, -, hm⟩ := hP
  exact GLR.false_of_noTwoCover hs (rankCertified_of_lieModel_3D4 hp hp2 hm)
    (hF.noTwoCover_3D4 p f hp hp2 _ hm)

end CFSG.GH74.Generic.BProg.B3.S3T2A7
