module

public import CFSG.GH74.Generic.GKFLinear
public import CFSG.GH74.Generic.GKFSymp
public import CFSG.GH74.Generic.GKFUnitary
public import CFSG.GH74.Generic.GKFAlt
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.GH74.Generic.GKFSporadic
public import CFSG.GH74.Generic.GKFRank3D4
public import CFSG.GH74.Generic.GKFMcL
public import CFSG.GH74.Generic.GKFLy

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.TBLit in
theorem genericKnownFacts_of_griess_bridges
    (hGA : GriessMultipliersAllModels)
    (hB : CFSG.TauCetiBridge.TypewiseBridges) : GenericKnownFacts where
  alt_cover := by
    intro n hn7 hn11 K _ _ hK h2 he
    obtain ⟨e⟩ := he
    exact alt_cover_of_central_kernel (by omega) hK h2 e
  psl2_cover := by
    intro p f hp hp2 K _ _ hK h2 hm
    exact psl2_cover_of_griess hGA hp hp2 hK h2
      (models_of_blueprint_of_ne_zero (by norm_num) hm)
  psp4_cover := by
    intro p f hp hp2 K _ _ hK h2 hm
    exact psp4_cover_of_griess hGA hp hp2 hK h2
      (models_of_blueprint_of_ne_zero (by norm_num) hm)
  psl4_cover := by
    intro K _ _ hK h2 F _ _ hodd e
    exact psl4_cover_of_griess hGA hK h2 F hodd e
  psu4_cover := by
    intro K _ _ hK h2 F _ _ q hF hq e
    exact psu4_cover_of_griess hGA hK h2 F q hF hq e
  noTwoCover_psl3 := by
    intro p f hp hp2 S _ hm
    exact noTwoCover_psl3_of_griess hGA hp2 (models_of_blueprint_of_ne_zero (by norm_num) hm)
  noTwoCover_psu3 := by
    intro p f hp hp2 S _ hm
    exact noTwoCover_psu3_of_griess hGA (models_of_blueprint_of_ne_zero (by norm_num) hm)
  noTwoCover_g2 := by
    intro p f hp hp2 S _ hm
    exact noTwoCover_g2_of_griess hGA hp2
      (models_of_blueprint_exceptional hB hp hp2 (Or.inl rfl) hm)
  noTwoCover_3D4 := by
    intro p f hp hp2 S _ hm
    exact noTwoCover_3D4_of_griess hGA
      (models_of_blueprint_exceptional hB hp hp2 (Or.inr (Or.inl rfl)) hm)
  noTwoCover_ree := by
    intro f S _ hm
    exact noTwoCover_ree_of_griess hGA
      (models_of_blueprint_exceptional hB Nat.prime_three (by norm_num)
        (Or.inr (Or.inr rfl)) hm)
  noTwoCover_J1 := noTwoCover_J1_of_walter
  noTwoCover_McL := fun S _ h => coverGen4_McL S h
  noTwoCover_Ly := fun S _ h => coverGen4_Ly S h
  noTwoCover_psl5 := by
    intro p f hp hq S _ hm
    exact noTwoCover_psl5_of_griess hGA (models_of_blueprint_of_ne_zero (by norm_num) hm)
  noTwoCover_psu5 := by
    intro p f hp hq S _ hm
    exact noTwoCover_psu5_of_griess hGA (models_of_blueprint_of_ne_zero (by norm_num) hm)
  rank_3D4 := by
    intro p f hp hp2 S _ _ hm
    exact rank_3D4_of_lieModel hp hp2 hm

end CFSG.GH74.Generic
