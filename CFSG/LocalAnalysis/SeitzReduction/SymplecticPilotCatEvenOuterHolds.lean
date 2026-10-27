module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuterExc

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem catSp2mEvenOuterExact_holds (m : ℕ) : CatSp2mEvenOuterExact m := by
  obtain ⟨hPSL, hPSU, hPSp, hOp, hOm⟩ := catSp2mEvenOuterFamily_classical m
  exact catSp2mEvenOuterExact_of_open_families hPSL hPSU hPSp hOp hOm
    (catSp2mEvenOuterFamily_G2 m) (catSp2mEvenOuterFamily_F4 m) (catSp2mEvenOuterFamily_E6 m)
    (catSp2mEvenOuterFamily_E7 m) (catSp2mEvenOuterFamily_E8 m)
    (catSp2mEvenOuterFamily_twistedE6 m) (catSp2mEvenOuterFamily_trialityD4 m)

theorem catSp2mEvenOuter_holds (m : ℕ) : CatSp2mEvenOuter m :=
  catSp2mEvenOuter_of_exact (catSp2mEvenOuterExact_holds m)

end CFSG.SeitzReduction.SymplecticPilot
