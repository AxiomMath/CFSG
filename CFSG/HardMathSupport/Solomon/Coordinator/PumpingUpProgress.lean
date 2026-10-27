module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporProgress
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.YS07
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Classical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SymplecticOrthogonalComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SuzukiReeTitsComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Main
public import CFSG.Yardstones.M67c2c3e09a6b.Definitions

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem input14_20_7_of_open (hBM : NoOrderSixtyFiveBM) (hSS : Fi22LieSSC) (hUn : Fi22LieUnipC)
    (hOut : Fi22LieOuterC) : CFSG.HardMathSupport.Solomon.LocalBalance.Input14_20_7 := by
  have hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group) :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOutS := CFSG.AGLEmbedding.not_dvd_card_outer_sporadic_of hbr
    CFSG.Milestones.fam_m_simplicity
  exact input14_20_7_of_comp_BM hbr hOutS hBM lieOrderBridge_holds hSS hUn hOut

theorem pumpingUpFacts_of_open
    (h33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33TypeSameField)
    (hBM : NoOrderSixtyFiveBM) (hSS : Fi22LieSSC) (hUn : Fi22LieUnipC) (hOut : Fi22LieOuterC)
    (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name) (h1 : LieDownChev) (h2 : LieNoHatSix) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  ⟨h33, input14_20_7_of_open hBM hSS hUn hOut, gapFinalPumpup_of_openSpor hR h1 h2⟩

theorem pumpingUpFacts_of_lieComp
    (h33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33TypeSameField)
    (hBM : NoOrderSixtyFiveBM) (hSS : Fi22LieSSC) (hUn : Fi22LieUnipC) (hOut : Fi22LieOuterC)
    (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name) (hLie : LieComp.LieComp) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  pumpingUpFacts_of_open h33 hBM hSS hUn hOut hR
    (LieComp.lieDownChev_of_lieComp hLie lieOrderBridge_holds inputONGroup_holds)
    (LieComp.lieNoHatSix_of_lieComp hLie)

theorem pumpingUpFacts_of_lieComps
    (h33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33TypeSameField)
    (hBM : NoOrderSixtyFiveBM) (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name)
    (hLie : LieComp.LieComp) (h5 : ∀ F, LieComp.LieCompsOn 5 F)
    (hQ5 : YS08.LieQ.LieQConstrainedInner 5) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  pumpingUpFacts_of_lieComp h33 hBM (LieComp.fi22LieSSC_of_lieCompsOn lieOrderBridge_holds h5)
    (LieComp.fi22LieUnipC_of_lieQ hQ5) (LieComp.fi22LieOuterC_of_lieCompsOn lieOrderBridge_holds h5)
    hR hLie

theorem pumpingUpFacts_of_residuals
    (h33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33TypeSameField)
    (hBM : NoOrderSixtyFiveBM) (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name)
    (hQ3 : YS08.LieQ.LieQConstrainedInner 3) (hQ5 : YS08.LieQ.LieQConstrainedInner 5)
    (hD4 : LieComp.D4OuterExport) (hres : LieComp.ExcRationalLieTypes)
    (hout : LieComp.TrialityOuterExport) (hchar3 : LieComp.ExcChar3Export)
    (hExc5 : LieComp.LieCompsOn 5 .exceptional) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  pumpingUpFacts_of_lieComps h33 hBM hR
    (LieComp.lieComp_of_classical lieOrderBridge_holds hQ3 hD4
        (LieComp.lieCompOn_exceptional hres hout hchar3)
        (LieComp.lieCompOn_suzukiReeTits (LieComp.reeG2Char3Export_of_lieQ lieOrderBridge_holds hQ3)))
    (fun F => by
      cases F
      · exact LieComp.lieCompsOn_linearUnitary Nat.prime_five (by decide)
      · exact LieComp.lieCompsOn_symplecticOrthogonal Nat.prime_five le_rfl
      · exact hExc5
      · exact LieComp.lieCompsOn_suzukiReeTits Nat.prime_five le_rfl)
    hQ5

end CFSG.HardMathSupport.Solomon.Coordinator
