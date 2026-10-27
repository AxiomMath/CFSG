module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporMEleven
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporMathieu
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporJ2ON
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporCo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporCo1
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporFischer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporHN
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLy
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporSuz
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporTh
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporM
import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicBMData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.SectionRank CFSG.SectionRank.Native

theorem wcSporadic_of_residues
    (hSuz : (ops3 64).squareCheck suzFiveRot = true)
    (hTh : (ops2 248).squareCheck thSevenRot = true)
    (hB : ∃ x y h k : CFSG.Blueprint.NativeSporadic.B,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.RotSevenData x y h k)
    (hM : elevenRotCheck () = true) : WCSporadic := by
  refine wcSporadic_of_forall fun s _ => ?_
  obtain ⟨-, hcardM, -⟩ := CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds
  have h3M : ¬ 11 ^ 3 ∣ Nat.card (Carrier .M) := by
    rw [hcardM]
    norm_num [monsterOrder]
  haveI : IsSimpleGroup (Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨eM⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := Carrier .M) (MulEquiv.refl _)
  have hMrot : RotationDatum 11 (Carrier .M) :=
    rotationDatum_of_mulEquiv eM (rotationDatum_Gmat_eleven hM)
  cases s
  · exact wcSporadicAt_M11
  · exact wcSporadicAt_M12
  · exact wcSporadicAt_M22
  · exact wcSporadicAt_M23
  · exact wcSporadicAt_M24
  · exact wcSporadicAt_J1
  · exact wcSporadicAt_J2
  · exact wcSporadicAt_J3
  · exact wcSporadicAt_J4
  · exact wcSporadicAt_HS
  · exact wcSporadicAt_McL
  · exact wcSporadicAt_He
  · exact wcSporadicAt_Ru
  · exact wcSporadicAt_Suz_of_five (wcOn_Suz_five_of_check hSuz)
  · exact wcSporadicAt_ON
  · exact wcSporadicAt_Co1
  · exact wcSporadicAt_Co2
  · exact wcSporadicAt_Co3
  · exact wcSporadicAt_Fi22
  · exact wcSporadicAt_Fi23
  · exact wcSporadicAt_Fi24Prime
  · exact wcSporadicAt_HN
  · exact wcSporadicAt_Ly
  · exact wcSporadicAt_Th_of_seven (wcOn_Th_seven_of_check hTh)
  · exact wcSporadicAt_B_of_seven (wcOn_B_seven_of_check hB)
  · exact wcSporadicAt_M_of_eleven (wcOn_eleven_of_rotationDatum hMrot h3M)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
