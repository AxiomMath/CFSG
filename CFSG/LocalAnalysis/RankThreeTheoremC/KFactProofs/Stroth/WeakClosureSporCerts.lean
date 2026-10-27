module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporFinal
public import Certificates.Certificate41505
public import Certificates.Certificate41506
public import Certificates.Certificate41507
public import Certificates.Certificate41508

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.SectionRank.Native

theorem suz_five_rot_check :
    (ops3 64).squareCheck suzFiveRot = true :=
  Certificates.certificate41505

theorem th_seven_rot_check :
    (ops2 248).squareCheck thSevenRot = true :=
  Certificates.certificate41506

theorem b_seven_rot_check :
    ∃ x y h k : CFSG.Blueprint.NativeSporadic.B,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.RotSevenData x y h k :=
  Certificates.certificate41507

theorem eleven_rot_check : elevenRotCheck () = true :=
  Certificates.certificate41508

section Assembly


theorem wcSporadic_holds : WCSporadic :=
  wcSporadic_of_residues suz_five_rot_check th_seven_rot_check b_seven_rot_check eleven_rot_check

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
