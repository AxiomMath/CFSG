module

public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge
public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
import CFSG.CGT.PushingUpLit.SYMB.FiveRigid
import CFSG.CGT.PushingUpLit.BHS7.PushUpPerfectTwo
import CFSG.RankThree.PartOne.KEXC.SL2Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

theorem bhsLocalCStar_proved :
    CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar :=
  CFSG.CGT.PushingUpLit.SYMB.bhsLocalCStar_of_restIH
    ⟨CFSG.RankThree.PartOne.KEXC.sl2EvenMultiplierTrivial_holds,
      CFSG.CGT.PushingUpLit.BHS7.pushUpPerfectTwo_holds,
      CFSG.CGT.PushingUpLit.SYMB.threeEightSymmIH_proved⟩

theorem aschbacherLocalFactorization_proved :
    CFSG.CGT.PushingUpLit.AschbacherLocalFactorization :=
  CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs bhsLocalCStar_proved

theorem aschbacherLocalCGTBlock_proved :
    AschbacherLocalCGTBlock :=
  aschbacherLocalCGTBlock_of_factorization aschbacherLocalFactorization_proved

end CFSG.LocalAnalysis.RankThreeTheoremC
