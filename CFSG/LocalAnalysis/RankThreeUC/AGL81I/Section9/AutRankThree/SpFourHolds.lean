module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Defs
public import Certificates.Certificate1022
public import Certificates.Certificate7059
public import Certificates.Certificate7023
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate110
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate8
public import Certificates.Certificate9
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.SpFourOf
import CFSG.RankThree.SubgroupLists.MitchellQuasisimple
import CFSG.RankThree.SubgroupLists.MitchellPartThreeProof
import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
import CFSG.RankThree.SubgroupLists.SymplecticFischerOrth
import CFSG.RankThree.SubgroupLists.SymplecticFischerUnitary
import CFSG.RankThree.SubgroupLists.SymplecticFischerRefl
public import CFSG.Certificates.Kernel.Th.Gen.Dce
public import CFSG.Certificates.Kernel.Th.Gen.DceStruct
public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Gen.Gen
public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Certificates.Kernel.Th.Gen.Sylow3
public import CFSG.Certificates.Kernel.Th.Gen.Sylow5
public import CFSG.Certificates.Kernel.Th.Gen.Sylow7
public import CFSG.Certificates.Kernel.Th.S.HswTC
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.KernelInputsBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.RankThree.SubgroupLists

theorem spFourQuasisimpleThreeDvd_holds :
    SpFourQuasisimpleThreeDvd := by
  intro r _ hr2 Y hY hq
  rcases mitchell_quasisimple_sp4_of mitchellPartThree_holds fischerSpClique fischerOrthClique
    fischerSpCard fischerOrthCard fischerUnitaryCard fischerReflectionCard hr2 hY hq with
    e | e | e | e | e | ⟨-, -, ⟨e⟩⟩
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_statedSp_two _
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · have : Fact (1 < 5) := ⟨by norm_num⟩
    exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · exact three_dvd_card_of_quotient_center_alternatingGroup_seven e

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
