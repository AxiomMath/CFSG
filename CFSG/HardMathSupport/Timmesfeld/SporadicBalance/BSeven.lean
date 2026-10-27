module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenC0
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCo2Chain
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElems
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicGammaPairs
public import Certificates.Certificate6032
public import Certificates.Certificate6033
public import CFSG.Monster.Existence.StdOdd.Defs
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Monster.B.Classical.E6AdjointGroup
import Certificates.Kernel.Misc.E6StdSlp
public import Certificates.Certificate6036
public import Certificates.Certificate6037
public import Certificates.Certificate10004
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.Monster.Existence.StdOdd.Cert.Base
public import CFSG.Monster.GMS.BabyReduce
public import CFSG.Monster.GMS.Facts.Section4
public import Certificates.Certificate10004Base

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.LocalTwo

section Final

theorem exists_census_B_seven :
    ∃ p : NativeSporadic.B, orderOf p = 7 ∧
      ∀ x : NativeSporadic.B, orderOf x = 7 → IsConj x p := by
  obtain ⟨x, y, h, k, D⟩ := Certificates.certificate41507
  exact exists_census_B_seven_of_rot D

theorem oPrimeCoreLeTwoAt_B_seven : OPrimeCoreLeTwoAt 7 (NativeSporadic.Carrier .B) :=
  card_gLAPPrimeCoreOf_B_le_two c0Seven_of_certificate co2Seven_of_certificate exists_census_B_seven
    bSeven_elements

end Final

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
