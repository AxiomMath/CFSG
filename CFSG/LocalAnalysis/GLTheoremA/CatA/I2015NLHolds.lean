module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTD4NE
public import Certificates.Certificate5133
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate14953
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLLinear
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLDerived
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLSymplectic
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLSymplecticB
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLOmega
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLOmegaMinus
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLChev
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTwE6B
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTwE6C
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTriD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLSuzuki
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTwF4N
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLG2NB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

section Assembly

set_option linter.unusedSectionVars false


theorem i2015NLFamilies_holds : I2015NLFamilies where
  linear := i2015NLOnLinear_holds
  unitary := i2015NLOnUnitary_holds
  symplectic := i2015NLOnSymplectic_holds
  resSp4 := i2015NLResSp4_holds
  d3 := i2015NLOnD3_holds
  omegaPlus := i2015NLOnOmegaPlus_holds
  twD2 := i2015NLOnTwD2_holds
  twD3 := i2015NLOnTwD3_holds
  omegaMinus := i2015NLOnOmegaMinus_holds
  g2 := i2015NLOnG2_holds
  resG2 := i2015NLResG2_holds
  f4 := i2015NLOnF4_holds
  e := i2015NLOnE_holds
  twE6 := i2015NLOnTwE6_holds
  resTwE6 := i2015NLResTwE6_holds
  triD4 := i2015NLOnTriD4_holds
  suzuki := i2015NLOnSuzuki_holds
  twF4 := i2015NLOnTwF4_holds
  resTwF4 := i2015NLResTwF4_holds
  derived := i2015NLOnDerived_holds
  td4Outer := i2015NLOnTD4Outer_holds

theorem i2015NoParabolicFact_holds : I2015NoParabolicFact :=
  i2015NoParabolicFact_of_families i2015NLFamilies_holds

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
