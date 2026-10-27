module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFrontier
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FinalSmall
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.B
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Final
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22Three
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi24Prime
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HN
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Ly
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.M
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McL
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Suz
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Th
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Normal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2.Tits

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.HardMathSupport.Cooperstein.Coordinator

set_option linter.unusedSectionVars false

theorem ffModuleTheorem_of_exceptionalRest
    (hERest : CoopersteinNoFFExceptionalRest) :
    FFModuleTheorem :=
  ffModuleTheorem_of
    (FFSporadic.gf2NoFFSporadic_of_each
      FFSporadic.gf2NoFFSporadicFor_J3
      FFSporadic.gf2NoFFSporadicFor_Co1
      FFSporadic.gf2NoFFSporadicFor_Co2
      FFSporadic.gf2NoFFSporadicFor_Co3
      FFSporadic.gf2NoFFSporadicFor_Fi22
      FFSporadic.gf2NoFFSporadicFor_Fi23
      FFSporadic.gf2NoFFSporadicFor_Fi24Prime
      FFSporadic.gf2NoFFSporadicFor_McL
      FFSporadic.gf2NoFFSporadicFor_Suz
      FFSporadic.gf2NoFFSporadicFor_ONan
      FFSporadic.gf2NoFFSporadicFor_HN
      FFSporadic.gf2NoFFSporadicFor_Ly
      FFSporadic.gf2NoFFSporadicFor_Th
      FFSporadic.gf2NoFFSporadicFor_B
      FFSporadic.gf2NoFFSporadicFor_M)
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOdd
    (coopersteinNoFFExceptional_of_rest hERest)

end CFSG.AGLEmbeddingD2.Tits
