module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Lang.TwE6Step3.Glue
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenFixedRootData
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3 CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

theorem tw6SixZetaPow_torusRootKernel {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) (z : Fin Tag.E6.rank → ZMod p) :
    torusRootKernel (rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val)) =
      CFSG.RankThree.E6.rootKernel z := by
  rw [torusRootKernel_rootDiagUnit, rootCharKernel_zetaPow hζ]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
