module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Chevalley.SteinbergBNF4Sym
public import CFSG.RankThree.PartOne.KA5L.Chain
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.RankThree.Classical2 CFSG.Open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups Pointwise commutatorElement


variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

theorem rootChar_pow_apply (b : Fin Tag.E7.rank → Lˣ) (n : ℕ) (u : Fin Tag.E7.rank → ℤ) :
    rootChar (b ^ n) u = rootChar b u ^ n := by
  induction n with
  | zero => simp [CTTorus.rootChar_one]
  | succ n ih => rw [pow_succ, CTTorus.rootChar_mul, ih, pow_succ]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
