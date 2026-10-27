module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14 (HypCGen)

variable {G : Type} [Group G] [Finite G]

def twelveCtx_of_hypCGen_of_h4 {M : Subgroup G} {q p : ℕ} {E H H' Q : Subgroup G}
    (hC : HypCGen G M q E H) (hQ : Q ∈ QSet M p) (hH : H' ∈ H4StarFam p M Q) :
    TwelveCtx G M p Q H' where
  cstar := hC.cstar
  maxLocal := hC.maxLocal
  sigma_nonempty := hC.sigma_nonempty
  mem_QSet := hQ
  mem_H4Star := hH

@[expose] def TwelveTenFinalStep (M H Q : Subgroup G) (p : ℕ) : Prop :=
  ∃ D : Subgroup G, IsThreeOnePlusTwo ↥D ∧ D ≤ Q ∧
    ∀ x : G, x ∈ kSub p M H ⊓ Subgroup.normalizer (D : Set G) → x ∉ M →
      7 ∣ Nat.card (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
