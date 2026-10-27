module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecFacts
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

theorem E4Facts.toHyp {G : Type} [Group G] {z : G} {k : Kind} (F : E4Facts G z k) : E4Hyp G z k :=
  ⟨fun B _ _ b hb p X h1 h2 h3 => F.p42 B b hb p X h1 h2 h3, F.two, F.f3, F.uinv⟩

theorem l34DiagClosure_of_cert : L34DiagClosure :=
  fun A _ J _ hJ X hX => Odd87L34Out.diag_closure J hJ X hX

theorem prop_4_3E (h42 : Prop4_2) (hL : Lemma31Narrow) : Prop4_3E :=
  prop_4_3E_of_hyp l34DiagClosure_of_cert
    (fun G _ _ z k _ hctx => (E4Facts.of_leaves h42 hL hctx).toHyp)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
