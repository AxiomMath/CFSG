module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Preamble
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineNineOneHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.QSetTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenAssembly
import CFSG.CGT.PushingUpLit.BHS6.NestedBasic
import CFSG.CGT.PushingUpLit.TwoKHolds
import CFSG.CGT.T75P.Ctx
import CFSG.CGT.T75P.DecA
import CFSG.CGT.Timmesfeld75.SimpleAssembly
import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J3
import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c
import CFSG.GH74.Generic.S45.LEvSporFacts
import CFSG.GroupTheory.SylowNormalIndex
import CFSG.HardMathSupport.Foote.Coordinator.Downstream
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HSubFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpPrimeCoreLe
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCoreCharacteristic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbedInput
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNine
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockExists
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssembly
import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGTools
import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.Notation
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakModules
import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
import CFSG.Quasithin.H13.A5S1327j
import CFSG.Quasithin.Vol2.Ch10SecD33
import CFSG.Quasithin.Vol2.Ch10SecDClA
import CFSG.Quasithin.Vol2.Ch11SecA11Main
import CFSG.Quasithin.Vol2.Ch11SecSMain
import CFSG.Quasithin.Vol2.Ch11SecSShape2
import CFSG.Quasithin.Vol2.Ch11SecSSym2
import CFSG.Quasithin.Vol2.Ch11SecSSym4
import CFSG.Quasithin.Vol2.Ch11SecSSym5
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
import CFSG.Walter.W67.W2Lemma26A

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.RankThreeUC.AGL81C



theorem twelveTenGen_of_sylow_false
    (h : ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H : Subgroup G),
      TwelveCtx G M p Q H → CFSG.ABGLocalTools.IsSylowOf p Q H → False) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.TwelveTenGen := by
  intro G _ _ M q E H hC p Q hQ
  rw [Set.eq_empty_iff_forall_notMem]
  intro H' hH'
  obtain ⟨Q', -, hQ', hsyl, hH'Q'⟩ :=
    exists_sylow_QSet_H4Star_of_twelveCtx (twelveCtx_of_hypCGen_of_h4 hC hQ hH')
      CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nineNineOneInput_holds
  exact h G M p Q' H' (twelveCtx_of_hypCGen_of_h4 hC hQ' hH'Q') hsyl

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
