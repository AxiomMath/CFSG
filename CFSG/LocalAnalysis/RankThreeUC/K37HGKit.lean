module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralSetup
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Split
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central
  (centGenI_le_rankThreeGamma le_rankThreeGamma_of_forall_seitzHyperGamma)

variable {X : Type} [Group X] [Finite X]

theorem k37G_isPGroup_center {K E S : Subgroup X} (h : K37Setting X K E S) :
    IsPGroup 3 (Subgroup.center ↥K) :=
  CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot Nat.prime_three
    h.core

theorem k37G_isQuasisimple_open {K E S : Subgroup X} (h : K37Setting X K E S) :
    CFSG.Open.IsQuasisimple ↥K :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1.mp h.quasi

theorem k37G_le_normalizer {K E S : Subgroup X} (h : K37Setting X K E S) :
    E ≤ Subgroup.normalizer (K : Set X) := by
  haveI := h.normal
  rw [Subgroup.normalizer_eq_top_iff.2 h.normal]
  exact le_top

theorem k37G_false_of_le_centGenI {K E S : Subgroup X} (h : K37Setting X K E S)
    (hgen : K ≤ GL83.CompFam.centGenI 3 E K) : False :=
  h.not_le (hgen.trans (centGenI_le_rankThreeGamma h.elem h.card K))

theorem k37G_false_of_forall_seitzHyperGamma {K E S : Subgroup X} (h : K37Setting X K E S)
    (hA : ∀ A : Subgroup (MulAut ↥K), CFSG.Open.IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      CFSG.LieType.Seitz.seitzHyperGamma 3 A = ⊤) : False :=
  h.not_le (le_rankThreeGamma_of_forall_seitzHyperGamma h.elem h.card (k37G_le_normalizer h) hA)

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
