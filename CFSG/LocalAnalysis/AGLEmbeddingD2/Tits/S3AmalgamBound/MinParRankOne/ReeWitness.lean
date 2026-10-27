module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4Group
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHAltSevenThreePlane
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem borel_le_reeLocalParabolic (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedBorel K a ≤ F4.reeLocalParabolic K a j :=
  reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j

theorem canonicalRep_mem_reeLocalParabolic (j : Fin F4.fixedOrbitCount) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈
      F4.reeLocalParabolic K a j :=
  canonicalRep_fixedOrbitElement_mem_reeGamma_inf j

theorem rankOneGroupOne_le_reeLocalParabolic (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
  rw [rankOneGroupOne, Subgroup.closure_le]
  rintro g ((hg | hT) | rfl)
  · exact borel_le_reeLocalParabolic _
      (reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ hg))
  · exact borel_le_reeLocalParabolic _ (reeFixedTorus_le_reeFixedBorel (rankOneTorusOne_le hK hT))
  · exact canonicalRep_mem_reeLocalParabolic _

theorem rankOneGroupTwo_le_reeLocalParabolic (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupTwo K a ≤ F4.reeLocalParabolic K a ⟨1, by decide⟩ := by
  rw [rankOneGroupTwo, Subgroup.closure_le]
  rintro g ((hg | hT) | rfl)
  · exact borel_le_reeLocalParabolic _
      (reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ hg))
  · exact borel_le_reeLocalParabolic _ (reeFixedTorus_le_reeFixedBorel (rankOneTorusTwo_le hK hT))
  · exact canonicalRep_mem_reeLocalParabolic _

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree
