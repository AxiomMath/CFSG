module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltUtil
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.SchreierLemmas.MooreCosets

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Sporadic.SchreierLemmas

theorem zpowers_normal_of_mem_center {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G) :
    (Subgroup.zpowers z).Normal := by
  refine ⟨fun a ha g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hc : g * z ^ k = z ^ k * g :=
    ((Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hz k)) g)
  rw [hc, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers z k

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
