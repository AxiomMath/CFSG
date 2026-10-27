module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Reduction
import CFSG.ClassicalInvolution.OrderForm
import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWitness
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open Subgroup

theorem nativeM11_eq_m11 :
    Blueprint.NativeSporadic.M11 = Assembly.ComponentType.M11 :=
  rfl

theorem nonempty_mulEquiv_m11_of_isSporadic {X : Type} [Group X]
    (h : Blueprint.NativeSporadic.IsSporadic X .M11) :
    Nonempty (X ≃* Assembly.ComponentType.M11) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (MulEquiv.subgroupCongr nativeM11_eq_m11)⟩

theorem milestone_of_partOne_of_oddLieType (hCIT : ClassicalInvolution.PartOne)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hLie : Blueprint.OddLieType G → Assembly.ComponentType.OddLieType G)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) := by
  obtain ⟨hw, hsub⟩ := classicalInvolutionWitness_of_component hz hJ hzJ S hS
  let eF : Open.genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr
      (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnonab)).trans
      Subgroup.topEquiv
  have : IsSimpleGroup (Open.genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : Open.genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  rcases hCIT G hFnonab z hz J hzJ hsub S hS hw trivial with h | h
  · exact Or.inl (hLie ((ClassicalInvolution.oddLieType_congr eF).1 h))
  · exact Or.inr
      (nonempty_mulEquiv_m11_of_isSporadic ((ClassicalInvolution.isSporadic_congr eF).1 h))

end CFSG.ComponentClassification.QuaternionComponent
