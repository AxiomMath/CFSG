module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.Pairing504
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.QuasisimpleCent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

theorem pairing_of_dichotomy {X : Type} [Group X] [Finite X]
    (hdich : ∀ c : X, orderOf c = 3 →
      CFSG.IsQuasisimple (Subgroup.centralizer ({c} : Set X)) ∨
        Nat.card (Subgroup.centralizer ({c} : Set X)) = 504)
    {D : Subgroup X} {c d : X} {K : Subgroup X} (h : InnerConfig424 X D c d K) :
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 1)) := by
  have hc3 : c ^ 3 = 1 := h.maximal.prop.2 c h.c_mem
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 h.c_ne_one
  have hz : (⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({c} : Set X)) ∈ Subgroup.center (Subgroup.centralizer ({c} : Set X)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hzo : orderOf (⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({c} : Set X)) = 3 := by
    rw [← hord, ← Subgroup.orderOf_coe]
  obtain ⟨hKC, hK'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsIn
  let e0 := Subgroup.subgroupOfEquivOfLe hKC
  let eq : (K.subgroupOf (Subgroup.centralizer ({c} : Set X)) ⧸
      aschbacherSolvableCore 3 (K.subgroupOf (Subgroup.centralizer ({c} : Set X)))) ≃*
      (K ⧸ aschbacherSolvableCore 3 K) :=
    QuotientGroup.congr _ _ e0 (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e0)
  have hT' := Sec11.isType424_of_mulEquiv eq h.isType424
  rcases hdich c hord with hq | h504
  · exact (false_of_mem_thetaComponents_of_quasisimple hq hz hzo hK' hT').elim
  · obtain ⟨f⟩ := nonempty_equiv_projSL_three_two_of_card_504 h504 hz hzo hK' hT'
    exact ⟨eq.symm.trans f⟩

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
