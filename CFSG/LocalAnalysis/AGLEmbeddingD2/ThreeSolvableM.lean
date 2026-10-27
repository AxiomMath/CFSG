module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

namespace D2Escape

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem deltaTwo_cases (h : D2Escape 3 P M A H R) (hglob : D2Global G)
    (h3 : 3 ∈ GLBBetaFour G) :
    GLBStronglyEmbedded 3 M ∨ (Group.IsSolvable M ∧ ∀ x ∈ M, orderOf x = 3 →
      3 ≤ Open.pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G)) →
      Subgroup.centralizer ({x} : Set G) ≤ M) :=
  hglob.deltaTwo h3 P M h.maxTwoLocal_M h.sylow_le

end D2Escape

theorem no_component_of_isSolvable {G : Type*} [Group G] {M : Subgroup G}
    (hM : Group.IsSolvable M) (Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : ¬ IsComponentOf Lb ⊤ := by
  rintro ⟨-, -, hperf, hsimple⟩
  have : Nontrivial (↥Lb ⧸ Subgroup.center ↥Lb) := hsimple.toNontrivial
  have : Nontrivial ↥Lb := (QuotientGroup.mk_surjective (s := Subgroup.center ↥Lb)).nontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Lb).ne hperf

end CFSG.AGLEmbeddingD2
