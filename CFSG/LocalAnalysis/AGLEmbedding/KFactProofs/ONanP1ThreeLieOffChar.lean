module

public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Constrained
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.Basic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem le_of_hyperGen (h : ReducedNongeneration p X R X₀) {K E : Subgroup X}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hER : E ≤ R) (hgen : HyperGen p K E) :
    K ≤ X₀ := by
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro k ⟨-, F, hFE, hrel, hF⟩
  exact h.hyperplane_le E hE hcard hER F hFE hrel (Subgroup.mem_centralizer_iff.2 hF)

theorem false_of_hyperGen (h : ReducedNongeneration p X R X₀) {K E : Subgroup X}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hER : E ≤ R)
    (hEN : E ≤ (K ⊔ (R : Subgroup X)).normalCore) (hgen : HyperGen p K E) : False := by
  have hKX : K ≤ X₀ := h.le_of_hyperGen hE hcard hER hgen
  have hNX : (K ⊔ (R : Subgroup X)).normalCore ≤ X₀ :=
    (Subgroup.normalCore_le _).trans (sup_le hKX h.sylow_le)
  have h2 := h.pRank_le_two_of_normal_le hNX
  have h3 := le_pRank_of_isElemAbelian_of_pow_le_card h.prime hE hEN (n := 3) (by rw [hcard])
  omega

end ReducedNongeneration

end CFSG.AGLEmbedding
