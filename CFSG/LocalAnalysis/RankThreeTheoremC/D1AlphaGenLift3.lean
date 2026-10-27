module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlpha
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem le_of_exists_genLift (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} [K.Normal]
    (hgen : ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ IsElemAbelian p A ∧
      3 ≤ Open.pRank p A ∧ Subgroup.closure {k : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (k : X) * f⁻¹ = k} = ⊤) :
    K ≤ X₀ := by
  obtain ⟨A, hAR, hA, hA3, hclos⟩ := hgen
  intro x hx
  have hxmem : (⟨x, hx⟩ : K) ∈ Subgroup.closure {k : K | ∃ f ∈ A,
      f ∉ Subgroup.centralizer (K : Set X) ∧ f * (k : X) * f⁻¹ = k} :=
    hclos ▸ Subgroup.mem_top _
  refine (Subgroup.closure_le (X₀.comap K.subtype)).mpr ?_ hxmem
  rintro k ⟨f, hfA, hf, hk⟩
  refine h.mem_of_conjNormal_apply_eq hz hzp hAR hA hA3 hfA (fun h1 => hf ?_) (Subtype.ext hk)
  rw [← ker_conjNormal_eq_centralizer K]
  exact h1

end ReducedNongeneration

end CFSG.AGLEmbedding

