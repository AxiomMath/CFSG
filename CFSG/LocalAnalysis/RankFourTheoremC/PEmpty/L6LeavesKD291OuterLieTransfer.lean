module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p : ℕ}

theorem pRank_fixed_le_of_intertwine (hp : 1 < p) {G H : Type} [Group G] [Group H] [Finite G]
    [Finite H] (v : G ≃* H) (α : MulAut G) (β : MulAut H) (hβ : ∀ x, β (v x) = v (α x)) :
    CFSG.Open.pRank p (fixedSubgroup β) ≤ CFSG.Open.pRank p (fixedSubgroup α) := by
  refine (CFSG.SectionRank.pRank_le_map hp v.symm.toMonoidHom v.symm.injective
    (fixedSubgroup β)).trans (CFSG.SectionRank.pRank_mono hp ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hy' : β y = y := hy
  change α (v.symm y) = v.symm y
  apply v.injective
  rw [← hβ, v.apply_symm_apply, hy']

theorem pRank_top_le_pRank_fixed_of_embedding (hp : 1 < p) {A G : Type} [Group A] [Group G]
    [Finite A] [Finite G] (ι : A →* G) (hι : Function.Injective ι) (α : MulAut G)
    (hfix : ∀ a, α (ι a) = ι a) :
    CFSG.Open.pRank p (⊤ : Subgroup A) ≤ CFSG.Open.pRank p (fixedSubgroup α) := by
  refine (CFSG.SectionRank.pRank_le_map hp ι hι ⊤).trans (CFSG.SectionRank.pRank_mono hp ?_)
  rintro _ ⟨a, -, rfl⟩
  exact hfix a

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
