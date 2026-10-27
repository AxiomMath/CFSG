module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCG2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCInputs
public import CFSG.LieType.Chevalley.ExceptionalChevalleyModelSchreier

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem isSolvable_outer_of_exceptional {G : Type} [Group G] {τ : StatedLieTag} {n p f : ℕ}
    (hτ : τ ∈ Burgoyne.oddExceptionalTags) (hL : LieModel G τ n p f) :
    Group.IsSolvable (Outer G) := by
  by_cases hR : τ = .twistedG2
  · subst hR
    rcases hL with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (LieType.Ree.small_Ree_model_Schreier G p f h).2.1
    · exact absurd h (by decide)
  · have hτ' : τ ∈ chevalleyExceptionalTags := by
      revert hτ hR
      cases τ <;> decide
    exact (LieType.Chevalley.exceptional_Chevalley_model_Schreier G τ p f hτ'
      (GH74.chevalleyExceptionalModel_of_lieModel hτ' hL)).1

theorem burgoynePropC_exceptional (hE3 : BurgoyneExcPropCInput) {X : Type} [Group X] [Finite X]
    (hX : IsM4 X) {τ : StatedLieTag} {n' p' f' : ℕ} (hτ : τ ∈ Burgoyne.oddExceptionalTags)
    (hp2' : p' ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) τ n' p' f') {r : X}
    {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData r R₁ R₂ p n) : False := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  obtain ⟨x, R₁', R₂', hC', -⟩ := exists_propCData_of_socle hsimple hnab
    (isSolvable_outer_of_exceptional hτ hL) (MulEquiv.refl _) hC.orderOf_eq hC.le₁ hC.comp₁
    hC.le₂ hC.comp₂ hC.p_ne_two hC.n_pos hC.iso₁ hC.iso₂ hC.mem
  by_cases hG2 : τ = .G2
  · subst hG2
    exact g2_propC_false hp2' hL hC'
  · exact hE3 _ hsimple hnab τ n' p' f' hτ hG2 hp2' hL x hC'.orderOf_eq R₁' R₂' hC'.le₁ hC'.comp₁
      hC'.le₂ hC'.comp₂ p n hC'.p_ne_two hC'.n_pos hC'.iso₁ hC'.iso₂ hC'.mem

end CFSG.ComponentClassification.Burgoyne.C
