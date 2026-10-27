module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def EvenOuterTypedConclusion (τ : StatedLieTag) (n f : ℕ) {X : Type} [Group X]
    (P : Subgroup X) : Prop :=
  (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
      Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f' ∧
      (τ' = .PSL → n' = 4 → τ = .PSL ∧ n = 4 ∧ f = 2 * f')) ∨
    Nonempty (P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 6)) ∨
    Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSU 3 3 1

@[expose] def EvenOuterTypedFamilyInput (τ : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f →
    Blueprint.LieModel K τ n 2 f → ∀ α : MulAut K, orderOf α = 2 →
    α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P → EvenOuterTypedConclusion τ n f P

@[expose] def EvenOuterTypedInput : Prop :=
  ∀ (K : Type) [Group K] (τ : StatedLieTag) (n f : ℕ), StatedLieAdmissible τ n 2 f →
    Blueprint.LieModel K τ n 2 f → ∀ α : MulAut K, orderOf α = 2 →
    α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P → EvenOuterTypedConclusion τ n f P

theorem evenOuterTypedInput_of_families (h : ∀ τ, EvenOuterTypedFamilyInput τ) :
    EvenOuterTypedInput :=
  fun K _ τ n f hadm hm => h τ K n f hadm hm

theorem evenOuterTypedFamilyInput_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n f : ℕ, ¬ StatedLieAdmissible τ n 2 f) : EvenOuterTypedFamilyInput τ :=
  fun _ _ n f hadm => absurd hadm (hτ n f)

theorem EvenOuterTypedConclusion.of_ne {τ : StatedLieTag} {n f : ℕ} {X : Type} [Group X]
    {P : Subgroup X} {τ' : StatedLieTag} {n' f' : ℕ} (hadm : StatedLieAdmissible τ' n' 2 f')
    (hm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f') (hne : τ' ≠ .PSL ∨ n' ≠ 4) :
    EvenOuterTypedConclusion τ n f P :=
  Or.inl ⟨τ', n', f', hadm, hm, fun h1 h2 => by
    rcases hne with h | h
    · exact absurd h1 h
    · exact absurd h2 h⟩

theorem evenOuterTypedFamilyInput_POmegaOdd : EvenOuterTypedFamilyInput .POmegaOdd :=
  evenOuterTypedFamilyInput_of_not_admissible fun _ _ hadm => hadm.2.2.2 rfl

theorem evenOuterTypedFamilyInput_twistedG2 : EvenOuterTypedFamilyInput .twistedG2 :=
  evenOuterTypedFamilyInput_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

end CFSG.ComponentClassification.CatFC
