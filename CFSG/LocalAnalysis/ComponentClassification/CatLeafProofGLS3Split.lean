module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def GLS3OddFamilyInput (τ : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] (n p f : ℕ), p.Prime → p ≠ 2 →
    StatedLieAdmissible τ n p f → Blueprint.LieModel J τ n p f →
    ∀ α : MulAut J, orderOf α = 2 → ∀ K : Subgroup (fixedSubgroup α), IsComponent K →
      (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' p f' ∧
          Blueprint.LieModel (K ⧸ center K) τ' n' p f') ∨
        (p = 3 ∧ Blueprint.LieModel J .G2 0 3 1 ∧ α ∉ (MulAut.conj : J →* MulAut J).range ∧
          Blueprint.LieModel K .PSL 2 2 3)

theorem gls3OddLieAutComponentsInput_of_families (h : ∀ τ, GLS3OddFamilyInput τ) :
    GLS3OddLieAutComponentsInput :=
  fun J _ τ n p f hp hp2 hadm hm => h τ J n p f hp hp2 hadm hm

theorem gls3OddFamilyInput_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n p f : ℕ, p ≠ 2 → ¬ StatedLieAdmissible τ n p f) : GLS3OddFamilyInput τ :=
  fun _ _ n p f _ hp2 hadm => absurd hadm (hτ n p f hp2)

theorem gls3OddFamilyInput_twistedB2 : GLS3OddFamilyInput .twistedB2 :=
  gls3OddFamilyInput_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

theorem gls3OddFamilyInput_twistedF4 : GLS3OddFamilyInput .twistedF4 :=
  gls3OddFamilyInput_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

theorem gls3OddFamilyInput_Tits : GLS3OddFamilyInput .Tits :=
  gls3OddFamilyInput_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

@[expose] def EvenOuterFamilyInput (τ : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f →
    Blueprint.LieModel K τ n 2 f → ∀ α : MulAut K, orderOf α = 2 →
    α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P →
      (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
          Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f') ∨
        Nonempty (P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 6)) ∨
        Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSU 3 3 1

theorem evenLieOuterTwoComponentsInput_of_families (h : ∀ τ, EvenOuterFamilyInput τ) :
    EvenLieOuterTwoComponentsInput :=
  fun K _ τ n f hadm hm => h τ K n f hadm hm

theorem evenOuterFamilyInput_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n f : ℕ, ¬ StatedLieAdmissible τ n 2 f) : EvenOuterFamilyInput τ :=
  fun _ _ n f hadm => absurd hadm (hτ n f)

theorem evenOuterFamilyInput_POmegaOdd : EvenOuterFamilyInput .POmegaOdd :=
  evenOuterFamilyInput_of_not_admissible fun _ _ hadm => hadm.2.2.2 rfl

theorem evenOuterFamilyInput_twistedG2 : EvenOuterFamilyInput .twistedG2 :=
  evenOuterFamilyInput_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

end CFSG.ComponentClassification.CatLeafProof
