module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Transfer
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
public import CFSG.GH74.GLS.Stage2.OddAut.LangR

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
  CFSG.GH74.GLS.Stage2.OddAut

section Small


@[expose] def ThreeD4FixedNF : Prop :=
  ∀ (p f : ℕ), p.Prime → 5 ≤ p → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1 →
      ∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧
        MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ

@[expose] def GraphShintaniNF : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ≤ ringChar K →
    ∀ x ∈ inndiagGroup Tag.D4 K, (x * (d4P K)⁻¹) ^ 3 = 1 →
      ∃ v ∈ inndiagGroup Tag.D4 K, ∃ t : ↥(adjointGroup Tag.D4 K),
        d4Graph K 1 t = t ∧ t ^ 3 = 1 ∧
          v * (x * (d4P K)⁻¹) * v⁻¹ = (t : ModGL Tag.D4 K) * (d4P K)⁻¹

end Small

section Large


@[expose] def G2ThreeClass : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ≤ ringChar K →
    ∀ t : ↥(adjointGroup Tag.D4 K), d4Graph K 1 t = t → t ^ 3 = 1 → t ≠ 1 →
      ∃ (w : ↥(adjointGroup Tag.D4 K)) (A : SL2 K), d4Graph K 1 w = w ∧ A ^ 3 = 1 ∧ A ≠ 1 ∧
        (w * t * w⁻¹ = sl2At K ⟨2, by decide⟩ A ∨ w * t * w⁻¹ = sl2Short K A)

end Large

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd
