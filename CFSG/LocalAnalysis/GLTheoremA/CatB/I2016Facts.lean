module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def fixSub {Q : Type} [Group Q] (σ : MulAut Q) : Subgroup Q where
  carrier := {g | σ g = g}
  one_mem' := map_one σ
  mul_mem' := fun {a b} ha hb => by
    show σ (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  inv_mem' := fun {a} ha => by
    show σ a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

@[expose] def HasA6Quot {Q : Type} [Group Q] (A : Subgroup Q) : Prop :=
  ∃ (A₀ : Subgroup Q) (S : Type) (_ : Group S) (f : ↥A₀ →* S),
    A₀ ≤ A ∧ catalogIs S S8.isA6 ∧ Function.Surjective f

@[expose] def I2016FactSp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (σ : MulAut Q) (A I T : Subgroup Q),
    CFSG.Open.IsQuasisimple Q → IsPGroup 3 (Subgroup.center Q) →
    catalogIs (Q ⧸ Subgroup.center Q) S8.L89.isSp8of2 →
    σ ^ 3 = 1 → A ≤ fixSub σ → HasA6Quot A →
    CFSG.Open.IsSubnormal I (fixSub σ) → S8.IsTypeWithCenter 3 I S8.isPSp43 1 →
    T ≠ ⊥ → IsPGroup 2 T → T.map σ.toMonoidHom = T →
    A ≤ Subgroup.normalizer (T : Set Q) → False

@[expose] def I2016FactU6 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (σ : MulAut Q) (A I T : Subgroup Q),
    CFSG.Open.IsQuasisimple Q → catalogIs (Q ⧸ Subgroup.center Q) S8.L89.isU6of2 →
    σ ^ 3 = 1 → A ≤ fixSub σ → HasA6Quot A →
    CFSG.Open.IsSubnormal I (fixSub σ) → S8.IsTypeWithCenter 3 I S8.isPSp43 1 →
    T ≠ ⊥ → IsPGroup 2 T → T.map σ.toMonoidHom = T →
    A ≤ Subgroup.normalizer (T : Set Q) →
    ∃ R : Subgroup Q, R ≠ ⊥ ∧ IsPGroup 2 R ∧ I ≤ Subgroup.normalizer (R : Set Q) ∧
      R.map σ.toMonoidHom = R

end CFSG.LocalAnalysis.GLTheoremA.I2016
