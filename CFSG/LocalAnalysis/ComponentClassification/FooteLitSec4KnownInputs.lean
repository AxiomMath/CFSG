module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteL2FourgroupGeneration : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (S : Subgroup Y), S.Normal →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ p ^ f ≠ 9 ∧
      Blueprint.LieModel ↥S .PSL 2 p f) →
    ∀ E : Subgroup Y, (∀ e ∈ E, e ^ 2 = 1) → Nat.card E = 8 →
      E ⊓ centralizer (S : Set Y) = ⊥ →
      S ≤ ⨆ (X : Subgroup Y) (_ : X ≤ E) (_ : 4 ≤ Nat.card X), normalizer (X : Set Y)

@[expose] def FooteAutRankThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ E : Subgroup (MulAut S), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 8

@[expose] def FooteL2RootedOuter : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ y : MulAut S, y ^ 4 = 1 → y ^ 2 ≠ 1 → y ^ 2 ∉ (MulAut.conj : S →* MulAut S).range →
      IsSimpleGroup ↥⁅MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S),
        MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S)⁆ ∧
      2 ≤ CFSG.pRank 2 ↥⁅MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S),
        MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S)⁆ ∧
      ∀ σ : MulAut S,
        (∀ j ∈ ⁅MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S),
          MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S)⁆, σ j = j) →
        σ = 1 ∨ σ = y ^ 2

end CFSG.ComponentClassification.FooteLit
