module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

@[expose] def Co1LocalComponentsInput : Prop :=
  ∀ (S : Type) [Group S], (S ≃* NativeSporadic.Co1) → ∀ t : S, orderOf t = 2 →
    ∀ B : Subgroup (centralizer ({t} : Set S)), IsComponent B →
      Nat.card (B ⧸ center B) = 251596800 ∧ 13 ∣ Nat.card (B ⧸ center B)

@[expose] def HNLocalComponentsInput : Prop :=
  ∀ (S : Type) [Group S], (S ≃* NativeSporadic.HN) → ∀ a : S, orderOf a = 2 →
    ∀ B : Subgroup (centralizer ({a} : Set S)), IsComponent B →
      Nat.card (B ⧸ center B) = 44352000

@[expose] def FourExactOuterInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    (Nonempty (S ≃* NativeSporadic.J4) ∨ Nonempty (S ≃* NativeSporadic.HN) ∨
      Nonempty (S ≃* NativeSporadic.B) ∨ Nonempty (S ≃* NativeSporadic.M)) →
    ∀ α : MulAut S, orderOf α = 2 → α ∉ inner S →
      Nonempty (S ≃* NativeSporadic.HN) ∧ IsEmpty (S ≃* NativeSporadic.J4) ∧
        IsEmpty (S ≃* NativeSporadic.B) ∧ IsEmpty (S ≃* NativeSporadic.M) ∧
        Nonempty (fixSub α ≃* Equiv.Perm (Fin 10)) ∧ Nat.card (fixSub α) = 3628800 ∧
        2 ^ (Nat.card (fixSub α)).factorization 2 = 256 ∧
        ∃ E : Subgroup (fixSub α), Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4

@[expose] def LyOuterTrivialInput : Prop := inner NativeSporadic.Ly = ⊤

@[expose] def Fi22OuterComponentsInput : Prop :=
  ∀ (G : Type) [Group G], Nonempty (G ≃* NativeSporadic.Fi22) → ∀ α : MulAut G, α * α = 1 →
    α ∉ inner G → ∀ B : Subgroup (fixSub α), IsComponent B →
      Nat.card (B ⧸ center B) = 174182400 ∨ Nat.card (B ⧸ center B) = 1451520

@[expose] def Fi24primeOuterComponentsInput : Prop :=
  ∀ (G : Type) [Group G], Nonempty (G ≃* NativeSporadic.Fi24prime) → ∀ α : MulAut G,
    α * α = 1 → α ∉ inner G → ∀ B : Subgroup (fixSub α), IsComponent B →
      Nat.card (B ⧸ center B) = 4089470473293004800 ∨ Nat.card (B ⧸ center B) = 9196830720

@[expose] def J4NoComponentsInput : Prop :=
  ∀ (G : Type) [Group G], Nonempty (G ≃* NativeSporadic.J4) → ∀ t : G, orderOf t = 2 →
    ∀ B : Subgroup (centralizer ({t} : Set G)), ¬ IsComponent B

end CFSG.ComponentClassification.RestrictedStd.Spor
