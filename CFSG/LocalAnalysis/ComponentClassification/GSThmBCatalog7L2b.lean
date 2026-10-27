module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

abbrev innOf {Y : Type} [Group Y] (T : Subgroup Y) : Subgroup (MulAut Y) :=
  T.map (MulAut.conj : Y →* MulAut Y)

@[expose] def CFL2Rank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ E : Subgroup (MulAut Y), (∀ e ∈ E, e * e = 1) →
      Nat.card E ≤ 8

@[expose] def CFL2Sylow : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ T : Sylow 2 Y, 8 ≤ Nat.card T →
      Nat.card ↥((T : Subgroup Y) ⊓ centralizer ((T : Subgroup Y) : Set Y)) = 2 ∧
      (∃ t ∈ (T : Subgroup Y), t * t ≠ 1 ∧ t * t ∈ centralizer ((T : Subgroup Y) : Set Y)) ∧
      ∀ t ∈ (T : Subgroup Y), ∃ i ∈ (T : Subgroup Y), ∃ j ∈ (T : Subgroup Y),
        i * i = 1 ∧ j * j = 1 ∧ t = i * j

@[expose] def CFL2C : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ T : Sylow 2 Y, 8 ≤ Nat.card T →
      ∀ R : Subgroup (MulAut Y), IsPGroup 2 R →
        R ≤ centralizer (innOf (T : Subgroup Y) : Set (MulAut Y)) → Nat.card R ≤ 4

@[expose] def CFL2A : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ R D₁ E : Subgroup (MulAut Y), IsPGroup 2 R →
      D₁ ≤ R → E ≤ R → E ≤ centralizer (D₁ : Set (MulAut Y)) → D₁ ⊓ E = ⊥ → E ≠ ⊥ →
      (∃ T : Sylow 2 Y, Nonempty (↥D₁ ≃* ↥(T : Subgroup Y))) →
      Nat.card E = 2 ∧ (∀ T : Sylow 2 Y, 8 ≤ Nat.card T) ∧
        ∃ T : Sylow 2 Y, innOf (T : Subgroup Y) ≤ D₁ ⊔ E

@[expose] def CFL2J : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ T : Sylow 2 Y, 8 ≤ Nat.card T →
      ∀ R : Subgroup (MulAut Y), IsPGroup 2 R → innOf (T : Subgroup Y) ≤ R →
      ∀ E : Subgroup (MulAut Y), E ≤ R → (∀ e ∈ E, e * e = 1) → Nat.card E = 8 →
        E ≤ innOf (T : Subgroup Y) ⊔
          (R ⊓ centralizer (innOf (T : Subgroup Y) : Set (MulAut Y)))

end CFSG.ComponentClassification.GSThmB
