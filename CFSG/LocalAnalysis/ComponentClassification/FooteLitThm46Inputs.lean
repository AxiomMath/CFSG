module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteL2FourgroupE8 : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ E : Subgroup (MulAut S), (∀ e ∈ E, e * e = 1) → Nat.card E = 8 →
      (∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x) ∧
      ∀ V : Subgroup S, IsKleinFour V →
        ∃ F : Subgroup (MulAut S), F ≤ E ⊔ (MulAut.conj : S →* MulAut S).range ∧
          (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8 ∧ V.map (MulAut.conj : S →* MulAut S) ≤ F

@[expose] def FooteSmallCentralizers : Prop :=
  ∀ (S : Type) [Group S] [Finite S], AschbacherKnownGroup.IsSmallDihedralSimple S →
    (∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x) →
    ∀ T : Subgroup (MulAut S), IsPGroup 2 T → (∃ P : Sylow 2 S, Nonempty ((P : Subgroup S) ≃* T)) →
      ⨆ (τ : MulAut S) (_ : τ ∈ T) (_ : orderOf τ = 2),
        MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) = ⊤

end CFSG.ComponentClassification.FooteLit
