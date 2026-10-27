module

public import CFSG.GH74.Generic.S3.Defs
public import CFSG.GH74.GLS.LU.Ident

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint Subgroup

@[expose] def B_S3_terminal_lin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → CentralizerCyclic2 x K →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f → LieModel ↥K .PSL 3 p f →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card F = p ^ f ∧ p ^ f % 4 = 1 ∧ GLS.LU.IsLinearA3Neighborhood F z u Y ∧
          A3Reflection x u Y ∧ imgBar x (Y 0 ⊔ Y 1) = K

@[expose] def B_S3_terminal_uni : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → CentralizerCyclic2 x K →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f → LieModel ↥K .PSU 3 p f →
      ∃ (F₂ F : Type) (_ : Field F₂) (_ : Finite F₂) (_ : Field F) (_ : Finite F) (z u : G)
        (Y : Fin 3 → Subgroup G),
        Nat.card F₂ = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ p ^ f % 4 = 3 ∧
          GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F z u Y ∧
          A3Reflection x u Y ∧ imgBar x (Y 0 ⊔ Y 1) = K

@[expose] def B_S3_terminal : Prop :=
  B_S3_terminal_lin ∧ B_S3_terminal_uni

@[expose] def B_S3_pump : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → ¬ CentralizerCyclic2 x K → QcongNegEps K →
    ∃ (w : G) (hw : w ∈ centralizer ({x} : Set G)) (K' : Subgroup (CentralizerBar w)),
      orderOf w = 2 ∧ barOf hw ∈ centralizer (K : Set (CentralizerBar x)) ∧
        IsComponent K' ∧ GLS.InG2 ↥K' ∧ ShapeS1 w K' ∧
        ∃ M : Subgroup G, M ≤ centralizer ({x} : Set G) ⊓ centralizer ({w} : Set G) ∧
          imgBar x M = K ∧ imgBar w M ≤ K'

@[expose] def B_S3_L4Reflection_lin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (F : Type) (_ : Field F) (_ : Finite F) (p f : ℕ),
    p.Prime → p ≠ 2 → Nat.card F = p ^ f → 5 ≤ p ^ f → p ^ f % 4 = 1 →
      ∀ (x z u : G) (Y : Fin 3 → Subgroup G), orderOf x = 2 →
        GLS.LU.IsLinearA3Neighborhood F z u Y → A3Reflection x u Y → False

@[expose] def B_S3_L4Reflection_uni : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (F₂ F : Type) (_ : Field F₂) (_ : Finite F₂)
    (_ : Field F) (_ : Finite F) (p f : ℕ),
    p.Prime → p ≠ 2 → Nat.card F₂ = (p ^ f) ^ 2 → Nat.card F = p ^ f → 5 ≤ p ^ f → p ^ f % 4 = 3 →
      ∀ (x z u : G) (Y : Fin 3 → Subgroup G), orderOf x = 2 →
        GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F z u Y → A3Reflection x u Y → False

@[expose] def B_S3_L4Reflection : Prop :=
  B_S3_L4Reflection_lin ∧ B_S3_L4Reflection_uni

end CFSG.GH74.Generic.S3
