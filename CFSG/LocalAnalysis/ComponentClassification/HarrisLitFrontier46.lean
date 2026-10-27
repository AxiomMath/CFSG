module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFamily

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open Standing.Setup42

variable {X : Type} [Group X]

@[expose] def IsLemma46c (L : Subgroup X) (β : X) : Prop :=
  layer (MBar β) = ⨆ g : ↥(layer (MBar β)), (KBar L β).map (MulAut.conj (g : MBar β)).toMonoidHom ∧
    layer (MBar β) = ⁅KBar L β, layer (MBar β)⁆ ∧
    (center ↥(layer (MBar β)) ≠ ⊥ →
      betaBar β ∈ (center ↥(layer (MBar β))).map (layer (MBar β)).subtype)

@[expose] def IsLemma46d (p f : ℕ) (L : Subgroup X) (β : X) (tb : MBar β) : Prop :=
  (IsQuasisimple ↥(layer (MBar β)) ∧ IsOfType (HarrisF p) ↥(layer (MBar β))) ∨
    ∃ K₁ K₂ : Subgroup (MBar β), K₁ ⊔ K₂ = layer (MBar β) ∧ K₁ ⊓ K₂ = ⊥ ∧
      K₁ ≤ centralizer (K₂ : Set (MBar β)) ∧ K₁.map (MulAut.conj tb⁻¹).toMonoidHom = K₂ ∧
      Nonempty (↥K₁ ≃* ↥(KBar L β)) ∧ Nonempty (↥K₂ ≃* ↥(KBar L β)) ∧
      Blueprint.LieModel ↥(KBar L β) .PSL 2 p (f / 2) ∧
      KBar L β = layer (MBar β) ⊓ centralizer {tb} ∧
      KBar L β = closure ((fun k => k * (tb⁻¹ * k * tb)) '' (K₁ : Set (MBar β)))

@[expose] def IsLemma46eOdd (L : Subgroup X) (β : X) : Prop :=
  pPrimeCore 2 ↥(KBar L β) = ⊥

@[expose] def IsLemma46g (β : X) : Prop :=
  pCore 2 (MBar β) = solvableRadical (MBar β) ∧
    solvableRadical (MBar β) = centralizer (layer (MBar β) : Set (MBar β)) ∧
    (IsCyclic ↥(pCore 2 (MBar β)) ∨
      ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥(pCore 2 (MBar β)) ≃* DihedralGroup (2 ^ k))) ∧
    closure {x : MBar β | Odd (orderOf x)} ≤ centralizer (pCore 2 (MBar β) : Set (MBar β))

@[expose] def IsLemma47 (p : ℕ) (β : X) : Prop :=
  ∀ J : Subgroup ↥(centralizer ({β} : Set X)), IsPComponent 2 J → ∀ k : ℕ, 1 ≤ k →
    ¬ IsOfType (fun (Y : Type) [Group Y] =>
      Blueprint.LieModel Y .PSL 4 p k ∨ Blueprint.LieModel Y .PSU 4 p k) ↥J

@[expose] def Harris46cInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j → ∀ i' j' : ℕ,
        IsLemma46c L (w ^ (orderOf w / 2) * t ^ i' * z ^ j')

@[expose] def Harris46dInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ)
      (hs : Setting46e t L p f S w z V i j) (i' j' : ℕ),
        IsLemma46d p f L (w ^ (orderOf w / 2) * t ^ i' * z ^ j') (hs.setup.tBar i' j')

@[expose] def Harris46eOddInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j → ∀ i' j' : ℕ,
        IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i' * z ^ j')

@[expose] def Harris46gInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j → ∀ i' j' : ℕ,
        IsLemma46g (w ^ (orderOf w / 2) * t ^ i' * z ^ j')

@[expose] def Harris47Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j → ∀ i' j' : ℕ,
        IsLemma47 p (w ^ (orderOf w / 2) * t ^ i' * z ^ j')

end CFSG.ComponentClassification.HarrisLit
