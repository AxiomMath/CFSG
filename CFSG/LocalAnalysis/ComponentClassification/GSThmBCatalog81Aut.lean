module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

abbrev fixSub {K₀ : Type} [Group K₀] (α : MulAut K₀) : Subgroup K₀ :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id K₀)

@[expose] def CF81NoNilp : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ α : MulAut K₀, α * α = 1 → ¬ HasNormalPComplement 2 ↥(fixSub α)

@[expose] def CF81FieldOrd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ T : Sylow 2 Y, 8 ≤ Nat.card T →
      ∀ φ : MulAut Y, φ * φ = 1 → φ ∈ centralizer (innOf (T : Subgroup Y) : Set (MulAut Y)) →
        φ ∉ innOf (T : Subgroup Y) → ∀ w : MulAut Y, w * φ = φ * w → IsPGroup 2 (zpowers w) →
          2 * orderOf w ≤ Nat.card T

@[expose] def CF81Diag : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ T : Sylow 2 Y, 8 ≤ Nat.card T →
      ∀ φ : MulAut Y, φ * φ = 1 → φ ∈ centralizer (innOf (T : Subgroup Y) : Set (MulAut Y)) →
        φ ∉ innOf (T : Subgroup Y) → ∀ ζ ∈ innOf (T : Subgroup Y),
          ζ ∈ centralizer (innOf (T : Subgroup Y) : Set (MulAut Y)) → ζ ≠ 1 →
          ∀ w ∈ normalizer (innOf (T : Subgroup Y) : Set (MulAut Y)), w⁻¹ * φ * w = ζ * φ →
            ∃ t ∈ innOf (T : Subgroup Y),
              w * t * w⁻¹ * t⁻¹ ∉ ⁅innOf (T : Subgroup Y), innOf (T : Subgroup Y)⁆

end CFSG.ComponentClassification.GSThmB
