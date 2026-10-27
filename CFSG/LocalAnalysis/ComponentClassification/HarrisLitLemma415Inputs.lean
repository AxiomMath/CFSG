module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

@[expose] def Harris415CaseHyp (X : Type) [Group X] [Finite X] (t : X) (L : Subgroup X)
    (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ) : Prop :=
  ∃ hs : Setting46e t L p f S w z V i j,
    IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j) ∧
    (∀ i' j' : ℕ, IsLemma47 p (w ^ (orderOf w / 2) * t ^ i' * z ^ j')) ∧
    ¬ IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

structure Harris415FData {X : Type} [Group X] (t : X) (L S : Subgroup X) (u z β : X)
    (z₁ τ α : X) (K₂ W 𝒱 : Subgroup X) : Prop where
  sq_z₁ : z₁ ^ 2 = 1
  z₁_ne : z₁ ≠ t * z₁ * t⁻¹
  z_eq : z = z₁ * (t * z₁ * t⁻¹)
  isTwoComponentIn_K₂ : IsTwoComponentIn K₂ (centralizer {z₁} ⊓ centralizer {β})
  bar_K₂ : Nonempty (↥K₂ ⧸ pPrimeCore 2 ↥K₂ ≃* ↥(Standing.Setup42.KBar L β))
  z₂_mem : t * z₁ * t⁻¹ ∈ K₂
  layerIn_K₂ : GSThmB.layerIn (centralizer {z₁} ⊓ centralizer {β}) = K₂
  isPGroup_centralizer_K₂ : IsPGroup 2
    (↥(centralizer {z₁} ⊓ centralizer {β} ⊓ centralizer (K₂ : Set X)) ⧸
      pPrimeCore 2 ↥(centralizer {z₁} ⊓ centralizer {β} ⊓ centralizer (K₂ : Set X)))
  isSylowOf_W : IsSylowOf 2 W (centralizer {β})
  isSylowOf_𝒱 : IsSylowOf 2 𝒱 ⊤
  W_le : W ≤ 𝒱
  t_mem : t ∈ 𝒱
  card_𝒱_le : Nat.card 𝒱 ≤ 4 * Nat.card W
  isSylowOf_𝒱₀ : IsSylowOf 2 (𝒱 ⊓ centralizer {z₁}) (centralizer {z₁})
  isSylowOf_W₀ : IsSylowOf 2 (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {β})
    (centralizer {z₁} ⊓ centralizer {β})
  card_W₀ : 2 * Nat.card ↥(𝒱 ⊓ centralizer {z₁} ⊓ centralizer {β}) = Nat.card W
  card_𝒱₀_le : Nat.card ↥(𝒱 ⊓ centralizer {z₁}) ≤
    4 * Nat.card ↥(𝒱 ⊓ centralizer {z₁} ⊓ centralizer {β})
  center_𝒱₀ : (center ↥(𝒱 ⊓ centralizer {z₁})).map (𝒱 ⊓ centralizer {z₁}).subtype =
    closure {z₁, t * z₁ * t⁻¹}
  τ_mem : τ ∈ 𝒱 ⊓ centralizer {z₁}
  τ_conj : τ * β * τ⁻¹ = β * z
  not_conj_z : ∀ g : X, g * z₁ * g⁻¹ ≠ z
  fusion : (∀ g : X, g * β * g⁻¹ ≠ z₁) →
    (∀ g : X, g * t * g⁻¹ ∈ closure {t, u, z} → g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z) ∧
      (∃ g : X, g * (t * β) * g⁻¹ = z₁) ∧
      twoPart (centralizer ({z₁} : Set X)) ≤ twoPart (centralizer ({β} : Set X))
  α_mem : α ∈ 𝒱 ⊓ centralizer {z₁}
  α_conj : ∃ g : X, g * t * g⁻¹ = α ∧ S.map (MulAut.conj g).toMonoidHom = 𝒱 ⊓ centralizer {α} ∧
    (closure {t, u, z}).map (MulAut.conj g).toMonoidHom = closure {α, z₁, t * z₁ * t⁻¹}

@[expose] def Harris415TwoLocalStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris415CaseHyp X t L p f S w z V i j →
      ∃ (z₁ τ α : X) (K₂ W 𝒱 : Subgroup X),
        Harris415FData t L S (w ^ (orderOf w / 2)) z (w ^ (orderOf w / 2) * t ^ i * z ^ j)
          z₁ τ α K₂ W 𝒱

@[expose] def Harris415ComponentStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Harris415CaseHyp X t L p f S w z V i j →
      ∀ (z₁ τ α : X) (K₂ W 𝒱 : Subgroup X),
        Harris415FData t L S (w ^ (orderOf w / 2)) z (w ^ (orderOf w / 2) * t ^ i * z ^ j)
          z₁ τ α K₂ W 𝒱 → False

theorem harris415_of_steps (h412 : Harris412Statement) (h47 : Harris47Input)
    (hA : Harris415TwoLocalStep) (hB : Harris415ComponentStep) : Harris415Input46e := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs
  by_contra hnq
  have hhyp : Harris415CaseHyp X t L p f S w z V i j :=
    ⟨hs, h412 X hnonab hK hcat t L p f S w z V i j hs,
      h47 X hnonab hK hcat t L p f S w z V i j hs, hnq⟩
  obtain ⟨z₁, τ, α, K₂, W, 𝒱, hD⟩ := hA X hnonab hK hcat t L p f S w z V i j hhyp
  exact hB X hnonab hK hcat t L p f S w z V i j hhyp z₁ τ α K₂ W 𝒱 hD

end CFSG.ComponentClassification.HarrisLit
