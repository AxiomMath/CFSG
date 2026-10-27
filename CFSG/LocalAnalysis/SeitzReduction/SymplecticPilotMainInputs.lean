module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

@[expose] def SpFieldRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (F : Type) [Field F] [Finite F] (ι : K →+* F) (σ : F ≃+* F), orderOf σ = 2 →
      (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ → ψ.range = spGlobal e →
      (∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) →
      (∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x)) →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
        g ∈ normalizer (spGlobal e : Set G)

@[expose] def SpFourOrthInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (F : Type) [Field F] [Finite F] (ι : K →+* F) (σ : F ≃+* F), orderOf σ = 2 →
      (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
      (∀ k : Fin 4, Nonempty (FieldNeighbourParam e t ι σ k)) →
      ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)),
        Commute a b

@[expose] def SpSwapRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, Nonempty (SwapNeighbourParam e t k)) →
    ∀ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = ⨆ k : Fin n, neighbourCore e k →
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) → (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ k : Fin n, neighbourCore e k : Subgroup G) : Set G) →
        g ∈ normalizer ((⨆ k : Fin n, neighbourCore e k : Subgroup G) : Set G)

@[expose] def SpGraphRowsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ κ : Sp2mKind, κ ≠ .field → κ ≠ .swap → (∀ k : Fin n, RootKindSp e t f k κ) → False

@[expose] def SpThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (_ : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

@[expose] def SpTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (_ : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

end CFSG.SeitzReduction.SymplecticPilot
