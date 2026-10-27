module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRecenter
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

@[expose] def LinearFRInput : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 5 ≤ n → ∀ (K : Type) [Field K] [Finite K] (f : ℕ),
    Nat.card K = 2 ^ f → 2 ≤ f → InnerGraphFieldRigid K hn

@[expose] def LinearTPInput : Prop :=
  ∀ (n : ℕ), 5 ≤ n → ∀ (K : Type) [Field K] [Finite K] (f : ℕ), Nat.card K = 2 ^ f → 2 ≤ f →
    TransvectionIntrinsicStd n K

@[expose] def LinearFieldRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ m → Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* LinearFlag.projectiveSL (m + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (F : Type) [Field F] [Finite F] (ι : K →+* F) (σ : F ≃+* F), σ ≠ 1 → σ * σ = 1 →
      (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
    ∀ G₀ : Subgroup G,
      G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) →
    (∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      (∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap (m + 1) ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀))) → False

@[expose] def LinearSwapLiftInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 5 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G)) →
    ∀ (a b : Fin n) (hab : a ≠ b), RootTorusSwapRow e t hab →
      Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin n))ᶜ))

@[expose] def LinearSwapRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* LinearFlag.projectiveSL (m + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin (m + 1)) (hab : a ≠ b),
        Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
          (({a, b} : Finset (Fin (m + 1)))ᶜ))) →
    ∀ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) →
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) → (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ i : Fin m,
          pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) : Subgroup G) : Set G) →
        g ∈ normalizer ((⨆ i : Fin m,
          pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) : Subgroup G) : Set G)

@[expose] def LinearOrthFiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G)) →
      ((∃ (F : Type) (_ : Field F) (_ : Finite F) (ι : K →+* F) (σ : F ≃+* F), σ ≠ 1 ∧
          σ * σ = 1 ∧ (∀ x : F, σ x = x ↔ x ∈ Set.range ι) ∧
          ∃ (a b : Fin 5) (hab : a ≠ b),
            Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
              (({a, b} : Finset (Fin 5))ᶜ))) ∨
        ∀ (a b : Fin 5) (hab : a ≠ b),
          Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
            (({a, b} : Finset (Fin 5))ᶜ))) →
      pieceCore e ({0, 1} : Finset (Fin 5)) ≤
        centralizer (pieceCore e ({2, 3} : Finset (Fin 5)) : Set G)

@[expose] def LinearFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (_ : L ≃* LinearFlag.projectiveSL 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

@[expose] def LinearTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 5 ≤ n →
    ∀ (_ : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False

end CFSG.SeitzReduction.LinearPilot
