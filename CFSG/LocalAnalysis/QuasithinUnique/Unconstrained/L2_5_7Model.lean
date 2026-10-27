module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Defs

variable {G : Type} [Group G]

@[expose] def IsRank2Model257 (K : Subgroup G) (n : ℕ) : Prop :=
  2 ≤ n ∧ (StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 n ∨
    StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 2 n)

structure IsParabolicPair257 (K P K₁ K₂ : Subgroup G) : Prop where
  sylow : IsSylowTwoOf P K
  lt₁ : K ⊓ Subgroup.normalizer (P : Set G) < K₁
  lt₂ : K ⊓ Subgroup.normalizer (P : Set G) < K₂
  lt_K₁ : K₁ < K
  lt_K₂ : K₂ < K
  ne : K₁ ≠ K₂
  sup_eq : K₁ ⊔ K₂ = K
  only : ∀ X : Subgroup G, K ⊓ Subgroup.normalizer (P : Set G) < X → X < K → X = K₁ ∨ X = K₂

structure RankTwoGeometry257 (P V V' : Subgroup G) : Prop where
  V_elem : IsElemAbelian 2 V
  P_eq : P = V ⊔ V'
  V_ne : V ≠ V'
  noncomm : ¬ V' ≤ Subgroup.centralizer (V : Set G)

end Defs

section Ledger

@[expose] def NonIso257 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 2 ≤ n →
    (StatedClassicalModel (K ⧸ CFSG.pCore 2 K) .PSL 3 2 n ∨
      StatedClassicalModel (K ⧸ CFSG.pCore 2 K) .PSp 2 2 n) →
    ¬ StatedClassicalModel K .PSL 3 3 1 ∧
      ¬ Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∧
      (∀ p : ℕ, IsFermatOrMersenne p → ¬ StatedClassicalModel K .PSL 2 p 1) ∧
      ¬ Id2519.Is121List (K ⧸ CFSG.pCore 2 K) ∧
      ¬ Nonempty (K ≃* alternatingGroup (Fin 6))

@[expose] def RankTwoGeom257 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P K₁ K₂ V V' : Subgroup G) (n : ℕ),
    CFSG.IsQuasisimple ↥K → IsRank2Model257 K n → IsRankTwoEvenType K →
    IsParabolicPair257 K P K₁ K₂ →
    V = pCoreOf 2 K₁ → V' = pCoreOf 2 K₂ → IsElemAbelian 2 (centerOf K) → RankTwoGeometry257 P V V'

@[expose] def RankTwoMaxRank257 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P K₁ K₂ V V' : Subgroup G) (n : ℕ),
    CFSG.IsQuasisimple ↥K → IsRank2Model257 K n → IsRankTwoEvenType K →
    IsParabolicPair257 K P K₁ K₂ →
    V = pCoreOf 2 K₁ → V' = pCoreOf 2 K₂ → IsElemAbelian 2 (centerOf K) →
    ∀ A : Subgroup G, A ≤ Subgroup.normalizer (K : Set G) → A ≤ Subgroup.normalizer (P : Set G) →
      IsElemAbelian 2 A →
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) ≤
        Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card V ∧
      (Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) =
          Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card V →
        A ≤ V ⊔ Subgroup.centralizer (K : Set G) ∨ A ≤ V' ⊔ Subgroup.centralizer (K : Set G))

@[expose] def Cover257a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G) (n : ℕ),
    CFSG.IsQuasisimple ↥K → IsRank2Model257 K n → IsRankTwoEvenType K → IsSylowTwoOf P K →
    ¬ IsElemAbelian 2 (centerOf K) →
    ∀ g ∈ Subgroup.normalizer (K : Set G), (∀ y ∈ P, g * y = y * g) →
      g ∈ Subgroup.centralizer (K : Set G)

@[expose] def RankTwoTorus257 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P K₁ K₂ V V' : Subgroup G) (n : ℕ),
    CFSG.IsQuasisimple ↥K → IsRank2Model257 K n → IsRankTwoEvenType K →
    IsParabolicPair257 K P K₁ K₂ →
    V = pCoreOf 2 K₁ → V' = pCoreOf 2 K₂ → IsElemAbelian 2 (centerOf K) →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ P₀ : Subgroup G, P₀ ≤ K ∧ IsElemAbelian p P₀ ∧
        Nat.card P₀ = p ^ 2) ∧
      ∃ h ∈ K ⊓ Subgroup.normalizer (P : Set G), (∃ k : ℕ, orderOf h = p ^ k) ∧
        ¬ ⁅V, V'⁆ ≤ Subgroup.centralizer ({h} : Set G)

@[expose] def AutOdd257 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P K₁ K₂ V V' : Subgroup G) (n : ℕ),
    CFSG.IsQuasisimple ↥K → IsRank2Model257 K n → IsRankTwoEvenType K →
    IsParabolicPair257 K P K₁ K₂ →
    V = pCoreOf 2 K₁ → V' = pCoreOf 2 K₂ → IsElemAbelian 2 (centerOf K) →
    ∀ g ∈ Subgroup.normalizer (K : Set G), g ∈ Subgroup.normalizer (P : Set G) →
      Odd (orderOf g) → (∀ s ∈ P, s⁻¹ * g⁻¹ * s * g ∈ V ⊓ V') →
        g ∈ Subgroup.centralizer (K : Set G)

end Ledger

end CFSG.QuasithinUnique
