module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.GLS.Stage1.Thm6.Prelude

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
  CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Vocab

variable {G : Type} [Group G]

@[expose] def IsIntrinsic (t : G) (K : Subgroup G) : Prop :=
  IsPCompIn 2 (centralizer ({t} : Set G)) K ∧ pRank 2 ↥K = 1 ∧ t ∈ K

@[expose] def Jt (t : G) : Subgroup G := sSup {K : Subgroup G | IsIntrinsic t K}

@[expose] def cSec (K : Subgroup G) : Subgroup G := centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def O22 (X : Subgroup G) : Subgroup G := (pPrimePCore 2 ↥X).map X.subtype

@[expose] def InducesInner (s : G) (K : Subgroup G) : Prop :=
  ∃ k ∈ K, s * k⁻¹ ∈ cSec K

@[expose] def IDiag (y : G) (L : Subgroup G) : Subgroup G :=
  pLayerOf 2 (centralizer ({y} : Set G) ⊓ (L ⊔ conjugate L y))

end Vocab

section VocabQ

@[expose] def innOf (Q : Type) [Group Q] : Subgroup (MulAut Q) := (MulAut.conj : Q →* MulAut Q).range

@[expose] def IsSL2Or2A7 (Q : Type) [Group Q] : Prop :=
  (HasSL2Model Q (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt Q 7) ∧ Nat.card (center Q) = 2

end VocabQ

@[expose] def IG_balance_fAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (x y : G), orderOf x = 2 →
    orderOf y = 2 → Commute x y → ∀ L : Subgroup G, IsIntrinsic x L → InducesFAut y L →
      x ∈ O22 (centralizer ({y} : Set G)) ∨
        ∃ K : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) K ∧ x ∈ K

@[expose] def II4_44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ t : G, orderOf t = 2 →
    ∀ K : Subgroup G, IsPCompIn 2 (centralizer ({t} : Set G)) K → pRank 2 ↥K = 1 →
      IsSL2Or2A7 (↥K ⧸ pPrimeCore 2 ↥K)

@[expose] def II4_Aut : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSL2Or2A7 Q →
    (∀ c : Q, c ∉ center Q → c * c ∈ center Q → ¬ IsFAutomorphism Q (MulAut.conj c)) ∧
    (∀ a b : Q, orderOf a = 4 → orderOf b = 4 → IsConj a b) ∧
    ∀ φ : MulAut Q, φ * φ = 1 →
      (φ ≠ 1 → ∀ P : Subgroup Q, IsSylow2In P ⊤ → (∀ p ∈ P, φ p ∈ P) →
        ∃ w ∈ P, orderOf w = 4 ∧ φ w = w⁻¹) ∧
      (φ ∉ innOf Q → ¬ IsFAutomorphism Q φ → ∀ ψ : MulAut Q, ψ * ψ ≠ φ)

@[expose] def IG_3_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (x y : G), orderOf x = 2 →
    orderOf y = 2 → Commute x y → ∀ L : Subgroup G, IsIntrinsic x L →
      y ∉ normalizer (L : Set G) →
      IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) (IDiag y L) ∧
      2 ≤ pRank 2 ↥(IDiag y L) ∧
      (⨆ g ∈ pLayerOf 2 (centralizer ({x} : Set G)),
          (IDiag y L).map (MulAut.conj g).toMonoidHom) = L ⊔ conjugate L y ∧
      ∀ T : Subgroup G, IsSylow2In T (L ⊔ conjugate L y) → y ∈ normalizer (T : Set G) →
        ∃ S₀ : Subgroup G, IsSylow2In S₀ (IDiag y L) ∧
          (S₀ : Set G) = (fun a : G => a * (y⁻¹ * a * y)) '' ((T ⊓ L : Subgroup G) : Set G)

structure RecipCfg (G : Type) [Group G] [Finite G] (x y : G) (L J : Subgroup G) : Prop where
  simple : IsKProperSimple G
  hx : orderOf x = 2
  hy : orderOf y = 2
  comm : Commute x y
  hL : IsIntrinsic x L
  hJ : IsIntrinsic y J

structure FailB (G : Type) [Group G] [Finite G] (x y : G) (L J : Subgroup G) (a : G) : Prop where
  cfg : RecipCfg G x y L J
  hxJ : x ∈ normalizer (J : Set G)
  ha : a ∈ J
  ha2 : IsPGroup 2 (zpowers a)
  hay : a ∉ zpowers y
  hax : Commute a x
  haL : a ∉ normalizer (L : Set G)
  hmin : ∀ b ∈ J, IsPGroup 2 (zpowers b) → b ∉ zpowers y → Commute b x →
    b ∉ normalizer (L : Set G) → orderOf a ≤ orderOf b

end CFSG.GH74.GLS.Stage1.Thm2.Recip
