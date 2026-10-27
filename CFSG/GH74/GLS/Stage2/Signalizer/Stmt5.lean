module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

structure Ctx51 {G : Type} [Group G] (k : Kind) (z : G) (S T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G) :
    Prop where
  T5 : T5A z k S T Tstar
  prime : p.Prime
  odd : p ≠ 2
  T_le : T ≤ H
  fstar : Fs H = Op p H
  maxi : MaxInv p H T Tstar P

@[expose] def Concl51 {G : Type} [Group G] [Finite G] (k : Kind) (S : Subgroup G) (p : ℕ) (H P : Subgroup G) : Prop :=
  H ≤ normalizer ((kInfty P : Subgroup G) : Set G) ∨ SDorWr S ∨
    (k = Kind.ly ∧ p = 3 ∧ IsDoubleCoverOfAlt ↥(layer (HBar H)) 11 ∧
      H = pPrimeCoreOf 2 H ⊔ H ⊓ centralizer ((omega1Z p P : Subgroup G) : Set G))

section Lemmas

variable {G : Type} [Group G] [Finite G]

@[expose] def L52 (k : Kind) (S T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G) : Prop :=
  Op p H ≤ P ∧
  ((TypeOneCase G k ∧ T = S ∧ Tstar = S) →
    CFSG.ABGLocalTools.IsSylowOf p (P ⊓ pPrimeCoreOf 2 H) (pPrimeCoreOf 2 H)) ∧
  ⁅O22Of H, P⁆ ≤ pPrimeCoreOf 2 H ∧
  barIn H P ≤ centralizer ((centralizer ((layer (HBar H) : Subgroup (HBar H)) : Set (HBar H)) :
    Subgroup (HBar H)) : Set (HBar H))

@[expose] def IsChiefFactorIn (H X Y : Subgroup G) : Prop :=
  X ≤ H ∧ Y < X ∧ (∀ h ∈ H, h ∈ normalizer (X : Set G)) ∧ (∀ h ∈ H, h ∈ normalizer (Y : Set G)) ∧
    ∀ Z : Subgroup G, Y ≤ Z → Z ≤ X → (∀ h ∈ H, h ∈ normalizer (Z : Set G)) → Z = Y ∨ Z = X

@[expose] def CV (H X Y : Subgroup G) : Subgroup G := H ⊓ centralizerSection X Y

@[expose] def Step53 (p : ℕ) (H P : Subgroup G) (g : G) (X Y : Subgroup G) : Prop :=
  g ∈ P ∧ g ∉ Op p H ∧ X ≤ Op p H ∧ IsChiefFactorIn H X Y ∧
    ⁅⁅X, zpowers g⁆, zpowers g⁆ ≤ Y ∧ ¬ ⁅X, zpowers g⁆ ≤ Y ∧
    (∃ h ∈ H, ∃ J : Subgroup G, J = Subgroup.closure {g, h * g * h⁻¹} ∧ J ≤ nclIn H (zpowers g) ∧
      ∃ N : Subgroup G, N ≤ J ∧ J ⊓ CV H X Y ≤ N ∧ ∃ _ : (N.subgroupOf J).Normal,
        HasSL2Model (↥J ⧸ N.subgroupOf J)
          (fun q => (∃ n : ℕ, 1 ≤ n ∧ q = p ^ n) ∨ (p = 3 ∧ q = 5))) ∧
    ¬ barIn H (zpowers g) ≤ centralizer ((layer (HBar H) : Set (HBar H)))

@[expose] def L55 (k : Kind) (p : ℕ) (H : Subgroup G) : Prop :=
  layer (HBar H) = ⊤ ∧ IsDoubleCoverOfAlt ↥(layer (HBar H)) 11 ∧ k = Kind.ly ∧ p = 3

end Lemmas

@[expose] def Lemma5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      ¬ Concl51 k S p H P → L52 k S T Tstar p H P

@[expose] def Lemma5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      ¬ Concl51 k S p H P → L52 k S T Tstar p H P → ∃ (g : G) (X Y : Subgroup G), Step53 p H P g X Y

end CFSG.GH74.GLS.Stage2.Signalizer
