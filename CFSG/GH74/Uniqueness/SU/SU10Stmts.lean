module

public import CFSG.GH74.Uniqueness.SU.SU8Stmts
public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8 CFSG.Blueprint

variable {G : Type} [Group G]

section Finite

variable [Finite G]

structure Hyp21 (S : Sylow 2 G) (M : Subgroup G) (z : G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kgh : KGH G
  rank : 3 ≤ Open.pRank 2 (S : Subgroup G)
  gamma_ne_top : gammaElem (S : Subgroup G) ≠ ⊤
  maximal : IsCoatom M
  gamma_le : gammaTwo (S : Subgroup G) ≤ M
  no_isolated : Concl184b M
  z_invol : orderOf z = 2
  z_center : ∀ s ∈ (S : Subgroup G), s * z = z * s

@[expose] def Prop211Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (M : Subgroup G) (z : G), Hyp21 S M z →
    (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype ≤ M ∧
    (centralizer ({z} : Set G) ≤ M ∨
      (K.IsTwoAlt (Hbar (centralizer ({z} : Set G))) 9 ∧
        K.IsTwoAlt ↥(hbarImage (centralizer ({z} : Set G)) M) 8) ∨
      ((∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
          Nonempty (Hbar (centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y)) ∧
        (∃ _ : ((centralizer ((S : Subgroup G) : Set G)).subgroupOf
            (normalizer ((S : Subgroup G) : Set G))).Normal,
          Nat.card (↥(normalizer ((S : Subgroup G) : Set G)) ⧸
            (centralizer ((S : Subgroup G) : Set G)).subgroupOf
              (normalizer ((S : Subgroup G) : Set G))) = 21 ∧
          ∃ a b : ↥(normalizer ((S : Subgroup G) : Set G)) ⧸
            (centralizer ((S : Subgroup G) : Set G)).subgroupOf
              (normalizer ((S : Subgroup G) : Set G)), a * b ≠ b * a) ∧
        (pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ →
          ∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
            Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y))))

@[expose] def Cor213Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (M : Subgroup G) (z : G), Hyp21 S M z →
    centralizer ({z} : Set G) ≤ M → CFSG.BenderSuzuki.IsBenderGroup G

end Finite

end CFSG.GH74.Uniqueness.SU.SU10
