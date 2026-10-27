module

public import CFSG.GH74.Generic.BProg.Frozen

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def derivedIn (M : Subgroup G) : Subgroup G := (commutator ↥M).map M.subtype

abbrev Mbar (M : Subgroup G) : Type := ↥M ⧸ pPrimeCore 2 ↥M

@[expose] def barIn (M H : Subgroup G) : Subgroup (Mbar M) :=
  (H.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))

structure Stage2Setup (G : Type) [Group G] [Finite G] (x : G) (K A M P Q : Subgroup G) : Prop where
  hyp : Hyp2 G
  noAlt : NoAltJ2 G
  pair : IsJ2Circ x K
  src : IsSource2 x K A
  nonSS : ¬ IsAllowable x K A
  reg : IsReg32 A
  maxM : IsCoatom M
  le_M : normalizer (thetaHalf 1 A : Set G) ≤ M
  sylowP : IsSylowOf 2 P (centralizer ({x} : Set G))
  A_le : A ≤ P
  Q_eq : Q = P ⊓ CxK x K
  sylowQ : IsSylowOf 2 Q (CxK x K)

structure Stage2Concl1 {G : Type} [Group G] (x : G) (K M Q H : Subgroup G) : Prop where
  K_le : K ≤ M
  Q_le : Q ≤ M
  Q_syl : IsSylowOf 2 Q (M ⊓ centralizerSection K (pPrimeCoreOf 2 K))
  H_min : IsMinSubnormalIn K M H
  H_G2 : ∀ L : Subgroup (Mbar M), IsComponent L → L ≤ barIn M H → GLS.InG2 ↥L
  H_tri : barIn M H = barIn M K ∨
    (barIn M H = generalizedFitting (Mbar M) ∧ IsSimpleGroup ↥(barIn M H)) ∨
    (barIn M H = generalizedFitting (Mbar M) ∧ ∃ (hx : x ∈ M) (L₁ L₂ : Subgroup (Mbar M)),
      IsComponent L₁ ∧ IsComponent L₂ ∧ L₁ ≠ L₂ ∧ IsSimpleGroup ↥L₁ ∧ IsSimpleGroup ↥L₂ ∧
        barIn M H = L₁ ⊔ L₂ ∧
        (L₁.map (MulAut.conj (QuotientGroup.mk (⟨x, hx⟩ : ↥M) : Mbar M)).toMonoidHom) = L₂ ∧
        (∀ L : Subgroup (Mbar M), IsComponent L → L = L₁ ∨ L = L₂))
  O_ne : pPrimeCoreOf 2 M ≠ ⊥
  preuniq : M ≠ ⊤ ∧ ∀ y ∈ M, orderOf y = 2 → y ∈ centralizerSection H (pPrimeCoreOf 2 H) →
    centralizer ({y} : Set G) ≤ M

@[expose] def InU0 (M B : Subgroup G) : Prop :=
  IsE 2 M B ∧ (pRank 2 ↥B = 2 ∨ pRank 2 ↥B = 3) ∧ gammaK 2 B (pRank 2 ↥B - 1) ≤ M

@[expose] def Stage2Concl2 (M : Subgroup G) : Prop :=
  ∀ B : Subgroup G, InU0 M B → ∀ g : G, conjugate B g ≤ M → g ∈ M

structure Stage2Cor2 {G : Type} [Group G] (x : G) (K A M H : Subgroup G) : Prop where
  a : ∀ X B : Subgroup G, X ≤ M → InU0 M B → B ≤ X → normalizer (X : Set G) ≤ M
  b : ∀ X B : Subgroup G, InU0 M B → (B.subgroupOf X).IsSubnormal → B ≤ X → X ≤ M
  c : ∀ X B : Subgroup G, IsPGroup 2 ↥X → InU0 M B → B ≤ X → X ≤ M
  d : A ⊔ zpowers x ≤ derivedIn M ∧
    ∀ y ∈ M ⊓ centralizer (A : Set G), orderOf y = 2 → y ∈ derivedIn M
  e : barIn M H = barIn M K ∨
    (barIn M H = generalizedFitting (Mbar M) ∧ IsSimpleGroup ↥(barIn M H))

structure Stage3A {G : Type} [Group G] (x : G) (A M H : Subgroup G) : Prop where
  Cx_le : centralizer ({x} : Set G) ≤ M
  x_mem : x ∈ derivedIn M
  inv_mem : ∀ y ∈ M ⊓ centralizer (A : Set G), orderOf y = 2 → y ∈ derivedIn M
  H_simple : barIn M H = generalizedFitting (Mbar M) ∧ IsSimpleGroup ↥(barIn M H)

end Defs

end CFSG.GH74.Generic.BProg
