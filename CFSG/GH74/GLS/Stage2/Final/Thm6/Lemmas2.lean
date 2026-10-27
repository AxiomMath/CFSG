module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs2

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def Lemma20_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    TypeCl z k S → ∀ g : G, zc z g ∈ S → zc z g ∉ zpowers z → F20 z ⊓ Ag z g = ⊥

@[expose] def Lemma20_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    TypeCl z k S →
      ((∃ (ε : Bool) (q : ℕ), TypeL4 z k S ε q ∧ ¬ Fused ε q) ∨ ∃ q : ℕ, TypePSp4 z k S q) ∧
      (∀ u ∈ L20 z, IsConj z u → u = z) ∧
      ∀ y ∈ S, IsConj z y →
        (∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ ∧ Swaps z y L₁ L₂) →
        ∀ f ∈ F20 z, y * f * y⁻¹ = f⁻¹

@[expose] def Lemma20_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    (∃ (ε : Bool) (q : ℕ), TypeL4 z k S ε q ∧ ¬ Fused ε q) → ∃ q : ℕ, TypePSp4 z k S q

section Symplectic

variable {G : Type} [Group G]

@[expose] def Concl20_14 (z g : G) : Prop :=
  ∀ e ∈ Ey z g, zc z g * e * (zc z g)⁻¹ = e⁻¹ ∧ z * e * z⁻¹ = e⁻¹ ∧ (zc z g * z) * e = e * (zc z g * z)

@[expose] def Concl20_15 (z g : G) : Prop :=
  (∃ r : ℕ, Odd r ∧ PGLModO (Jy z g) (zpowers z) r) ∧ zc z g * z ∈ Jy z g

end Symplectic

@[expose] def Lemma20_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    (∃ q : ℕ, TypePSp4 z k S q) → ∀ g : G, SympCtx z S g → Concl20_14 z g

@[expose] def Lemma20_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    (∃ q : ℕ, TypePSp4 z k S q) → ∀ g : G, SympCtx z S g → Concl20_14 z g → Concl20_15 z g

@[expose] def Lemma20_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    (∃ q : ℕ, TypePSp4 z k S q) → ∀ g : G, SympCtx z S g → Concl20_14 z g → Concl20_15 z g →
      A20 z = ⊥

end CFSG.GH74.GLS.Stage2.Final.Thm6
