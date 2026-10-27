module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.Stage2Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

section Gamma

variable {G : Type} [Group G]

@[expose] def gammaKC (p : ℕ) (B : Subgroup G) (k : ℕ) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ B) (_ : k ≤ pRank p ↥Q), centralizer (Q : Set G)

@[expose] def InU0C (M B : Subgroup G) : Prop :=
  IsE 2 M B ∧ (pRank 2 ↥B = 2 ∨ pRank 2 ↥B = 3) ∧ gammaKC 2 B (pRank 2 ↥B - 1) ≤ M

@[expose] def Stage2Concl2C (M : Subgroup G) : Prop :=
  ∀ B : Subgroup G, InU0C M B → ∀ g : G, conjugate B g ≤ M → g ∈ M

@[expose] def sigX (M : Subgroup G) (h : G) : Subgroup G :=
  pPrimeCoreOf 2 M ⊔ conjugate (pPrimeCoreOf 2 M) h

structure Sym8A (M B : Subgroup G) (h : G) : Prop where
  maxM : IsCoatom M
  O_ne : pPrimeCoreOf 2 M ≠ ⊥
  hB : InU0C M B
  h_not : h ∉ M
  D_le : conjugate B h ≤ M
  B_le : B ≤ conjugate M h

end Gamma

section Core

variable {G : Type} [Group G]

@[expose] def HTri (x : G) (K M H : Subgroup G) : Prop :=
  barIn M H = barIn M K ∨
    (barIn M H = generalizedFitting (Mbar M) ∧ IsSimpleGroup ↥(barIn M H)) ∨
    (barIn M H = generalizedFitting (Mbar M) ∧ ∃ (hx : x ∈ M) (L₁ L₂ : Subgroup (Mbar M)),
      IsComponent L₁ ∧ IsComponent L₂ ∧ L₁ ≠ L₂ ∧ IsSimpleGroup ↥L₁ ∧ IsSimpleGroup ↥L₂ ∧
        barIn M H = L₁ ⊔ L₂ ∧
        (L₁.map (MulAut.conj (QuotientGroup.mk (⟨x, hx⟩ : ↥M) : Mbar M)).toMonoidHom) = L₂ ∧
        (∀ L : Subgroup (Mbar M), IsComponent L → L = L₁ ∨ L = L₂))

structure Stage2Concl1Core (x : G) (K M Q H : Subgroup G) : Prop where
  K_le : K ≤ M
  Q_le : Q ≤ M
  Q_syl : IsSylowOf 2 Q (M ⊓ centralizerSection K (pPrimeCoreOf 2 K))
  H_min : IsMinSubnormalIn K M H
  H_G2 : ∀ L : Subgroup (Mbar M), IsComponent L → L ≤ barIn M H → GLS.InG2 ↥L
  H_tri : HTri x K M H
  O_ne : pPrimeCoreOf 2 M ≠ ⊥

theorem Stage2Concl1.toCore {x : G} {K M Q H : Subgroup G} (h : Stage2Concl1 x K M Q H) :
    Stage2Concl1Core x K M Q H :=
  ⟨h.K_le, h.Q_le, h.Q_syl, h.H_min, h.H_G2, h.H_tri, h.O_ne⟩

theorem Stage2Concl1.ofCore {x : G} {K M Q H : Subgroup G} (h : Stage2Concl1Core x K M Q H)
    (hp : M ≠ ⊤ ∧ ∀ y ∈ M, orderOf y = 2 → y ∈ centralizerSection H (pPrimeCoreOf 2 H) →
      centralizer ({y} : Set G) ≤ M) : Stage2Concl1 x K M Q H :=
  ⟨h.K_le, h.Q_le, h.Q_syl, h.H_min, h.H_G2, h.H_tri, h.O_ne, hp⟩

end Core

structure ShapeInCent {N : Type} [Group N] [Finite N] (H : Subgroup N) (t : N) (L : Subgroup N) : Prop where
  normal : H.Normal
  simple : IsSimpleGroup ↥H
  faithful : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1
  inv : orderOf t = 2
  comp : IsCompIn (H ⊓ centralizer ({t} : Set N)) L
  shape : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧
    ∃ _ : Z.Normal, QShapeNS (↥L ⧸ Z)

@[expose] def InJ2M {G : Type} [Group G] (M : Subgroup G) (y : G) : Prop :=
  y ∈ M ∧ orderOf y = 2 ∧ centralizer ({y} : Set G) ≤ M

@[expose] def ControlsFusionElt {G : Type} [Group G] (M : Subgroup G) (y : G) : Prop :=
  ∀ g : G, g⁻¹ * y * g ∈ M → ∃ m ∈ M, m⁻¹ * y * m = g⁻¹ * y * g

@[expose] def Prop151For {G : Type} [Group G] (A M : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → centralizer ({a} : Set G) ≤ M

@[expose] def Stage2Thm2C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1Core x K M Q H → Stage2Concl2C M

namespace SD

abbrev centBarK {G : Type} [Group G] (M K : Subgroup G) : Subgroup (Mbar M) :=
  centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M))

end SD

end CFSG.GH74.Generic.BProg.B2
