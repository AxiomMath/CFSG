module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadShape
public import CFSG.ClassicalInvolution.Q3.Q3AMBadDouble

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Defs


abbrev PspLayerFam {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Set (Subgroup (↥(centralizingLayer (nbrCoreFam Ω M a) {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer (nbrCoreFam Ω M a) {a}))) :=
  oddQuotientFamily (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a})
    (centralizingLayer (nbrCoreFam Ω M a) {a}))

@[expose] def PspNbhdKind {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G)
    (c : CompData) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι
      (↥(centralizingLayer (nbrCoreFam Ω M a) {a}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer (nbrCoreFam Ω M a) {a}))
      (PspLayerFam Ω M a)),
    ∃ ha : a ∈ centralizingLayer (nbrCoreFam Ω M a) {a},
      ShapeSingle D c (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(centralizingLayer (nbrCoreFam Ω M a) {a})) ⟨a, ha⟩)

@[expose] def PspNbhdS4 {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  PspNbhdKind Ω M a (CompData.model .PSU 4) ∨ PspNbhdKind Ω M a (CompData.model .POmegaOdd 3) ∨
    PspNbhdKind Ω M a (CompData.model .POmegaMinus 4)

@[expose] def PspNbhdTriple {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  MuTab.ShapeTriple (PspLayerFam Ω M a)

theorem pspNbhdKind_sp4_iff {G : Type} [Group G] {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G} :
    PspNbhdSp4 Ω M a ↔ PspNbhdKind Ω M a (CompData.model .PSp 2) := Iff.rfl

theorem pspNbhdKind_l4_iff {G : Type} [Group G] {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G} :
    PspNbhdL4 Ω M a ↔ PspNbhdKind Ω M a (CompData.model .PSL 4) := by
  constructor
  · rintro ⟨ι, hι, D, ha, hS⟩
    exact ⟨ι, hι, D, ha, hS⟩
  · rintro ⟨ι, hι, D, ha, hS⟩
    exact ⟨ι, hι, D, ha, hS⟩

@[expose] def PspTableLeaf : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    Asc77.CITBelowAll 3 (Nat.card G) → PspSetting Ω K J S R T W z t K' →
      PspNbhdSp4 Ω K z ∨ PspNbhdL4 Ω K z ∨ PspNbhdS4 Ω K z ∨ PspNbhdDouble Ω K z ∨
        PspNbhdTriple Ω K z

@[expose] def PspS4Leaf : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    Asc77.CITBelowAll 3 (Nat.card G) → PspSetting Ω K J S R T W z t K' → PspNbhdS4 Ω K z → False

@[expose] def PspTripleLeaf : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    Asc77.CITBelowAll 3 (Nat.card G) → PspSetting Ω K J S R T W z t K' →
      PspNbhdTriple Ω K z → False

@[expose] def C28_TriB : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    Asc77.CITBelowAll 3 (Nat.card G) → PspSetting Ω K J S R T W z t K' → False

end Defs

section Assembly


theorem c28_triB_of_leaves (hTab : PspTableLeaf) (hE : PspClose) (hS4 : PspS4Leaf)
    (hD : C28_DoubleB) (hTr : PspTripleLeaf) : C28_TriB := by
  intro hIH G _ _ _ Ω K J S R T W z t K' hCIT h
  rcases hTab hIH G Ω K J S R T W z t K' hCIT h with h1 | h1 | h1 | h1 | h1
  · exact hE hIH G Ω K J S R T W z t K' hCIT h (h.shapeE4_of_sp4 h1)
  · exact hE hIH G Ω K J S R T W z t K' hCIT h (h.shapeE4_of_l4 h1)
  · exact hS4 hIH G Ω K J S R T W z t K' hCIT h h1
  · exact hD G Ω K J S R T W z t K' h h1
  · exact hTr hIH G Ω K J S R T W z t K' hCIT h h1

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3AM
