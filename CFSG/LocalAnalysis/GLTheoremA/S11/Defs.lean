module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Hyp111 (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  mu : p ∈ Mu G m
  bmax : GLAIsBmax p B
  mem : x ∈ B
  ne_one : x ≠ 1
  comp : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L
  norm : B ≤ Subgroup.normalizer (L : Set G)
  cent : CentModEqZpowers p B L x
  qs : CFSG.Open.IsQuasisimple ↥L
  idiag : InnerDiagMarking B L

@[expose] def RQuad (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  p ∈ Mu G m ∧ IsSStarMax p B x L ∧ InnerDiagMarking B L

@[expose] def LabelOf (L : Subgroup G) (lab : GLALabel) : Prop :=
  GLAMarking L fun lab' _ _ _ _ _ => lab' = lab

@[expose] def NoSplit16 (p : ℕ) (L : Subgroup G) : Prop :=
  ∀ lab : GLALabel, LabelOf L lab → ¬ GLASplit16 p lab

@[expose] def HalfSplit16At (p : ℕ) (L : Subgroup G) : Prop :=
  ∃ lab : GLALabel, LabelOf L lab ∧ GLAHalfSplit16 p lab (Subgroup.center ↥L = ⊥)

@[expose] def List110 (p : ℕ) (lab : GLALabel) (c : Prop) : Prop :=
  GLAHalfSplit16 p lab c ∧ ¬ GLASplit16 p lab

@[expose] def IsChev2 (K : Subgroup G) : Prop :=
  GLAMarking K fun _ _ _ _ _ _ => True

@[expose] def TrivialMultiplier (J : Subgroup G) : Prop :=
  ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ → ∀ π : E →* ↥J, Function.Surjective π →
    π.ker ≤ Subgroup.center E → π.ker = ⊥

@[expose] def JShape (lab : GLALabel) (z3 : Prop) (labJ : GLALabel) : Prop :=
  labJ.n = lab.n ∧
    (((lab.tag = .B ∨ lab.tag = .C) ∧ labJ.tag = .B ∧ labJ.rank + 1 = lab.rank) ∨
      (lab.tag = .D ∧ labJ.tag = .D ∧ labJ.rank + 1 = lab.rank) ∨
      (lab.tag = .F4 ∧ labJ.tag = .B ∧ labJ.rank = 3) ∨
      (lab.tag = .E7 ∧ labJ.tag = .D ∧ labJ.rank = 6) ∨
      (lab.tag = .E8 ∧ labJ.tag = .D ∧ labJ.rank = 7) ∨
      (lab.tag = .twA ∧ lab.rank = 5 ∧ ¬ z3 ∧ labJ.tag = .twA ∧ labJ.rank = 4) ∨
      (lab.tag = .twA ∧ lab.rank = 5 ∧ z3 ∧ labJ.tag = .twA ∧ labJ.rank = 5) ∨
      (lab.tag = .twE6 ∧ ¬ z3 ∧ labJ.tag = .twD ∧ labJ.rank = 5) ∨
      (lab.tag = .twE6 ∧ z3 ∧ labJ.tag = .twE6) ∨
      (lab.tag = .A ∧ lab.rank = 5 ∧ labJ.tag = .A ∧ labJ.rank = 3) ∨
      (lab.tag = .E6 ∧ labJ.tag = .D ∧ labJ.rank = 4) ∨
      (lab.tag = .A ∧ lab.rank = 8 ∧ labJ.tag = .A ∧ labJ.rank = 6))

@[expose] def IsSCIn (p : ℕ) (L A : Subgroup G) : Prop :=
  A ≤ L ∧ IsElemAbelian p A ∧
    ∀ g ∈ L ⊓ Subgroup.centralizer (A : Set G), orderOf g = p → g ∈ A

@[expose] noncomputable def weakCoreK (k q : ℕ) (P : Subgroup G) : Subgroup G :=
  sSup {N | ∃ X : Subgroup G, X ≤ P ∧ k ≤ CFSG.Open.pRank q X ∧
    k + 1 ≤ CFSG.Open.pRank q (X ⊔ (P ⊓ Subgroup.centralizer (X : Set G))) ∧
    N = Subgroup.normalizer (X : Set G)}

theorem weakCoreK_two (q : ℕ) (P : Subgroup G) : weakCoreK 2 q P = GLAWeakCore q P := rfl

end CFSG.LocalAnalysis.GLTheoremA
