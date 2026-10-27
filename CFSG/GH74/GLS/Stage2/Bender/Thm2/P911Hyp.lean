module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

structure Hyp911 {G : Type} [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (X V N : Subgroup G) : Prop where
  ctx : Ctx9 G z k S M p
  hXP : X ≤ Op p M
  hX0 : X ≠ ⊥
  hzX : z ∈ normalizer (X : Set G)
  hXc : ⁅X, zpowers z⁆ = X
  hN : IsCoatom N
  hXN : normalizer (X : Set G) ≤ N
  hV : V ≤ Op p M ⊓ N ⊓ Cen z
  hVe : IsElementaryAbelian p ↥V
  hV2 : Nat.card ↥V = p ^ 2
  hv : ∀ v ∈ V, v ≠ 1 → NN z p (Op p M) (zpowers v)
  hFm : Fm N = Op p N
  hEm : Em N ≠ ⊥

@[expose] def Lemma913a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (X V N : Subgroup G), Hyp911 z k S M p X V N → X ≤ centralizer (Em N : Set G)

@[expose] def End911 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (X V N : Subgroup G), Hyp911 z k S M p X V N → X ≤ centralizer (Em N : Set G) →
      ∀ J : Subgroup ↥N, IsComponent J → LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 2 → False

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
