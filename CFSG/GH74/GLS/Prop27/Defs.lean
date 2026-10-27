module

public import CFSG.GH74.Uniqueness.Statements
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.E2.ComponentsFacts
public import CFSG.GH74.E2.Shapes
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup Blueprint Assembly.LowTwoRank CFSG.GH74.E2

@[expose] def S_prop27G : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → Gen4 G → KGH G → IsLB2Type G →
    pRank 2 G = 3 → L2Sub G InC2 → L2Meets G (fun K _ => HasL2Model K IsFM9)

@[expose] def S_lemma26G : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → Gen4 G → KGH G → pRank 2 G = 3 →
    L2Sub G (fun K _ => InC2 K ∧ ¬ HasL2Model K IsFM9) →
      IsRestrictedEvenType G ∨
        ∃ x : G, orderOf x = 2 ∧ pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥

@[expose] def Shapes7 (K : Type) [Group K] : Prop :=
  (center K = ⊥ ∧ (ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨ ShapeSz8 K ∨ ShapeM11 K)) ∨
    Shape2M12 K ∨ Shape2Sz8 K

@[expose] def S_Thm182_P27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → KGH G →
    Gen4 G → ∀ S : Sylow 2 G, Open.pRank 2 (S : Subgroup G) = 3 →
      Uniqueness.gammaElem (S : Subgroup G) ≠ ⊤ →
        NativeSporadic.IsSporadic G .J1 ∨ CFSG.BenderSuzuki.IsBenderGroup G

structure Prop27TableFacts : Prop where
  sylow_rank_simple : ∀ (K : Type) [Group K] [Finite K], Shapes7 K → center K = ⊥ →
    ∃ T : Subgroup K, IsPGroup 2 T ∧ 2 ≤ Group.rank T
  sylow_rank_cover : ∀ (K : Type) [Group K] [Finite K], Shapes7 K → center K ≠ ⊥ →
    ∃ T : Subgroup K, IsPGroup 2 T ∧ 3 ≤ Group.rank T

@[expose] def LocBal2 (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X), N.Normal → P ↥N →
    centralizer (N : Set X) = ⊥ → ∀ e : X, orderOf e = 2 →
      pPrimeCore 2 ↥(centralizer ({e} : Set X)) = ⊥

structure Prop27LocalBalance : Prop where
  L28 : LocBal2 ShapeL28
  L33 : LocBal2 ShapeL33
  U33 : LocBal2 ShapeU33
  M11 : LocBal2 ShapeM11
  M12 : LocBal2 fun S _ => NativeSporadic.IsSporadic S .M12
  Sz8 : LocBal2 ShapeSz8

structure Prop27Leaves : Prop where
  generic : Generic.GenericKnownFacts
  e2 : E2ComponentFacts
  thm182 : S_Thm182_P27
  localBalance : Prop27LocalBalance

end CFSG.GH74.GLS.Prop27
