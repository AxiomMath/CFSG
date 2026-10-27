module

public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def Lemma29Alt {G : Type} [Group G] (z : G) (k : Kind) (U : Subgroup G) : Prop :=
  HasNormal2Compl (centralizer (U : Set G)) ∨
    (IsClassicalKind k ∧ (∀ P : Sylow 2 ↥(O2Of (centralizer (U : Set G))), IsDihedral ↥P) ∧
      ((∀ u ∈ U, ¬ IsConj z u) ∨
        ∃ t g : G, SwapsComps z t ∧ conjugate (zpowers z ⊔ zpowers t) g = U)) ∨
    ((k = Kind.mcl ∨ k = Kind.ly) ∧ Lemma29b U)

@[expose] def Lemma29FirstAt {G : Type} [Group G] (z : G) (k : Kind) : Prop :=
  ∀ U : Subgroup G, IVK.IsFourSubgroup U → Lemma29Alt z k U

@[expose] def Lemma29First : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    Lemma29FirstAt z k

@[expose] def Lemma29NonSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ U : Subgroup G, IVK.IsFourSubgroup U → ∀ X : Subgroup G, X ≤ centralizer (U : Set G) →
      ¬ Group.IsSolvable ↥X →
      (IVK.IsL2 (↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X)) Odd ∨
        Nonempty ((↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X)) ≃* alternatingGroup (Fin 7)))

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
