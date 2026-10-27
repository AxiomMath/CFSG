module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch6Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt6_1_4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    IsNatQuotCh5 L ⁅V, L⁆ n

@[expose] def Stmt6_1_5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    ∀ H : Subgroup G, IsHStar T M H →
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

@[expose] def Stmt6_1_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
    (IsNatModCh5 L ⁅V, L⁆ n ∧ (⁅L, thompsonJ T⁆ = L → V = ⁅V, L⁆)) ∧
    ⁅V, L⁆ = ⁅reducedAggregate (L ⊔ T), L⁆

@[expose] def Stmt6_1_10_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    (n : ℕ∞) ≤ rParam V ∧
    (∀ hV : IsElemAbelian 2 V, sParam hV = n ∧ mParam (autI hV M) = n) ∧
    ∀ g : G, conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) →
      ¬ conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) →
      mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) = n

@[expose] def Stmt6_1_11_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    ∀ g : G, conjSubgroup V g ≤ T → ⁅V, conjSubgroup V g⁆ ≠ ⊥ →
      ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g →
      ch6ZS T L V = ⁅V, conjSubgroup V g⁆ ∧ ch6ZS T L V = V ⊓ conjSubgroup V g ∧
      ∃ c ∈ Subgroup.centralizer (ch6ZS T L V : Set G), conjSubgroup V g = conjSubgroup V c

@[expose] def Stmt6_1_12_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    (¬ Subgroup.normalizer (wClos V 0 T : Set G) ≤ M ∨
      ¬ Subgroup.centralizer (cClos V 1 T : Set G) ≤ M) ∧
    (2 < n → ch6ZS T L V ≤ cClos V 1 T) ∧
    wClos V 0 T ≤ ch6S T L V

@[expose] def Stmt6_1_13_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    ∀ U : Subgroup G, U ≤ V → mQuot V U = n →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
      (∃ l ∈ L, U = conjSubgroup (ch6ZS T L V) l) ∨
      (Even n ∧ ∃ t ∈ M, IsInvolutoryFieldAut L t ∧ U = V ⊓ Subgroup.centralizer ({t} : Set G))

@[expose] def Stmt6_1_14_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    Even n → ∀ t ∈ T, IsInvolutoryFieldAut L t →
    ∀ U : Subgroup G, U = V ⊓ Subgroup.centralizer ({t} : Set G) →
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (M ⊓ Subgroup.normalizer (U : Set G)) →
      (IsSylowIn 2 (ch6Q T V ⊔ Subgroup.zpowers t) (Subgroup.centralizer (U : Set G)) ∧
        Subgroup.normalizer (thompsonJ (ch6Q T V ⊔ Subgroup.zpowers t) : Set G) ≤ M ∧
        IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (Subgroup.normalizer (U : Set G))) ∧
      (QuasithinUnique.CharTwo (Subgroup.normalizer (U : Set G)) ∧
        QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G))) ∧
      (wClos V 0 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V ∧
        (2 < n → wClos V 1 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V)) ∧
      (IsElemAbelian 2 (conjClosure V (Subgroup.normalizer (U : Set G))) ∧
        IsReducedMod (Subgroup.normalizer (U : Set G))
          (conjClosure V (Subgroup.normalizer (U : Set G))) U ∧
        ⁅pCoreOf 2 (Subgroup.normalizer (U : Set G)),
          conjClosure V (Subgroup.normalizer (U : Set G))⁆ ≤ U) ∧
      (2 < n → ∀ g : G, conjSubgroup V g ≤ Subgroup.centralizer (U : Set G) →
        V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) → ⁅V, conjSubgroup V g⁆ ≠ ⊥ →
        ¬ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M)

@[expose] def Stmt6_1_15_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
    ¬ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M ∨
      (n = 2 ∧ (¬ Subgroup.normalizer (wClos V 0 T : Set G) ≤ M ∨
        ¬ wClos V 1 T ≤ ch6S T L V))

@[expose] def Stmt6_1_27_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    n = 2 ∧
    (IsNatModCh5 L ⁅V, L⁆ 2 ∧ T ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
    Subgroup.centralizer (ch6ZS T L ⁅V, L⁆ : Set G) ≤ M ∧
    (¬ Subgroup.normalizer (wClos ⁅V, L⁆ 0 T : Set G) ≤ M ∨
      ¬ wClos ⁅V, L⁆ 1 T ≤ ch6S T L ⁅V, L⁆)

end CFSG.Quasithin.H13
