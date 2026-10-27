module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Statements

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

@[expose] def Stmt5_2_L2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsL2Choice T H L₂ →
      IsSylowTwoOf (T ⊓ L₂) L₂ ∧ oTwoUpper H = conjClosure L₂ T

@[expose] def Stmt5_2_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsL2Choice T H L₂ →
    ¬ LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      sec52S M H ≤ Subgroup.normalizer (L₂ : Set G)

@[expose] def Stmt5_2_4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
      D ≤ Subgroup.normalizer (oTwoUpper H : Set G) ∧
      (D ≤ Subgroup.normalizer (B : Set G) ∧ B ≤ Subgroup.normalizer (D : Set G)) ∧
      (B ≤ Subgroup.normalizer (sec52S M H : Set G) ∧
        D ≤ Subgroup.normalizer ((sec52S M H ⊓ L₂ : Subgroup G) : Set G) ∧
        (D : Set G) * (sec52S M H : Set G) = (sec52S M H : Set G) * (D : Set G)) ∧
      D ⊔ sec52S M H ⊔ B ≤ Subgroup.normalizer (L₂ : Set G)

end CFSG.Quasithin.H13
