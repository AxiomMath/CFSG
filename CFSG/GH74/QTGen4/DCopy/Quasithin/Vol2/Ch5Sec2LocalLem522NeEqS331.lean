module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_eq_D42_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L₂ : Set G))
      (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) →
    ∀ (Lh : Subgroup G) (k : ℕ),
      IsHatComp (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂ Lh →
      L₂ < Lh →
      ((SuzukiModel (O2Q L₂) 2 k ∧ Is2F4 k (O2Q Lh)) ∨
        (LieModel (O2Q L₂) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Lh))) →
      (∃ U P : Subgroup (O2Q Lh), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
        Group.IsSolvable ↥P) →
      False

@[expose] def Stmt5_2_2_eq_three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L₂ : Set G))
      (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) →
    ∀ Lh : Subgroup G,
      IsHatComp (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂ Lh →
      L₂ < Lh → LieModel (O2Q L₂) .PSL 2 2 2 → ¬ IsLieTypeChar2 (O2Q Lh) →
      ¬ IsRank2LieChar2 (O2Q Lh) →
      A314Statement
        (o2Img (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B)
          (T ⊓ Subgroup.normalizer (L₂ : Set G)))
        (o2Img (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) L₂)
        (o2Img (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) Lh) →
      p = 3

@[expose] def Stmt5_2_2_eq_cartan_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p → L₂ < oTwoUpper H → LieModel (O2Q L₂) .PSL 2 2 2 →
      IsElemAbelian 3 B ∧ Nat.card ↥B = 9 ∧
        Lin2.IsHallTwoPrimeOf (B ⊓ L₂) (L₂ ⊓ Subgroup.normalizer ((T ⊓ L₂ : Subgroup G) : Set G))

end CFSG.Quasithin.H13
