module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Lem12220Pick_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
      ∃ h ∈ H, h ∉ Subgroup.normalizer (L : Set G) ∧
        (pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).relIndex V = 2 ∧
        ∃ _ : IsMulCommutative ↥V, autOn (pCoreOf 2 (V ⊔ CFSG.conjugate V h)) V =
          transvAxis ((pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).subgroupOf V)

@[expose] def Lem12220Transv_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    ∀ _ : IsMulCommutative ↥V, ∀ A : Subgroup ↥V, A.index = 2 → 4 ≤ Nat.card A →
      transvAxis A ≤
        autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V →
      ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nat.card V = 2 ^ n ∧ autOn L V = ⊤ ∧
        BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1 ∧
        T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G))

@[expose] def Lem12221_23_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
    ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) → Nat.card V = 2 ^ n → autOn L V = ⊤ →
    (∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) →
    T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) →
      ∃ (P U I : Subgroup G) (h : G) (p : ℕ), Chain12_2_23 T L V H P U I h n p

@[expose] def Lem12224Block_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Chain12_2_23 T L V H P U I h n p → IsLnBlock L n

end CFSG.Quasithin.H13
