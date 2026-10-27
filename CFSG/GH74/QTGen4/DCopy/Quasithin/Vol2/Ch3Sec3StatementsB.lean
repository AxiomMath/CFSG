module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Setup
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

@[expose] def Stmt3_3_16_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 1 < n → Nat.card K = 2 ^ n →
      IsEmpty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSL 3 K)) ∧
      IsEmpty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSp 2 K)) ∧
      IsEmpty (↥(autOn L (vPlus L T)) ≃* ↥(quasithinG2 K))

@[expose] def Stmt3_3_17_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 6

@[expose] def Stmt3_3_18_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ n : ℕ, (n = 4 ∨ n = 5) →
      Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
        ∃ _ : IsMulCommutative ↥(vPlus L T), ¬ ∃ k : ℕ, 1 ≤ k ∧
          DirectSumOfCopies (autOn L (vPlus L T)) (commVPlus L T L) ⊥
            (FFModel.nat (StatedSL n (ZMod 2))) k

@[expose] def Stmt3_3_19_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsEmpty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

@[expose] def Stmt3_3_21_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsEmpty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))

@[expose] def Stmt3_3_22_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsEmpty (↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7))

@[expose] def Stmt3_3_23_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      (IsLnBlock L 3 ∧ D ≤ Subgroup.normalizer (preCenterAut T (vPlus L T) : Set G)) ∨
      ((HasNoncentralTwoChief L 2 ∧ ¬ HasNoncentralTwoChief L 4) ∧
        ¬ D ≤ Subgroup.normalizer (pCoreOf 2
          (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Set G))

@[expose] def Stmt3_3_24_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 ∨ IsHatA6Block L ∨ IsG2Block L ∨ IsLnBlock L 3

@[expose] def Stmt3_3_25_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    (IsAltBlockType L 6 ∨ IsG2Block L ∨ IsLnBlock L 3) ∧
    (tC L T ≠ ⊥ → ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      D ≤ Subgroup.normalizer
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : Set G) ∧
      D ≤ Subgroup.normalizer (pCoreOf 2
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) : Set G) ∧
      ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ pCoreOf 2
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) →
        L ⊔ T ≤ Subgroup.normalizer (R₀ : Set G) → ¬ D ≤ Subgroup.normalizer (R₀ : Set G)) ∧
    (tC L T = ⊥ → vPlus L T = qL L T ∨ IsAltBlockType L 6)

@[expose] def Stmt3_3_26_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∃ d ∈ D, d ∉ M ∧ ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T

@[expose] def Stmt3_3_27_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ d ∈ D, d ∉ M → ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T → tC L T ≠ ⊥ →
      tC L T ⊓ CFSG.conjugate (tC L T) d = ⊥ ∧ frattini ↥(tC L T) = ⊥ ∧
        (CFSG.conjugate (tC L T) d ≤ qL L T ∨ tC L T ≤ CFSG.conjugate (qL L T) d)

@[expose] def Stmt3_3_29_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T))

@[expose] def Stmt3_3_30_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6

@[expose] def Stmt3_3_31_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D → tC L T = ⊥

@[expose] def Stmt3_3_32_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ((qL L T = vPlus L T ∧ ∃ _ : IsMulCommutative ↥(vPlus L T),
        XMod.IsIrrSec ↥(autOn L (vPlus L T)) (⊥ : Subgroup ↥(vPlus L T)) ⊤) ∨
      (∃ _ : IsMulCommutative ↥(qL L T), Nat.card ↥(qL L T) = 2 ^ 5 ∧
        permQuot6Model.Realizes (autOn (L ⊔ T) (qL L T)) ⊤ ⊥)) ∧
    Nonempty (↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6)) ∧
    ∃ φ : ↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6),
      ((autOn T (vPlus L T)).subgroupOf (autOn (L ⊔ T) (vPlus L T))).map φ.toMonoidHom = sylowS6 ∧
      D ≤ Subgroup.normalizer (preimageAut T (vPlus L T)
        ((aBar2.map φ.symm.toMonoidHom).map (autOn (L ⊔ T) (vPlus L T)).subtype) : Set G)

@[expose] def Stmt3_3_Close_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D → False

theorem stmt3_3_1A_of_close_F4 (h : Stmt3_3_Close_F4) : Stmt3_3_1A_F4 :=
  stmt3_3_1A_of_false_F4 h

end CFSG.Quasithin.H13
