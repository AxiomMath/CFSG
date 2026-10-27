module

public import CFSG.GH74.GLS.C3.Layer1.EvenStd
public import CFSG.GH74.GLS.C3.Layer1.St1Thm7
public import CFSG.Blueprint.EvenStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

@[expose] def RankTwoStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, CFSG.Open.standardComponentIsStandard L →
    2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (L : Set G)) →
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .Suz ∨
        NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Ru ∨
        NativeSporadic.IsSporadic G .Co1)

@[expose] def EvenResidualStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, CFSG.Open.standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
    IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L) →
    ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L

@[expose] def CTSSStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, CFSG.Open.standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
    IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L) →
    ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L →
    NativeSporadic.SporadicRep (L ⧸ Subgroup.center L) →
    (NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12 ∨
      NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .J2 → Subgroup.center L = ⊥) →
    CFSG.Blueprint.Recognition.EvenSporadicOutcome G

@[expose] def SmallLieStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, CFSG.Open.standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
    IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L) →
    ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L →
    (CFSG.Blueprint.Recognition.Exact.ResidualB L ∨ CFSG.Blueprint.Recognition.Exact.ResidualC L ∨
      CFSG.Blueprint.Recognition.Exact.ResidualD L) →
    CFSG.Blueprint.Recognition.EvenSporadicOutcome G

@[expose] def DihedralStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (S : Sylow 2 G) (n : ℕ), 2 ≤ n → Nonempty (↥(S : Subgroup G) ≃* DihedralGroup (2 ^ (n - 1))) →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7))

@[expose] def SporadicOrders : Prop :=
  ∀ (X : Type) [Group X],
    (NativeSporadic.IsSporadic X .He → Nat.card X = 4030387200) ∧
    (NativeSporadic.IsSporadic X .M12 → Nat.card X = 95040) ∧
    (NativeSporadic.IsSporadic X .J2 → Nat.card X = 604800) ∧
    (NativeSporadic.IsSporadic X .HS → Nat.card X = 44352000)

@[expose] def G2FourOrder : Prop :=
  ∀ (X : Type) [Group X], LieModel X .G2 0 2 2 → Nat.card X = 251596800

@[expose] def G2DerivedU33 : Prop :=
  ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
    LieModel ↥⁅Chevalley.adjointGroup .G2 k, Chevalley.adjointGroup .G2 k⁆ .PSU 3 3 1

@[expose] def A8NotL34 : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSL 3 2 2 → ∀ n : ℕ, 5 ≤ n →
    IsEmpty (X ≃* alternatingGroup (Fin n))

structure Phase2Inputs : Prop where
  bIg : GH74.GLS.B_ig_6_10
  bPU4 : GH74.GLS.B_cor_PU4
  rankTwo : RankTwoStd
  smallLie : SmallLieStd
  quat : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels → (∀ (G :
      Type) [Group G] [Finite G] (L : Subgroup G), CFSG.OddStandard.StandardSetting G L → ∀ (S :
      Sylow 2 (Subgroup.centralizer (L : Set G))) (r : ℕ), 3 ≤ r → Nonempty (↥(S : Subgroup
      (Subgroup.centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (r - 2))) → OddLieType G ∨
      NativeSporadic.IsSporadic G .M12)
  dihedral : DihedralStd
  orders : SporadicOrders
  g2Four : G2FourOrder
  a8 : A8NotL34
  g2Derived : G2DerivedU33

end CFSG.OddStandard.SmallF3.HypA2
