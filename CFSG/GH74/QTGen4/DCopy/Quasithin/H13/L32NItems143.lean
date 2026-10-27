module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32NItems143

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def StmtL32NModule_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    IsElemAbelian 2 V ∧ Nat.card V = 8 ∧ L ⊔ T ≤ Subgroup.normalizer (V : Set G) ∧
      Nat.card ↥(fsuV1 T V) = 2 ∧
      ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1

@[expose] def Lemma1433Five_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14_3_1One G T L → FSU G T L V →
    Subgroup.normalizer (V : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)

@[expose] def Lemma14323Ge_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    2 ^ 4 * Nat.card ↥(centerOf (fsuU T V)) ≤ Nat.card ↥(fsuU T V)

@[expose] def Lemma14332_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) → Concl14332 T V

@[expose] def Lemma14333_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) → Concl14333 T L V

end CFSG.Quasithin.H13
