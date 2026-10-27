module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32ASk1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_4_two_three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G), Hyp147 G T L V →
    A6.IsV2 T V V₂ →
    (L32A.i2 T V V₂ ≤ Subgroup.normalizer (V₂ : Set G) ∧
      Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (L32A.i2 T V V₂ : Set G)) ∧
    L32A.i2 T V V₂ = L₁Of L V₂ ⊔ pCoreOf 2 (A6.g1 T V) ∧
    Nonempty (↥(L32A.i2 T V V₂) ⧸ CFSG.pCore 2 ↥(L32A.i2 T V V₂) ≃* Equiv.Perm (Fin 3)) ∧
    L₁Of L V₂ = oTwoRes (L32A.i2 T V V₂) ∧
    CFSG.pRank 3 ↥(Subgroup.centralizer (V₂ : Set G)) ≤ 1

@[expose] def Lemma14_7_11_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ¬ quasithinO2QuotientIso H (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      ¬ quasithinO2QuotientIso H ↥(alternatingGroup (Fin 6)) ∧
      ¬ quasithinO2QuotientIso H (Equiv.Perm (Fin 6))

@[expose] def Thm14_7_14_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ¬ IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))

@[expose] def Lemma14_7_27_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ ∨
      CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (L32A.l1 T L V)

@[expose] def Lemma14_7_28_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ ∨
      CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (L32A.l1 T L V)

@[expose] def Thm14_7_29_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp147 G T L V →
    ∀ X : Subgroup G, L32A.l1 T L V ⊔ T ≤ X → X ≤ A6.g1 T V → Group.IsSolvable ↥X →
      X ≤ Subgroup.normalizer (L : Set G)

end CFSG.Quasithin.H13
