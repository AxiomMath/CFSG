module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.H13.L32NNotation
public import CFSG.Quasithin.H13.L32NStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Lemma1444One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 →
      IsElemAbelian 3 (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) ∧
        Nat.card ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) = 9

@[expose] def Lemma1444Two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
      V = fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G) ⊓
          CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g ∧
        Nat.card ↥(imageOTwoQuot (l32nH T V)
          (CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g)) = 2 ∧
        (∀ x ∈ imageOTwoQuot (l32nH T V)
            (CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g), x ≠ 1 →
          ∀ k ∈ imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)), x * k * x⁻¹ = k⁻¹) ∧
        ∀ x ∈ CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g,
          x ∉ pCoreOf 2 (l32nH T V) →
            Nat.card ↥(⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V) = 8 ∧
              ∃ a ∈ ⁅fsuU T V, Subgroup.zpowers x⁆ ⊔ fsuV1 T V, a ^ 2 ≠ 1

@[expose] def Lemma1444Four_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 → V = pCoreOf 2 L

@[expose] def Lemma1444Six_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 →
      (¬ ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L) ∧
      ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
        ∀ A : Subgroup G,
          A ≤ fsuU T V ⊔ CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g →
          IsElemAbelian 2 A → Nat.card A ≤ 8

@[expose] def Lemma1444Seven_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 →
      l32nH T V = oTwoUpper (l32nH T V) ⊔ T ∧ Subgroup.normalizer (L : Set G) = L ⊔ T

@[expose] def Lemma1445One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 → Subgroup.normalizer (L : Set G) = L

@[expose] def Lemma1445Two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 →
      fsuU T V = pCoreOf 2 (l32nH T V) ∧
        ∃ N : Subgroup (OTwoQuot (l32nH T V)), N.Normal ∧ IsElemAbelian 3 N ∧
          Nat.card N = 9 ∧ N.index = 2

@[expose] def Lemma1445Three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
      T = fsuU T V ⊔ CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g

@[expose] def Lemma14413Big_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
      ∃ X : Subgroup G, X ≠ lOne L (fsuV1 T V) ∧ X ≤ l32nH T V ∧
        T ≤ Subgroup.normalizer (X : Set G) ∧ oTwoUpper X = X ∧
        (pCoreOf 2 X).relIndex X = 3 ∧ Nat.card ↥⁅V₂, X⁆ = 8 ∧
        ⁅V₂, X⁆ ≤ fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G) ⊓
          CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g ∧
        Nonempty (↥(L ⊔ T ⊔ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊔ (lOne L V₂ ⊔ X ⊔ T)) ≃*
          Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))

end CFSG.Quasithin.H13
