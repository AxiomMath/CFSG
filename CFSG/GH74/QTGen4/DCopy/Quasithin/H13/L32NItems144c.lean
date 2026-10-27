module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32NItems144c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Lemma1442Big_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V),
      Case1442Three T V V₂ g D ∨ Case1442Four T V V₂ g D ∨ Case1442EightPrime T V V₂ g D ∨
        Case1442Five T V V₂ g D ∨ Case1442Six T V V₂ g D

@[expose] def Lemma14413BigM22_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), Case1442Six T V V₂ g D → Y1444Claim T L V V₂ g

end CFSG.Quasithin.H13
