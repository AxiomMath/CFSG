module

public import CFSG.CGT.PushingUpLit.A78.ThreeSNonSylow

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.CGT.PushingUpLit.BHS

@[expose] def Aschbacher78NonSylowL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥ →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → CFSG.GH74.SectionalTwoRankLE G 4

@[expose] def Aschbacher78NonSylowSp4GE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥ → 3 ≤ e →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → CFSG.GH74.SectionalTwoRankLE G 4

@[expose] def Aschbacher78NonSylowSp4Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥ → e = 2 →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → CFSG.GH74.SectionalTwoRankLE G 4

theorem threeSNonSylow_of_split (h₁ : Aschbacher78NonSylowL3) (h₂ : Aschbacher78NonSylowSp4GE3)
    (h₃ : Aschbacher78NonSylowSp4Two) : Aschbacher78ThreeSNonSylow := by
  intro G _ _ L₁ L₂ T e cfg hns
  by_cases hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥
  · exact h₁ G L₁ L₂ T e cfg hZ hns
  · by_cases he : e = 2
    · exact h₃ G L₁ L₂ T e cfg hZ he hns
    · exact h₂ G L₁ L₂ T e cfg hZ (by have := cfg.two_le; omega) hns

end CFSG.CGT.PushingUpLit.A78
