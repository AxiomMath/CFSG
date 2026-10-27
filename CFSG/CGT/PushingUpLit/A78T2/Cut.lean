module

public import CFSG.CGT.PushingUpLit.A78T2.Data
public import CFSG.CGT.PushingUpLit.A78.ThreeSNonSylowSplit

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.BHS

@[expose] def T2FromCfg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥ → 3 ≤ e →
        ∃ S M M₂ : Subgroup G,
          T2Loc G L₁ L₂ (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T))
            (oTwoIn (L₁ ⊔ T) ⊓ oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) T S M M₂ e

@[expose] def T2Chain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L L₂ V V₂ Z J T S M M₂ : Subgroup G) (e : ℕ),
    T2Loc G L L₂ V V₂ Z J T S M M₂ e → False

@[expose] def T2Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥ → e = 2 →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → CFSG.GH74.SectionalTwoRankLE G 4

theorem nonSylowL3_of_cut (h₁ : T2FromCfg) (h₂ : T2Chain) (h₃ : T2Two) :
    Aschbacher78NonSylowL3 := by
  intro G _ _ L₁ L₂ T e cfg hZ hns
  by_cases he : e = 2
  · exact h₃ G L₁ L₂ T e cfg hZ he hns
  · obtain ⟨S, M, M₂, hloc⟩ :=
      h₁ G L₁ L₂ T e cfg hns hZ (by have := cfg.two_le; omega)
    exact (h₂ G L₁ L₂ _ _ _ _ T S M M₂ e hloc).elim

end CFSG.CGT.PushingUpLit.A78T2
