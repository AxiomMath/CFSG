module

public import CFSG.CGT.PushingUpLit.A78Sp4.Data
public import CFSG.CGT.PushingUpLit.A78.ThreeSNonSylowSplit

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.BHS

@[expose] def Sp4FromCfg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥ →
        ∃ S M M₂ : Subgroup G,
          Sp4Loc G L₁ L₂ (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T))
            (oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G))
            (oTwoIn (L₂ ⊔ T) ⊓ Subgroup.centralizer (L₂ : Set G))
            (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) T S M M₂ e

@[expose] def Sp4ChainGE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G) (e : ℕ),
    Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e → 3 ≤ e → False

@[expose] def Sp4ChainTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G) (e : ℕ),
    Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e → e = 2 → False

theorem nonSylowSp4GE3_of_cut (h₁ : Sp4FromCfg) (h₂ : Sp4ChainGE3) :
    Aschbacher78NonSylowSp4GE3 := by
  intro G _ _ L₁ L₂ T e cfg hZ he hns
  obtain ⟨S, M, M₂, hloc⟩ := h₁ G L₁ L₂ T e cfg hns hZ
  exact (h₂ G L₁ L₂ _ _ _ _ _ T S M M₂ e hloc he).elim

theorem nonSylowSp4Two_of_cut (h₁ : Sp4FromCfg) (h₂ : Sp4ChainTwo) :
    Aschbacher78NonSylowSp4Two := by
  intro G _ _ L₁ L₂ T e cfg hZ he hns
  obtain ⟨S, M, M₂, hloc⟩ := h₁ G L₁ L₂ T e cfg hns hZ
  exact (h₂ G L₁ L₂ _ _ _ _ _ T S M M₂ e hloc he).elim

end CFSG.CGT.PushingUpLit.A78Sp4
