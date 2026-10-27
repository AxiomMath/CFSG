module

public import CFSG.CGT.PushingUpLit.A78G0.Data
public import CFSG.CGT.PushingUpLit.A78S4.SideRec

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem g0Core_of_sides {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ} (hsimple : IsSimpleGroup G)
    (hchar : CFSG.Assembly.IsCharTwoType G) (hS : IsSylowOf 2 T ⊤) (hZ : Z ≠ ⊥)
    (hT : V ⊔ W = T) (P : S4Pair G L₁ L₂ V W Z Z₂ T e)
    (s₁ : Sp4Side G L₁ V Z (V ⊔ W) T (Subgroup.normalizer (V : Set G)) e)
    (s₂ : Sp4Side G L₂ W Z₂ (W ⊔ V) T (Subgroup.normalizer (W : Set G)) e) :
    G0Core G L₁ L₂ V W Z Z₂ e := by
  subst hT
  rw [sup_comm V W] at s₂
  exact ⟨hsimple, hchar, hS, hZ, P, s₁, s₂⟩

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.g0Core {L₁ L₂ T : Subgroup G} {e : ℕ}
    (cfg : A78Cfg G L₁ L₂ T e) (hS : IsSylowOf 2 T ⊤)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥)
    (hJT : oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) = T) :
    G0Core G L₁ L₂ (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T))
      (oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G))
      (oTwoIn (L₂ ⊔ T) ⊓ Subgroup.centralizer (L₂ : Set G)) e :=
  g0Core_of_sides cfg.simple cfg.charTwo hS hZ hJT (cfg.s4Pair hZ) (cfg.sp4Side hZ)
    (cfg.symm.sp4Side (cfg.s4Pair₀.Z₂_ne_bot hZ))

end CFSG.CGT.PushingUpLit.A78G0
