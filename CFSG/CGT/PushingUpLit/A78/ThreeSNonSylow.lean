module

public import CFSG.CGT.PushingUpLit.A78.Cfg
public import CFSG.GH74.Defs

public section

namespace CFSG.CGT.PushingUpLit.A78

@[expose] def Aschbacher78ThreeSNonSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ), A78Cfg G L₁ L₂ T e →
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → CFSG.GH74.SectionalTwoRankLE G 4

end CFSG.CGT.PushingUpLit.A78
