module

public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LargeExtraspecial.DW

open Module CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

@[expose] def DW2ModuleInputD4 : Prop :=
  ∀ (X : Type) [Group X], LieModel X .trialityD4 0 2 1 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (ρ : X →* (V ≃ₗ[ZMod 2] V)), Function.Injective ρ → ∀ d : X, d ≠ 1 → d * d = 1 →
      3 ≤ finrank (ZMod 2) (commSpace (ρ d))

end CFSG.LargeExtraspecial.DW
