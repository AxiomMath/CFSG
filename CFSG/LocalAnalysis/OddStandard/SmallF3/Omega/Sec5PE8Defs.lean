module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def Sec5PE8AutStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 2 Y), Nonempty (↥P ≃* DihedralGroup 4) →
    Sec5SH8Shape P → ∀ tb : Y, tb ∈ (P : Subgroup Y) → orderOf tb = 2 →
      (∀ g ∈ (P : Subgroup Y), tb * g = g * tb) → ∀ κ : MulAut Y, Odd (orderOf κ) →
        (∀ x ∈ (P : Subgroup Y), κ x = x) →
          (∀ w : Y, w * tb = tb * w → Nat.Coprime (orderOf w) 6 → κ w = w) → κ = 1

end CFSG.OddStandard.SmallF3.Omega
