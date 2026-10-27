module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

@[expose] def SL2Key : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → ∀ (L : Type) [Group L],
    Nonempty (L ≃* ↥(StatedSL 2 F)) →
    ∀ (a : L ⧸ center L), a * a = 1 → a ≠ 1 → ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ Y : Subgroup (L ⧸ center L), IsPGroup p ↥Y →
        (∀ c : L ⧸ center L, c * a = a * c → c ∈ normalizer (Y : Set (L ⧸ center L))) →
        ∀ y ∈ Y, y * a = a * y

end CFSG.GH74.GLS.Stage2.Signalizer.L48
