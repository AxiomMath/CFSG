module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FrameParts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12

@[expose] def EndgameL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55 G z k S T Tstar p H P g X Y →
      ∀ (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
        [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ)
        (P' R : Subgroup Γ), Frame55 k p ρ K a P' R → Link55 H P T g K a P' R →
          (∃ n : ℕ, 1 ≤ n ∧ LieModel (↥K ⧸ center ↥K) .PSL 3 p n) → False

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
