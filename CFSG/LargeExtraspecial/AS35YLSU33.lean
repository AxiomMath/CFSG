module

public import CFSG.LargeExtraspecial.AS35YLSCen
public import CFSG.LargeExtraspecial.AS35YLSIrr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace S14

@[expose] def Asc512U33ModuleInput : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSU 3 3 1 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V), (QuadraticMap.polarBilin Q).Nondegenerate →
      ∀ ρ : X →* (V ≃ₗ[ZMod 2] V), Function.Injective ρ → (∀ x v, Q (ρ x v) = Q v) →
      (∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∀ d : X, d ≠ 1 → d * d = 1 → finrank (ZMod 2) (commSpace (ρ d)) ≤ 2 → False

theorem asc512InspU33_of (hmod : Asc512U33ModuleInput) (h5127 : Asc512FiveTwelveSevenStmt)
    (hfix : Asc512FixFreeStmt) : Asc512InspFor Asc512U33Fam := by
  intro G _ _ S hS hst h
  exfalso
  have hfixS := hfix G S hS hst (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨hnd, hL⟩ := h
  have hc := Setting.center_LbarAsc_eq_bot_YL hS hst hnd
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨d, -, hd1, hdd, hdA⟩ := Setting.exists_inv_of_center_eq_bot_YL hS hst hc
  have hirrS := Setting.lbarIrred_of_fixFree_YL hS hst hnd h5127 hfixS
  exact hmod _ hL S.Qt S.q S.q_nondegenerate (Setting.actHat_YL hc)
    (Setting.actHat_YL_injective hc) (Setting.actHat_YL_isometry hc)
    (Setting.irred_actHat_YL hc hirrS) d hd1 hdd hdA.2.2.2.1.le

end S14

end CFSG.LargeExtraspecial
