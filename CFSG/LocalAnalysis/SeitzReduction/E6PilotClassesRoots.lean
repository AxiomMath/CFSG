module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.SeitzReduction.E6Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem e6RepFrame_iform_highRoot (κ : Fin 3) : ∀ β ∈ e6RepFrame κ,
    iform (highRoot .E6) β = 0 ∧ iform (-highRoot .E6) β = 0 := by
  revert κ
  decide +kernel

variable {K : Type} [Field K]

theorem coe_e6Rep_mem_centralizer_highRootSL2 (κ : Fin 3) :
    (e6Rep K κ : ModGL .E6 K) ∈
      Subgroup.centralizer (EPilot.highRootSL2 .E6 K : Set (ModGL .E6 K)) := by
  have hτ : Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inr (Or.inl rfl)
  have key : ∀ {ρ : Fin Tag.E6.rank → ℤ}, IsRoot .E6 ρ → (∀ β ∈ e6RepFrame κ, iform ρ β = 0) →
      rootSubgroup .E6 K ρ ≤
        Subgroup.centralizer ({(e6Rep K κ : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
    intro ρ hρ h0
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, coe_e6Rep]
    exact (Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact classD4_commute_pinnedX hτ hρ (e6RepFrame_perp κ β hβ).1 (h0 β hβ).ge c 1).eq
  have hle : EPilot.highRootSL2 .E6 K ≤
      Subgroup.centralizer ({(e6Rep K κ : ModGL .E6 K)} : Set (ModGL .E6 K)) :=
    sup_le (key (isRoot_highRoot .E6) fun β hβ => (e6RepFrame_iform_highRoot κ β hβ).1)
      (key (IsRoot.neg (isRoot_highRoot .E6)) fun β hβ => (e6RepFrame_iform_highRoot κ β hβ).2)
  exact Subgroup.mem_centralizer_iff.2 fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

end CFSG.SeitzReduction.E6Pilot
