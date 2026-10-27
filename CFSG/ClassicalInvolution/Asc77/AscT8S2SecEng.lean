module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBasic
public import CFSG.ClassicalInvolution.Asc77.AscMuTabGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8S2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem muIsoZ2_of_unique_memberE {J₀ : Subgroup G}
    (hiff : ∀ ρ σ : Rep Ω W, (MuTab.muTabElt ρ = MuTab.muTabElt σ ↔ ρ.K = σ.K))
    (hmul : ∀ ρ : Rep Ω W, MuTab.muTabElt ρ * MuTab.muTabElt ρ = 1) (hW : W ∈ WSet Ω)
    (hρ : Nonempty (Rep Ω W)) (h : ∀ ρ : Rep Ω W, ρ.K = J₀) : MuIsoZ2 Ω W := by
  obtain ⟨ρ₀⟩ := hρ
  have hall : ∀ d ∈ muDelta Ω W, d = MuTab.muTabElt ρ₀ := by
    intro d hd
    obtain ⟨ρ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
    rw [hiff, h ρ, h ρ₀]
  have h2 : MuTab.muTabElt ρ₀ * MuTab.muTabElt ρ₀ = 1 := hmul ρ₀
  have h1 : MuTab.muTabElt ρ₀ ≠ 1 := muDelta_ne_one hW (MuTab.muTabElt_mem ρ₀)
  refine MuTab.nonempty_mulEquiv_z2 h2 h1 ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd => ?_
  rw [hall d hd]
  exact Subgroup.subset_closure rfl

end T8S2

end CFSG.ClassicalInvolution.Asc77
