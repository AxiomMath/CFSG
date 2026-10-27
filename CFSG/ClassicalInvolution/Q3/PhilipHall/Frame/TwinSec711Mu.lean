module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuCtx

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6.Mu
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem nonempty_mulEquiv_klein
  mem_omegaNbr_of_commutes)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem muIsoE4_of_two (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {ρ σ : Rep Ω W}
    (hne : ρ.K ≠ σ.K) (hσρ : σ.K ∈ omegaNbr Ω ρ.K)
    (hall : ∀ τ : Rep Ω W, τ.K = ρ.K ∨ τ.K = σ.K) : MuIsoE4 Ω W := by
  have hcomm : muTabElt ρ * muTabElt σ = muTabElt σ * muTabElt ρ :=
    (muTab_commute_iff hP hW ρ σ hne).mpr hσρ
  have hd : muTabElt ρ ≠ muTabElt σ := fun h => hne ((muTabElt_eq_iff hP hW ρ σ).mp h)
  have hall' : ∀ d ∈ muDelta Ω W, d = muTabElt ρ ∨ d = muTabElt σ := by
    intro d hd'
    obtain ⟨τ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd'
    rcases hall τ with h | h
    · exact Or.inl ((muTabElt_eq_iff hP hW τ ρ).mpr h)
    · exact Or.inr ((muTabElt_eq_iff hP hW τ σ).mpr h)
  have h1 : muTabElt ρ * muTabElt ρ = 1 := muDelta_mul_self hP.hyp hW (muTabElt_mem ρ)
  have h2 : muTabElt σ * muTabElt σ = 1 := muDelta_mul_self hP.hyp hW (muTabElt_mem σ)
  refine nonempty_mulEquiv_klein h1 h2 hcomm (muDelta_ne_one hW (muTabElt_mem ρ))
    (muDelta_ne_one hW (muTabElt_mem σ)) hd ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd' => ?_
  rcases hall' d hd' with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711
