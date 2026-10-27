module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuStar

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM710

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6.Mu
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem nonempty_mulEquiv_klein)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

@[expose] def PartnerUniq (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop :=
  ∀ ρ σ σ' : Rep Ω W, σ.K ∈ omegaNbr Ω ρ.K → σ'.K ∈ omegaNbr Ω ρ.K → σ.K = σ'.K

section Cls

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem cent_subset (ρ : Rep Ω W) {y : ↥(muGroup Ω W)}
    (hy : y ∈ Star3T.cent (muDelta Ω W) (muTabElt ρ)) :
    y = muTabElt ρ ∨ ∃ τ : Rep Ω W, y = muTabElt τ ∧ τ.K ∈ omegaNbr Ω ρ.K := by
  obtain ⟨hyD, hyc⟩ := hy
  obtain ⟨τ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hyD
  by_cases hτ : τ.K = ρ.K
  · exact Or.inl ((muTabElt_eq_iff hP hW τ ρ).mpr hτ)
  · exact Or.inr ⟨τ, rfl, (muTab_commute_iff hP hW ρ τ (Ne.symm hτ)).mp hyc.symm⟩

theorem muIso_E4_or_S4 (hU : PartnerUniq Ω W) (ρ σ : Rep Ω W) (hσ : σ.K ∈ omegaNbr Ω ρ.K) :
    MuIsoE4 Ω W ∨ MuIsoS4 Ω W := by
  classical
  have hTT := isTT_muDelta hP hW
  have hS := isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  have hne : ρ.K ≠ σ.K := fun h => hσ.2.1 h.symm
  have hcomm : muTabElt ρ * muTabElt σ = muTabElt σ * muTabElt ρ :=
    (muTab_commute_iff hP hW ρ σ hne).mpr hσ
  have hd : muTabElt ρ ≠ muTabElt σ := fun h => hne ((muTabElt_eq_iff hP hW ρ σ).mp h)
  have hσρ : ρ.K ∈ omegaNbr Ω σ.K :=
    (muTab_commute_iff hP hW σ ρ hne.symm).mp hcomm.symm
  have hcentρ : ∀ y ∈ Star3T.cent (muDelta Ω W) (muTabElt ρ),
      y = muTabElt ρ ∨ y = muTabElt σ := by
    intro y hy
    rcases cent_subset hP hW ρ hy with h | ⟨τ, rfl, hτ⟩
    · exact Or.inl h
    · exact Or.inr ((muTabElt_eq_iff hP hW τ σ).mpr (hU ρ τ σ hτ hσ))
  have hcentσ : ∀ y ∈ Star3T.cent (muDelta Ω W) (muTabElt σ),
      y = muTabElt σ ∨ y = muTabElt ρ := by
    intro y hy
    rcases cent_subset hP hW σ hy with h | ⟨τ, rfl, hτ⟩
    · exact Or.inl h
    · exact Or.inr ((muTabElt_eq_iff hP hW τ ρ).mpr (hU σ τ ρ hτ hσρ))
  by_cases hcon : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) (muTabElt ρ) a
  · right
    obtain ⟨a, ha, hconn⟩ := hcon
    have hk : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 2 := by
      have hset : Star3T.cent (muDelta Ω W) (muTabElt ρ) = {muTabElt ρ, muTabElt σ} := by
        ext y
        refine ⟨fun hy => ?_, ?_⟩
        · rcases hcentρ y hy with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rintro (rfl | rfl)
          · exact Star3T.self_mem_cent (muTabElt_mem ρ)
          · exact ⟨muTabElt_mem σ, hcomm.symm⟩
      rw [hset]
      exact Set.ncard_pair hd
    obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_four hTT hS (muTabElt_mem ρ) ha hconn hk
    exact ⟨e⟩
  · left
    push Not at hcon
    have hall : ∀ a ∈ muDelta Ω W, a = muTabElt ρ ∨ a = muTabElt σ := by
      intro a ha
      have hc := hcon a ha
      have key : ∀ b, Star3T.Conn (muDelta Ω W) (muTabElt ρ) b →
          b = muTabElt ρ ∨ b = muTabElt σ := by
        intro b hb
        induction hb with
        | refl => exact Or.inl rfl
        | @tail b c _ hbc ih =>
          have hcb : c ∈ Star3T.cent (muDelta Ω W) b := ⟨hbc.2.1, hbc.2.2.symm⟩
          rcases ih with rfl | rfl
          · rcases hcentρ c hcb with h | h
            · exact Or.inl h
            · exact Or.inr h
          · rcases hcentσ c hcb with h | h
            · exact Or.inr h
            · exact Or.inl h
      exact key a hc
    have h1 : muTabElt ρ * muTabElt ρ = 1 := muDelta_mul_self hP.hyp hW (muTabElt_mem ρ)
    have h2 : muTabElt σ * muTabElt σ = 1 := muDelta_mul_self hP.hyp hW (muTabElt_mem σ)
    refine nonempty_mulEquiv_klein h1 h2 hcomm (muDelta_ne_one hW (muTabElt_mem ρ))
      (muDelta_ne_one hW (muTabElt_mem σ)) hd ?_
    rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
    refine (Subgroup.closure_le _).mpr fun d hd' => ?_
    rcases hall d hd' with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end Cls

end CFSG.ClassicalInvolution.Q3.Q3AM710
