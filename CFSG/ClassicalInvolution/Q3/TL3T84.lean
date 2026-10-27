module

public import CFSG.ClassicalInvolution.Q3.TL3T83

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {n : ℕ}

theorem CSetting.false_of_labCtx (hS : CSetting 3 IH Ω K J) (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) (ctx : LabCtx I) : False := by
  have hn5 : 5 ≤ n := hn
  have hC := hS.toCHyp
  have hΩ : ∀ L ∈ Ω, ∀ g : G, conjSub g L ∈ Ω := fun L hL g =>
    hS.cex.hyp.conjInvariant g L hL
  obtain ⟨hti, hti'⟩ := CHyp.swap_inv ctx.D.ht ctx.D.ht'
  have hP₂ : ∀ N ∈ orbOf (TC.nbrAdj Ω) J K, ∃ σ : alternatingGroup (Fin (n + 4)),
      ∃ M ∈ centMembers Ω ctx.D.u, N = conjSub (ctx.f σ) M := by
    intro N hN
    have hM : conjSub ctx.D.t⁻¹ N ∈ orbOf (TC.nbrAdj Ω) K J := by
      rw [← hC.conjSub_orb_swap hti hti']
      exact ⟨N, hN, rfl⟩
    obtain ⟨σ, M, hM1, e⟩ := ctx.chart2 hS hn5 (ctx.D.hπY hM)
    refine ⟨σ, M, hM1, ?_⟩
    rw [← e, conjSub_conjSub_inv]
  have hDisj : n + 4 = 9 → (ctx.labHyp' hn5).Disj := by
    intro h9
    have hn5e : n = 5 := by omega
    exact ctx.disj_five hS hn5 (hmove_five_of_eq hn5e hS ctx.D ctx.E.hc₁ ctx.subHyp_common
      ctx.over_common_subset ctx.E.hcorr)
  obtain ⟨lab, hlab, hinj, hsurj, hloc⟩ := (ctx.labHyp' hn5).exists_labelling' hDisj hΩ
    hS.cex.trans ctx.D.hπY hC.pSpan_orb_sup_eq_top hP₂
  obtain ⟨I'⟩ := nonempty_aeIdent_of_labels (m := n + 4) (by omega) (by omega) hS.cex.gen
    (fun L hL => by rw [hS.cex.card L hL]; norm_num) hΩ (hS.exists_moved_member hn I) lab hlab
    hinj hsurj hloc
  exact hS.cex.not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n + 4, by omega, ⟨I'⟩⟩)))))

theorem CSetting.false_of_aeIdent_of_model117 (hS : CSetting 3 IH Ω K J) {n : ℕ} (hn : 5 ≤ n)
    (hM : Model117At n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) : False := by
  obtain ⟨ctx⟩ := hS.nonempty_labCtx hn hM I
  exact hS.false_of_labCtx hn I ctx

end CFSG.ClassicalInvolution.Q3.TC.Thin
