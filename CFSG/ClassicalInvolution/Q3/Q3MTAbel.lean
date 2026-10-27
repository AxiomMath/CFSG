module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuTab
public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6.Mu
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem nonempty_mulEquiv_klein
  mem_omegaNbr_of_commutes)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_rep_pair_of_omegaNbr (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    ∃ g : G, ∃ ρ σ : Rep Ω W, ρ.K = conjSub g K ∧ σ.K = conjSub g J := by
  obtain ⟨hJΩ, -, R', hR'Ω, hR'J, hR'N⟩ := hJ
  have hR'syl : IsSylow2In R' J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hP.hyp hJΩ hR'Ω hR'J
  obtain ⟨R, hRK, hRn⟩ := Asc77.T3.exists_sylow_normalized hR'syl.2.1 hR'N
  have hRR' : IsPGroup 2 ↥(R' ⊔ R) :=
    hR'syl.2.1.to_sup_of_normal_right' hRK.2.1 (fun w hw => mem_normalizer_iff_conjSub_eq.mpr
      (hRn w hw))
  obtain ⟨g, hg⟩ := exists_rep_of_member_sylow hP hW ![K, J] ![R, R'] (by
    intro i; fin_cases i
    · exact hK
    · exact hJΩ) (by
    intro i; fin_cases i
    · exact hRK
    · exact hR'syl) (R' ⊔ R) hRR' (by
    intro i; fin_cases i
    · exact le_sup_right
    · exact le_sup_left)
  obtain ⟨ρ, hρ⟩ := hg 0
  obtain ⟨σ, hσ⟩ := hg 1
  exact ⟨g, ρ, σ, hρ, hσ⟩

section Shapes

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem muIsoE4_of_shape (hs : ∀ K ∈ Ω, omegaStarNbr Ω K ⊆ omegaNbr Ω K)
    (htri : ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ L ∈ omegaNbr Ω K, L ∈ omegaNbr Ω J → False)
    (hedge : ∃ K ∈ Ω, (omegaNbr Ω K).Nonempty) : MuIsoE4 Ω W := by
  obtain ⟨K, hK, J, hJ⟩ := hedge
  obtain ⟨g, ρ, σ, hρ, hσ⟩ := exists_rep_pair_of_omegaNbr hP hW hK hJ
  have hne : ρ.K ≠ σ.K := by
    rw [hρ, hσ]
    exact fun h => hJ.2.1 ((conjSub_inj g).mp h).symm
  have hσρ : σ.K ∈ omegaNbr Ω ρ.K := hs _ ρ.hK (muTab_omegaStar hP hW ρ σ hne)
  have hcomm : muTabElt ρ * muTabElt σ = muTabElt σ * muTabElt ρ :=
    (muTab_commute_iff hP hW ρ σ hne).mpr hσρ
  have hd : muTabElt ρ ≠ muTabElt σ := fun h => hne ((muTabElt_eq_iff hP hW ρ σ).mp h)
  have hall : ∀ d ∈ muDelta Ω W, d = muTabElt ρ ∨ d = muTabElt σ := by
    intro d hd'
    obtain ⟨τ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd'
    by_contra hcon
    push Not at hcon
    have hτρ : τ.K ≠ ρ.K := fun h => hcon.1 ((muTabElt_eq_iff hP hW τ ρ).mpr h)
    have hτσ : τ.K ≠ σ.K := fun h => hcon.2 ((muTabElt_eq_iff hP hW τ σ).mpr h)
    have h1 : τ.K ∈ omegaNbr Ω ρ.K := hs _ ρ.hK (muTab_omegaStar hP hW ρ τ (Ne.symm hτρ))
    have h2 : τ.K ∈ omegaNbr Ω σ.K := hs _ σ.hK (muTab_omegaStar hP hW σ τ (Ne.symm hτσ))
    exact htri ρ.K ρ.hK σ.K hσρ τ.K h1 h2
  have h1 : muTabElt ρ * muTabElt ρ = 1 := muDelta_mul_self hP.hyp hW (muTabElt_mem ρ)
  have h2 : muTabElt σ * muTabElt σ = 1 := muDelta_mul_self hP.hyp hW (muTabElt_mem σ)
  refine nonempty_mulEquiv_klein h1 h2 hcomm (muDelta_ne_one hW (muTabElt_mem ρ))
    (muDelta_ne_one hW (muTabElt_mem σ)) hd ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd' => ?_
  rcases hall d hd' with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem muIsoS4_of_cent (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W)
    (hk : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 2) : MuIsoS4 Ω W := by
  have hTT := isTT_muDelta hP hW
  have hS := isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  obtain ⟨a, ha, hconn⟩ := exists_not_conn_at hP hW hnc (muTabElt ρ)
  obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_four hTT hS (muTabElt_mem ρ) ha hconn hk
  exact ⟨e⟩

theorem muIsoS4_of_shape (hone : ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ L ∈ omegaNbr Ω K, J = L)
    (hedge : ∃ K ∈ Ω, (omegaNbr Ω K).Nonempty) (hcomp : ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K) :
    MuIsoS4 Ω W := by
  obtain ⟨K₁, hK₁, hne⟩ := hcomp
  have hnc := not_dbarConnected_of_shape hP hW hK₁ hne
  obtain ⟨K, hK, J, hJ⟩ := hedge
  obtain ⟨g, ρ, σ, hρ, hσ⟩ := exists_rep_pair_of_omegaNbr hP hW hK hJ
  have hσρ : σ.K ∈ omegaNbr Ω ρ.K := by
    rw [hρ, hσ]
    exact omegaNbr_conj hP.hyp.conjInvariant hJ g
  have hne' : ρ.K ≠ σ.K := fun h => hσρ.2.1 h.symm
  refine muIsoS4_of_cent hP hW hnc ρ ?_
  have hle : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard ≤ 2 := by
    refine ncard_cent_le hP hW ρ (n := 1) ?_
    rw [Set.ncard_le_one_iff]
    intro a b ha hb
    exact hone ρ.K ρ.hK a ha b hb
  have hge : 2 ≤ (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard := by
    have hd : muTabElt ρ ≠ muTabElt σ := fun h => hne' ((muTabElt_eq_iff hP hW ρ σ).mp h)
    have hsub : ({muTabElt ρ, muTabElt σ} : Set ↥(muGroup Ω W)) ⊆
        Star3T.cent (muDelta Ω W) (muTabElt ρ) := by
      rintro y (rfl | rfl)
      · exact Star3T.self_mem_cent (muTabElt_mem ρ)
      · exact ⟨muTabElt_mem σ, ((muTab_commute_iff hP hW ρ σ hne').mpr hσρ).symm⟩
    calc 2 = ({muTabElt ρ, muTabElt σ} : Set ↥(muGroup Ω W)).ncard := (Set.ncard_pair hd).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end Shapes

end CFSG.ClassicalInvolution.Q3.Q3MT
