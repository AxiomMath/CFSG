module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuStar
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuGraph

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.Mu

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem nonempty_mulEquiv_z2)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

noncomputable def memberOfMu (d : ↥(muGroup Ω W)) : Subgroup G :=
  open Classical in
  if h : d ∈ muDelta Ω W then (Classical.choose (MuTab.exists_rep_of_mem_muDelta h)).K else ⊥

section Shapes

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem memberOfMu_muTabElt (ρ : Rep Ω W) : memberOfMu (muTabElt ρ) = ρ.K := by
  classical
  have hm := muTabElt_mem ρ
  unfold memberOfMu
  simp only [hm, ↓reduceDIte]
  have := Classical.choose_spec (MuTab.exists_rep_of_mem_muDelta hm)
  exact ((muTabElt_eq_iff hP hW _ ρ).mp this.symm)

theorem ncard_cent_le (ρ : Rep Ω W) {n : ℕ} (hn : (omegaNbr Ω ρ.K).ncard ≤ n) :
    (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard ≤ n + 1 := by
  have hfin : (insert ρ.K (omegaNbr Ω ρ.K)).Finite := Set.toFinite _
  refine le_trans (Set.ncard_le_ncard_of_injOn memberOfMu (t := insert ρ.K (omegaNbr Ω ρ.K))
    ?_ ?_ hfin) ((Set.ncard_insert_le _ _).trans (by omega))
  · rintro y ⟨hy, hyc⟩
    obtain ⟨τ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hy
    rw [memberOfMu_muTabElt hP hW]
    by_cases hτ : τ.K = ρ.K
    · exact Or.inl hτ
    · exact Or.inr ((muTab_commute_iff hP hW ρ τ (Ne.symm hτ)).mp hyc.symm)
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ hyy'
    obtain ⟨τ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hy
    obtain ⟨τ', rfl⟩ := MuTab.exists_rep_of_mem_muDelta hy'
    rw [memberOfMu_muTabElt hP hW, memberOfMu_muTabElt hP hW] at hyy'
    exact (muTabElt_eq_iff hP hW τ τ').mpr hyy'

theorem exists_not_conn_at (hnc : ¬ DbarConnected Ω W) (d : ↥(muGroup Ω W)) :
    ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
  obtain ⟨d₁, hd₁, a₁, ha₁, hc⟩ := exists_not_conn_of_not_connected hP.hyp hW hnc
  by_cases h : Star3T.Conn (muDelta Ω W) d d₁
  · exact ⟨a₁, ha₁, fun h' => hc (h.symm.trans h')⟩
  · exact ⟨d₁, hd₁, h⟩

theorem muIsoS3_of_cent (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W)
    (hk : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 1) : MuIsoS3 Ω W := by
  have hTT := isTT_muDelta hP hW
  have hS := isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  obtain ⟨a, ha, hconn⟩ := exists_not_conn_at hP hW hnc (muTabElt ρ)
  obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_three hTT hS (muTabElt_mem ρ) ha hconn hk
  exact ⟨e⟩

theorem not_dbarConnected_of_shape {K : Subgroup G} (hK : K ∈ Ω)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  thompsonGraphAll hP hK hne hW

theorem muIsoS3_of_shape (hA : Disconnected.DEdgeless Ω)
    (hstar : ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty) : MuIsoS3 Ω W := by
  obtain ⟨K, hK, J, hJ⟩ := hstar
  have hnbr : ∀ M ∈ Ω, omegaNbr Ω M = ∅ := fun M hM => by
    ext N
    refine ⟨fun hN => ?_, fun hN => absurd hN (Set.notMem_empty N)⟩
    exact absurd (Or.inl hN) (hA M hM N hN.1)
  have hnc : ¬ DbarConnected Ω W := by
    refine not_dbarConnected_of_shape hP hW hK (fun h => ?_)
    have hJs : J ∈ dstarComp Ω K :=
      Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩
    rw [← h] at hJs
    have key : ∀ L, L ∈ dComp Ω K → L = K := by
      intro L hL
      have hL' : Relation.ReflTransGen
          (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K L := hL
      rcases hL'.cases_head with h' | ⟨c, ⟨hcΩ, hc⟩, -⟩
      · exact h'.symm
      · rcases hc with hc | hc
        · rw [hnbr K hK] at hc
          exact absurd hc (Set.notMem_empty c)
        · exact absurd (Or.inl hc) (hA c hcΩ K hK)
    exact hJ.2.1 (key J hJs)
  obtain ⟨g, ρ, hρ⟩ := exists_rep hP hW hK
  refine muIsoS3_of_cent hP hW hnc ρ ?_
  have h1 := ncard_cent_le hP hW ρ (n := 0) (by rw [hnbr _ ρ.hK]; simp)
  have h2 : 0 < (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨muTabElt ρ, Star3T.self_mem_cent (muTabElt_mem ρ)⟩
  omega

theorem muIsoZ2_of_shape (hne : Ω.Nonempty) (hsh : ∀ K ∈ Ω, omegaStarNbr Ω K = ∅) :
    MuIsoZ2 Ω W := by
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨g₀, ρ₀, hρ₀⟩ := exists_rep hP hW hK₀
  have hall : ∀ d ∈ muDelta Ω W, d = muTabElt ρ₀ := by
    intro d hd
    obtain ⟨ρ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
    rw [muTabElt_eq_iff hP hW]
    by_contra hne
    have := muTab_omegaStar hP hW ρ₀ ρ (Ne.symm hne)
    rw [hsh _ ρ₀.hK] at this
    exact this
  have h2 : muTabElt ρ₀ * muTabElt ρ₀ = 1 := muDelta_mul_self hP.hyp hW (muTabElt_mem ρ₀)
  have h1 : muTabElt ρ₀ ≠ 1 := muDelta_ne_one hW (muTabElt_mem ρ₀)
  refine nonempty_mulEquiv_z2 h2 h1 ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd => ?_
  rw [hall d hd]
  exact Subgroup.subset_closure rfl

end Shapes

end CFSG.ClassicalInvolution.Q3.Q3T6.Mu

namespace CFSG.ClassicalInvolution.Q3.Q3T6

theorem muS3OfShape3 : MuS3OfShape3 := by
  intro G _ _ Ω hP W hW hA hstar
  exact Mu.muIsoS3_of_shape hP hW hA hstar

theorem muZ2OfShape3 : MuZ2OfShape3 := by
  intro G _ _ Ω hP W hW hne hsh
  exact Mu.muIsoZ2_of_shape hP hW hne hsh

end CFSG.ClassicalInvolution.Q3.Q3T6
