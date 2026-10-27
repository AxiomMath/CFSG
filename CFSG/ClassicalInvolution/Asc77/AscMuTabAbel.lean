module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabBasic
public import CFSG.ClassicalInvolution.Asc77.AscMuTabGroup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace MuTab

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_sylow2In (J : Subgroup G) : ∃ R, IsSylow2In R J := by
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (P := J) (T := ⊥) IsPGroup.of_bot bot_le
  exact ⟨R, hR⟩

theorem exists_rep (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ g : G, ∃ ρ : Rep Ω W, ρ.K = conjSub g K := by
  obtain ⟨R, hR⟩ := exists_sylow2In K
  obtain ⟨g, hg⟩ := exists_rep_of_member_sylow (ι := Unit) hP hW (fun _ => K) (fun _ => R)
    (fun _ => hK) (fun _ => hR) R hR.2.1 (fun _ => le_rfl)
  obtain ⟨ρ, hρ⟩ := hg ()
  exact ⟨g, ρ, hρ⟩

theorem exists_rep_pair_of_omegaNbr (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    ∃ g : G, ∃ ρ σ : Rep Ω W, ρ.K = conjSub g K ∧ σ.K = conjSub g J := by
  obtain ⟨hJΩ, -, R', hR'Ω, hR'J, hR'N⟩ := hJ
  have hR'syl : IsSylow2In R' J := T3.isSylow2In_of_mem_RSet_of_le hP.1 hP.2.2.1 hJΩ hR'Ω hR'J
  obtain ⟨R, hRK, hRn⟩ := T3.exists_sylow_normalized hR'syl.2.1 hR'N
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

variable (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem muIsoZ2_of_shape (hne : Ω.Nonempty) (hsh : ∀ K ∈ Ω, omegaStarNbr Ω K = ∅) :
    MuIsoZ2 Ω W := by
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨g₀, ρ₀, hρ₀⟩ := exists_rep hP hW hK₀
  have hall : ∀ d ∈ muDelta Ω W, d = muTabElt ρ₀ := by
    intro d hd
    obtain ⟨ρ, rfl⟩ := exists_rep_of_mem_muDelta hd
    rw [muTabElt_eq_iff hP hW]
    by_contra hne
    have := muTab_omegaStar hP hW ρ₀ ρ (Ne.symm hne)
    rw [hsh _ ρ₀.hK] at this
    exact this
  have h2 : muTabElt ρ₀ * muTabElt ρ₀ = 1 :=
    muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (muTabElt_mem ρ₀)
  have h1 : muTabElt ρ₀ ≠ 1 := muDelta_ne_one hW (muTabElt_mem ρ₀)
  refine nonempty_mulEquiv_z2 h2 h1 ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd => ?_
  rw [hall d hd]
  exact Subgroup.subset_closure rfl

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
    obtain ⟨τ, rfl⟩ := exists_rep_of_mem_muDelta hd'
    by_contra hcon
    push Not at hcon
    have hτρ : τ.K ≠ ρ.K := fun h => hcon.1 ((muTabElt_eq_iff hP hW τ ρ).mpr h)
    have hτσ : τ.K ≠ σ.K := fun h => hcon.2 ((muTabElt_eq_iff hP hW τ σ).mpr h)
    have h1 : τ.K ∈ omegaNbr Ω ρ.K := hs _ ρ.hK (muTab_omegaStar hP hW ρ τ (Ne.symm hτρ))
    have h2 : τ.K ∈ omegaNbr Ω σ.K := hs _ σ.hK (muTab_omegaStar hP hW σ τ (Ne.symm hτσ))
    exact htri ρ.K ρ.hK σ.K hσρ τ.K h1 h2
  have h1 : muTabElt ρ * muTabElt ρ = 1 :=
    muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (muTabElt_mem ρ)
  have h2 : muTabElt σ * muTabElt σ = 1 :=
    muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (muTabElt_mem σ)
  refine nonempty_mulEquiv_klein h1 h2 hcomm (muDelta_ne_one hW (muTabElt_mem ρ))
    (muDelta_ne_one hW (muTabElt_mem σ)) hd ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd' => ?_
  rcases hall d hd' with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end Shapes

end MuTab

end CFSG.ClassicalInvolution.Asc77
