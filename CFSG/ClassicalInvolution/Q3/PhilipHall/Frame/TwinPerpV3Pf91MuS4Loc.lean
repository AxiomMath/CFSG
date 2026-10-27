module

public import CFSG.ClassicalInvolution.Q3.Q3MTAbel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.Loc

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6.Mu
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem muIsoS4_of_local (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaNbr Ω K) (hone : ∀ a ∈ omegaNbr Ω K, ∀ b ∈ omegaNbr Ω K, a = b)
    (hcomp : dComp Ω K ≠ dstarComp Ω K) : MuIsoS4 Ω W := by
  have hnc : ¬ DbarConnected Ω W := thompsonGraphAll hP hK hcomp hW
  obtain ⟨g, ρ, σ, hρ, hσ⟩ := Q3MT.exists_rep_pair_of_omegaNbr hP hW hK hJ
  have hσρ : σ.K ∈ omegaNbr Ω ρ.K := by
    rw [hρ, hσ]
    exact omegaNbr_conj hP.hyp.conjInvariant hJ g
  have hne' : ρ.K ≠ σ.K := fun h => hσρ.2.1 h.symm
  refine Q3MT.muIsoS4_of_cent hP hW hnc ρ ?_
  have hle : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard ≤ 2 := by
    refine ncard_cent_le hP hW ρ (n := 1) ?_
    rw [Set.ncard_le_one_iff]
    intro a b ha hb
    rw [hρ] at ha hb
    have ha' := omegaNbr_conj hP.hyp.conjInvariant ha g⁻¹
    have hb' := omegaNbr_conj hP.hyp.conjInvariant hb g⁻¹
    rw [conjSub_inv_conjSub] at ha' hb'
    exact (conjSub_inj g⁻¹).mp (hone _ ha' _ hb')
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

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.Loc
