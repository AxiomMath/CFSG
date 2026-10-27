module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuLayer
import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8
import CFSG.ClassicalInvolution.Q3.Sec13PerpA3
import CFSG.ClassicalInvolution.Q3.Sec13EndDict
public import CFSG.ClassicalInvolution.Q3.Sec13End18A
import CFSG.ClassicalInvolution.Q3.Sec13PerpD

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

section FrameCert


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace End18

namespace Hyp

private theorem e18c_exists_rep (h : EndHyp Ω) {W R : Subgroup G} (hW : W ∈ WSet Ω)
    (hR : R ∈ DSet Ω W) : ∃ ρ : Asc77.Thompson.Rep Ω W, ρ.K = R := by
  obtain ⟨hRΩ, -⟩ := h.mem_dSet_iff.mp hR
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D h.thmD.hyp hW hR
  have hRR : IsSylow2In R R :=
    ⟨le_rfl, h.thmD.two R hRΩ, fun _ hVR _ hRV => le_antisymm hVR hRV⟩
  exact ⟨⟨R, R, r, hRΩ, hR, hRR, hr, hrW⟩, rfl⟩

private theorem e18c_rep_mem (h : EndHyp Ω) {W : Subgroup G} (ρ : Asc77.Thompson.Rep Ω W) :
    ρ.K ∈ DSet Ω W := by
  have hKR : ρ.K = ρ.R := ρ.hRK.2.2 ρ.K le_rfl (h.thmD.two ρ.K ρ.hK) ρ.hRK.1
  rw [hKR]
  exact ρ.hR

private theorem e18c_kPerp_of_twin (H : Hyp Ω) {K A B : Subgroup G} (hA : A ∈ twinSet Ω K)
    (hB : B ∈ twinSet Ω K) : B ∈ KPerp Ω A := by
  rw [H.kPerp_eq_twinSet hA.1]
  obtain ⟨hBΩ, z₀, hz₀K, hz₀B⟩ := hB
  obtain ⟨-, z₁, hz₁K, hz₁A⟩ := hA
  have hz : z₁ = z₀ := hz₁K.eq hz₀K
  exact ⟨hBΩ, z₁, hz₁A, by rw [hz]; exact hz₀B⟩

private theorem e18c_twin_of_kPerp (H : Hyp Ω) {K A B : Subgroup G} (hA : A ∈ twinSet Ω K)
    (hB : B ∈ KPerp Ω A) : B ∈ twinSet Ω K := by
  rw [H.kPerp_eq_twinSet hA.1] at hB
  obtain ⟨hBΩ, z₁, hz₁A, hz₁B⟩ := hB
  obtain ⟨-, z₀, hz₀K, hz₀A⟩ := hA
  have hz : z₀ = z₁ := hz₀A.eq hz₁A
  exact ⟨hBΩ, z₀, hz₀K, by rw [hz]; exact hz₁B⟩

private theorem e18c_omegaNbr_of_twin (H : Hyp Ω) {K A B : Subgroup G} (hA : A ∈ twinSet Ω K)
    (hB : B ∈ twinSet Ω K) (hne : A ≠ B) : B ∈ omegaNbr Ω A :=
  (Set.mem_insert_iff.mp (e18c_kPerp_of_twin H hA hB)).resolve_left (Ne.symm hne)

private theorem e18c_not_conn (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hKD : K ∈ DSet Ω W) (hP : Q3CL.PartIHypG Ω)
    {ρa ρS : Asc77.Thompson.Rep Ω W} (haK : ρa.K ∈ twinSet Ω K) (hSK : ρS.K ∉ KPerp Ω K) :
    ¬ Star3T.Conn (Thompson.muDelta Ω W) (MuTab.muTabElt ρa) (MuTab.muTabElt ρS) := by
  intro hconn
  have key : ∀ x : ↥(muGroup Ω W),
      Relation.ReflTransGen (Star3T.Adj (Thompson.muDelta Ω W)) (MuTab.muTabElt ρa) x →
        ∀ σ : Asc77.Thompson.Rep Ω W, MuTab.muTabElt σ = x → σ.K ∈ KPerp Ω K := by
    intro x hx
    induction hx with
    | refl =>
      intro σ hσ
      rw [(Q3T6.Mu.muTabElt_eq_iff hP hW σ ρa).mp hσ, H.kPerp_eq_twinSet hK]
      exact haK
    | @tail b c hab hbc ih =>
      intro τ hτ
      obtain ⟨hbΔ, -, hbc_comm⟩ := hbc
      obtain ⟨σ₀, hσ₀⟩ := MuTab.exists_rep_of_mem_muDelta hbΔ
      have hK₀ : σ₀.K ∈ KPerp Ω K := ih σ₀ hσ₀.symm
      have hτD := e18c_rep_mem H.endHyp τ
      have hσD := e18c_rep_mem H.endHyp σ₀
      have hTU : τ.K ∈ KPerp Ω σ₀.K := by
        by_cases hne : σ₀.K = τ.K
        · rw [hne]
          exact Set.mem_insert _ _
        · have hc : MuTab.muTabElt σ₀ * MuTab.muTabElt τ =
              MuTab.muTabElt τ * MuTab.muTabElt σ₀ := by
            rw [← hσ₀, hτ]
            exact hbc_comm
          exact Set.mem_insert_of_mem _ ((Q3T6.Mu.muTab_commute_iff hP hW σ₀ τ hne).mp hc)
      exact dSet_comm_trans H.endHyp hW hKD hσD hτD hK₀ hTU
  exact hSK (key _ hconn ρS rfl)

theorem mem_pSpan_twinSet_of_omegaStar (H : Hyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    j ∈ pSpan (twinSet Ω K) := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  by_cases hJT : J ∈ twinSet Ω K
  ·
    obtain ⟨-, z', hz'K, hz'J⟩ := hJT
    rw [hj.eq hz'J]
    exact le_pSpan hKT hz'K.mem
  have hJK : J ∉ KPerp Ω K := by
    rw [H.kPerp_eq_twinSet hK]
    exact hJT
  have hJn : J ∉ omegaNbr Ω K := fun h => hJK (Set.mem_insert_of_mem _ h)
  obtain ⟨W, hW, hKD, hJD, -⟩ := exists_wSet_of_omegaStar H.endHyp hK hJ hJn
  have hVD : twinSet Ω K ⊆ DSet Ω W := H.endHyp.twinSet_subset_dSet hW hKD
  have hcard : (twinSet Ω K).ncard = 4 := H.ncard_twinSet hK
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ :=
    (Set.two_lt_ncard_iff (Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num))).mp
      (by rw [hcard]; norm_num)
  have hP : Q3CL.PartIHypG Ω := ⟨H.endHyp.thmD.hyp, H.endHyp.cls, H.endHyp.thmD.aEmpty⟩
  obtain ⟨ρa, hρa⟩ := e18c_exists_rep H.endHyp hW (hVD hA)
  obtain ⟨ρb, hρb⟩ := e18c_exists_rep H.endHyp hW (hVD hB)
  obtain ⟨ρc, hρc⟩ := e18c_exists_rep H.endHyp hW (hVD hC)
  obtain ⟨ρS, hρS⟩ := e18c_exists_rep H.endHyp hW hJD
  have haK : ρa.K ∈ twinSet Ω K := by
    rw [hρa]
    exact hA
  have hbK : ρb.K ∈ twinSet Ω K := by
    rw [hρb]
    exact hB
  have hcK : ρc.K ∈ twinSet Ω K := by
    rw [hρc]
    exact hC
  have hne_ab : ρa.K ≠ ρb.K := by
    rw [hρa, hρb]
    exact hAB
  have hne_ac : ρa.K ≠ ρc.K := by
    rw [hρa, hρc]
    exact hAC
  have hne_bc : ρb.K ≠ ρc.K := by
    rw [hρb, hρc]
    exact hBC
  have hab : MuTab.muTabElt ρa ≠ MuTab.muTabElt ρb :=
    fun h => hne_ab ((Q3T6.Mu.muTabElt_eq_iff hP hW ρa ρb).mp h)
  have hac : MuTab.muTabElt ρa ≠ MuTab.muTabElt ρc :=
    fun h => hne_ac ((Q3T6.Mu.muTabElt_eq_iff hP hW ρa ρc).mp h)
  have hbc : MuTab.muTabElt ρb ≠ MuTab.muTabElt ρc :=
    fun h => hne_bc ((Q3T6.Mu.muTabElt_eq_iff hP hW ρb ρc).mp h)
  have cab := (Q3T6.Mu.muTab_commute_iff hP hW ρa ρb hne_ab).mpr
    (e18c_omegaNbr_of_twin H haK hbK hne_ab)
  have cac := (Q3T6.Mu.muTab_commute_iff hP hW ρa ρc hne_ac).mpr
    (e18c_omegaNbr_of_twin H haK hcK hne_ac)
  have cbc := (Q3T6.Mu.muTab_commute_iff hP hW ρb ρc hne_bc).mpr
    (e18c_omegaNbr_of_twin H hbK hcK hne_bc)
  have hSK : ρS.K ∉ KPerp Ω K := by
    rw [hρS]
    exact hJK
  have hconn := e18c_not_conn H hK hW hKD hP haK hSK
  obtain ⟨w, hwJ, hw4⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Thompson.exists_orderOf_four H.endHyp.thmD.hyp hW hJD
  have hw2 : w * w = j :=
    Asc77.Thompson.sq_eq_involution_of_orderOf_four hj (Subgroup.mem_inf.mp hwJ).1 hw4
  have hwS : w ∈ ρS.K ⊓ W := by
    rw [hρS]
    exact hwJ
  have hzS : IsUniqueInvolution ρS.K j := by
    rw [hρS]
    exact hj
  obtain ⟨za, hza⟩ : ∃ za, IsUniqueInvolution ρa.K za := by
    obtain ⟨-, za, -, h⟩ := haK
    exact ⟨za, h⟩
  obtain ⟨zb, hzb⟩ : ∃ zb, IsUniqueInvolution ρb.K zb := by
    obtain ⟨-, zb, -, h⟩ := hbK
    exact ⟨zb, h⟩
  obtain ⟨zc, hzc⟩ : ∃ zc, IsUniqueInvolution ρc.K zc := by
    obtain ⟨-, zc, -, h⟩ := hcK
    exact ⟨zc, h⟩
  obtain ⟨ρd, -, hF, -, -, -, ka, kb, kc, kd, hka, hkb, hkc, hkd, -, -, -, -, -, -, -, -, hprod⟩ :=
    PhilipHall.Frame.TwinMu.frame_prod hP hW hab hac hbc cab cac cbc hconn hwS hzS hw2 hza hzb hzc
  have hTd : ρd.K ∈ twinSet Ω K :=
    e18c_twin_of_kPerp H haK (show ρd.K ∈ KPerp Ω ρa.K from Set.mem_insert_of_mem _ hF.ad)
  rw [← hprod]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (le_pSpan haK (Subgroup.mem_inf.mp hka).1) (le_pSpan hbK (Subgroup.mem_inf.mp hkb).1))
    (le_pSpan hcK (Subgroup.mem_inf.mp hkc).1)) (le_pSpan hTd (Subgroup.mem_inf.mp hkd).1)

theorem eGroup_le_span (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    eGroup Ω K ≤ pSpan (twinSet Ω K) := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨J, hJ, hu⟩
  rcases hJ with h | hJ
  · rw [h] at hu
    exact le_pSpan hKT hu.mem
  · exact H.mem_pSpan_twinSet_of_omegaStar hK hJ hu

end Hyp

end End18

end FrameCert

end CFSG.ClassicalInvolution.Q3.Sec13
