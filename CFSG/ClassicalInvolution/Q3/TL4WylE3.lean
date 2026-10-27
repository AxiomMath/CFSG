module

public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Gen
public import CFSG.ClassicalInvolution.Q3.TL3T45
public import CFSG.ClassicalInvolution.Q3.Q3T8E4A
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2W

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Wyl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent AEIdentOn ThmDHyp)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem ncard_omegaNbr_of_wSet (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {W : Subgroup Y}
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W})
    (hnc : ¬ DConnected (CoreAssembly.conjClass (tightCore R))) {B₁ B₂ : Subgroup Y}
    (hB₁ : B₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hB₂ : B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) B₁)
    (hB₂K : B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    (omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3 := by
  classical
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  have hP := hd.partIHypG
  have hnc' := SecIdE2.not_dbarConnected_of_wSet hd hc hO2 hW1 hnc
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  obtain ⟨ρ0, h0⟩ := SecIdE2.exists_rep_of_wSet hd hc hO2 hW1 _ hK
  choose σ hσ using SecIdE2.exists_rep_of_wSet hd hc hO2 hW1
  set C := Star3T.cent (muDelta (CoreAssembly.conjClass (tightCore R)) W) (muTabElt ρ0) with hC
  have h0C : muTabElt ρ0 ∈ C := Star3T.self_mem_cent (muTabElt_mem ρ0)
  have hcard : (omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard =
      (C \ {muTabElt ρ0}).ncard := by
    refine Set.ncard_congr (fun J hJ => muTabElt (σ J hJ.1)) ?_ ?_ ?_
    · intro J hJ
      have hne : ρ0.K ≠ (σ J hJ.1).K := by rw [h0, hσ]; exact hJ.2.1.symm
      refine ⟨⟨muTabElt_mem _, ((Q3T8.Asc77.MuTab.muTab_commute_iff hP hW ρ0 _ hne).mpr
        (by rw [h0, hσ]; exact hJ)).symm⟩, fun e => hne ?_⟩
      exact ((Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW _ ρ0).mp e).symm
    · intro J J' hJ hJ' e
      have h1 := (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW _ _).mp e
      rwa [hσ, hσ] at h1
    · rintro d ⟨⟨hdD, hdc⟩, hd0⟩
      obtain ⟨τ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hdD
      have hne : ρ0.K ≠ τ.K := fun e =>
        hd0 ((Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW τ ρ0).mpr e.symm)
      have hτ : τ.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
        have h1 := (Q3T8.Asc77.MuTab.muTab_commute_iff hP hW ρ0 τ hne).mp hdc.symm
        rwa [h0] at h1
      exact ⟨τ.K, hτ, (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW _ τ).mpr (hσ _ _)⟩
  have hcard' : (C \ {muTabElt ρ0}).ncard = C.ncard - 1 := Set.ncard_sdiff_singleton_of_mem h0C
  have h2 : 2 ≤ (omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard := by
    have hsub : ({B₁, B₂} : Set (Subgroup Y)) ⊆
        omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
      rintro _ (rfl | rfl)
      · exact hB₁
      · exact hB₂K
    rw [← Set.ncard_pair hB₂.2.1.symm]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  rcases Q3T8.Asc77.thompsonClique Y _ hP W hW hnc' (muTabElt ρ0) (muTabElt_mem ρ0) with
    h | h | ⟨h, -⟩ <;> rw [← hC] at h <;> omega

theorem thmDHyp_of (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t) :
    ThmDHyp 3 (CoreAssembly.conjClass (tightCore R)) :=
  ⟨hd.hypOmegaGen, AlphaFr.E2D.isPGroup_mem hd hc hO2, AlphaFr.E2D.card_mem hd hc hO2, hd.aEmpty,
    AlphaFr.E2D.pSpan_eq_top hc, AlphaFr.E2D.transitive, hc.2.2, AlphaFr.E2D.exists_normal hd hO2⟩

theorem commutes_of_true_false_labels {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    {r : ℕ} (hD : ThmDHyp r Φ) {m : ℕ} (φ : ↥(pSpan Φ) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ)) {L M : Subgroup X} (hL : L ∈ Φ) (hM : M ∈ Φ)
    (hne : L ≠ M) {α : Finset (Fin m)} {h : α.card = 4}
    (hlab : (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h true)
    (hlab' : (M.subgroupOf (pSpan Φ)).map φ = AE.memBar α h false) : Commutes L M := by
  have hcomm := AE.comm_memBar_true_false (h := h)
  have hN : AE.memBar α h true ≤ Subgroup.normalizer (AE.memBar α h false : Set (AE.AEQ m)) :=
    fun x hx => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)
  have hsup := (LinkE2.isPGroup_memBar hD φ hL hlab).to_sup_of_normal_right'
    (LinkE2.isPGroup_memBar hD φ hM hlab') hN
  have hQ := (hsup.comap_of_ker_isPGroup φ (LinkE2.isPGroup_ker hD hker)).map (pSpan Φ).subtype
  refine LinkE2.commutes_of_le hD hL hM hne hQ ?_ ?_
  · intro x hx
    refine ⟨⟨x, le_pSpan hL hx⟩, ?_, rfl⟩
    have hm : φ ⟨x, le_pSpan hL hx⟩ ∈ AE.memBar α h true := by
      rw [← hlab]
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_sup_left hm
  · intro x hx
    refine ⟨⟨x, le_pSpan hM hx⟩, ?_, rfl⟩
    have hm : φ ⟨x, le_pSpan hM hx⟩ ∈ AE.memBar α h false := by
      rw [← hlab']
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_sup_right hm

end CFSG.ClassicalInvolution.Q3.TL4.Wyl
