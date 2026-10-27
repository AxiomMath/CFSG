module

import CFSG.ClassicalInvolution.Asc77.AscT8ZC6Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8YC4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY
open scoped commutatorElement

namespace T8ZZ

variable {p f : ℕ} [Fact p.Prime]


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_rep_le_cen_z (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    (i : Fin 4) : (F.ρ i).R ≤ T8.cenZ z := by
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact frame_rep_le_cen_zE (T8V.RepHooks.ofCtx c) F i

theorem frame_xMem_z (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    (i : Fin 4) : T8.XMem Ω z (F.ρ i).K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact frame_xMem_zE hΩ.conjInvariant hnt c.comm_W F (fun j => frame_rep_le_cen_z hs F j) i

theorem frame_layerImg_ne_z (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    T8.layerImg Ω z (F.ρ i).K ≠ T8.layerImg Ω z (F.ρ j).K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact T8.layerImg_ne_of_involutions hp hq hΩ hs.hz.sq (frame_xMem_z hs F i)
    (frame_xMem_z hs F j) (F.hz i) (F.hz j) (F.zz_comm c i j) (F.hinj i j hij)

theorem frame_layerImg_nbr_z (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    T8.layerImg Ω z (F.ρ j).K ∈
      omegaNbr (T8.layerFamQ Ω z) (T8.layerImg Ω z (F.ρ i).K) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hPN : (F.ρ j).R ≤ Subgroup.normalizer ((F.ρ i).K : Set G) := fun y hy =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (F.ρ i).hK (hnt _ (F.ρ i).hK)
      (F.hz i) (T8.rep_le_centralizer c (F.ρ j) (F.ρ i)
        (Or.inr (F.hadj j i (Ne.symm hij))) (F.hz i) hy)
  exact T8.layerImg_omegaNbr hp hq hΩ hs.hz.sq (frame_xMem_z hs F i) (frame_xMem_z hs F j)
    (F.ρ j).hRK (frame_rep_le_cen_z hs F j) hPN (frame_layerImg_ne_z hs F hij)

theorem oddCore_z_commutes_nbr [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s) {n : G}
    (hn : n ∈ oddCoreOf (T8.layerJoin Ω z)) : n * s = s * n := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  have hα' : alphaOf (Subgroup.closure ({s, z} : Set G)) = ⊥ := by
    rw [(T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM
      hs.hJ).symm]
    exact hα
  exact oddCore_z_commutes_nbrE hs.hz (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ z) hα' hn

theorem conjSub_eq_of_commute {Ω' : Set (Subgroup G)}
    (hnt : ∀ M ∈ Ω', ∀ M' ∈ twinSet Ω' M, M' = M) {M : Subgroup G} (hM : M ∈ Ω') {s : G}
    (hs : IsUniqueInvolution M s) {n : G} (hn : n * s = s * n) (hnΩ : conjSub n M ∈ Ω') :
    conjSub n M = M := by
  have h1 := hs.conj n
  have e : n * s * n⁻¹ = s := by
    rw [hn]
    group
  rw [e] at h1
  exact hnt M hM _ ⟨hnΩ, s, hs, h1⟩

theorem eq_of_layerImg_eq_z [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    {j : Fin 4} (hj : j ≠ 0) {L : Subgroup G} (hL : T8.XMem Ω z L)
    (h : T8.layerImg Ω z L = T8.layerImg Ω z (F.ρ j).K) : L = (F.ρ j).K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨n, hn, hnK⟩ :=
    T8.exists_oddCore_conj_of_layerImg_eq hp hq hΩ hs.hz.sq (frame_xMem_z hs F j) hL h.symm
  have hjK : (F.ρ j).K ∈ omegaNbr Ω K := by
    have := F.hadj 0 j (Ne.symm hj)
    rwa [F.h0] at this
  have hcomm := oddCore_z_commutes_nbr hs hμ hne hα hjK (F.hz j) hn
  have hΩn : conjSub n (F.ρ j).K ∈ Ω := hΩ.conjInvariant n _ (F.ρ j).hK
  have := conjSub_eq_of_commute hnt (F.ρ j).hK (F.hz j) hcomm hΩn
  rw [hnK] at this
  exact this

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
