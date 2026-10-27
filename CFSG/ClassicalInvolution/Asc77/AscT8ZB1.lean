module

import CFSG.ClassicalInvolution.Asc77.AscT8ZB1Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8YC4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY

namespace T8ZZ


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem zt_eq_frame (F : FrameData Ω W K J z t) : z * t = F.zz 0 * F.zz 1 := by
  rw [F.hz0, F.hz1]

theorem frame_rep_le_cenZ (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    (i : Fin 4) : (F.ρ i).R ≤ T8.cenZ (z * t) := by
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  intro r hr
  rw [T8.mem_cenZ_iff, zt_eq_frame F]
  exact commute_frame_prod_of_mem_DSet c F.ρ F.hadj F.hclos F.hz (F.ρ i).hR hr 0 1

theorem frame_xMem (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t) (i : Fin 4) :
    T8.XMem Ω (z * t) (F.ρ i).K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact frame_xMemE hΩ.conjInvariant hnt c.comm_W F (zt_eq_frame F)
    (fun j => frame_rep_le_cenZ hs F j) i

theorem frame_zz_mem_layerJoin (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    (i : Fin 4) : F.zz i ∈ T8.layerJoin Ω (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hK := frame_xMem hs F i
  have hL := hK.isSylow2In_layerRes_of_le hp hq hΩ hx (F.ρ i).hRK (frame_rep_le_cenZ hs F i)
  have h8 := hΩ.eight_le_of_mem_RSet hp (F.ρ i).hR.1
  have hzR : F.zz i ∈ (F.ρ i).R :=
    T3.mem_of_isPGroup (F.hz i) (F.ρ i).hRK.1 (F.ρ i).hRK.2.1 (by omega)
  exact T8.le_layerJoin ⟨(F.ρ i).K, hK, rfl⟩ (hL.1 hzR)

theorem frame_isUniqueInvolution_layerRes (hs : Std8 p f Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) (i : Fin 4) :
    IsUniqueInvolution (T8.layerRes (z * t) (F.ρ i).K) (F.zz i) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  exact (frame_xMem hs F i).isUniqueInvolution_layerRes hp hq hΩ hx (F.hz i)

theorem frame_isUniqueInvolution_layerImg (hs : Std8 p f Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) (i : Fin 4) :
    IsUniqueInvolution (T8.layerImg Ω (z * t) (F.ρ i).K)
      (T8V.layerMk (z * t) (F.zz i) (frame_zz_mem_layerJoin hs F i)) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(T8.layerJoin Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hLY : T8.layerRes (z * t) (F.ρ i).K ≤ T8.layerJoin Ω (z * t) :=
    T8.le_layerJoin ⟨(F.ρ i).K, frame_xMem hs F i, rfl⟩
  exact isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
    (isUniqueInvolution_subgroupOf (frame_isUniqueInvolution_layerRes hs F i) hLY)

theorem frame_layerImg_ne (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    T8.layerImg Ω (z * t) (F.ρ i).K ≠ T8.layerImg Ω (z * t) (F.ρ j).K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact T8.layerImg_ne_of_involutions hp hq hΩ hx (frame_xMem hs F i) (frame_xMem hs F j)
    (F.hz i) (F.hz j) (F.zz_comm c i j) (F.hinj i j hij)

theorem frame_layerImg_nbr (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    {i j : Fin 4} (hij : i ≠ j) :
    T8.layerImg Ω (z * t) (F.ρ j).K ∈
      omegaNbr (T8.layerFamQ Ω (z * t)) (T8.layerImg Ω (z * t) (F.ρ i).K) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hPN : (F.ρ j).R ≤ Subgroup.normalizer ((F.ρ i).K : Set G) := fun y hy =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (F.ρ i).hK (hnt _ (F.ρ i).hK)
      (F.hz i) (T8.rep_le_centralizer c (F.ρ j) (F.ρ i)
        (Or.inr (F.hadj j i (Ne.symm hij))) (F.hz i) hy)
  exact T8.layerImg_omegaNbr hp hq hΩ hx (frame_xMem hs F i) (frame_xMem hs F j)
    (F.ρ j).hRK (frame_rep_le_cenZ hs F j) hPN (frame_layerImg_ne hs F hij)

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
