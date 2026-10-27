module

import CFSG.ClassicalInvolution.Asc77.AscT8YC4Eng
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lift
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Tri
public import CFSG.ClassicalInvolution.Q3.TL4WylB2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

@[expose] def TightSecFrameR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ¬ DConnected Φ → ∀ B : Fin 3 → Subgroup X, (∀ i, B i ∈ Φ) → Function.Injective B →
        (∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) → ∀ u : Fin 3 → X,
          (∀ i, IsUniqueInvolution (B i) (u i)) →
            u 0 * u 1 ∈ Subgroup.center X ∧
              ∃ B₃ ∈ omegaNbr Φ (B 0), B₃ ≠ B 1 ∧ B₃ ≠ B 2 ∧
                ∀ M ∈ omegaNbr Φ (B 0), M = B 1 ∨ M = B 2 ∨ M = B₃

namespace Wyl

section Orbit

variable {X : Type} [Group X] [Finite X] {r : ℕ} {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem t4Hyp_of (h : TypeRFam r Φ) (hA : ∀ L ∈ Φ, AEmpty Φ L)
    (hO : classicalInvolutionOddCore X = ⊥) : T4Hyp r X Φ where
  hyp := h.hyp
  twoGroup := h.twoGroup
  quat := h.quat
  tight := h.tight
  noTwins := fun J hJ J' hJ' u hu hu' => (h.noTwins J hJ J' ⟨hJ', u, hu, hu'⟩).symm
  aEmpty := hA
  odd := hO

end Orbit

section Frame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G}
  {R T W : Subgroup G} {z t : G}

@[expose] def vGrp (F : FrameData Ω W K J z t) : Subgroup G :=
  Subgroup.closure {F.zz 0 * F.zz 1, F.zz 0 * F.zz 2}

theorem zt_eq (F : FrameData Ω W K J z t) : z * t = F.zz 0 * F.zz 1 := by
  rw [F.hz0, F.hz1]

theorem zt_mem_vGrp (F : FrameData Ω W K J z t) : z * t ∈ vGrp F := by
  rw [zt_eq F]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

variable [Finite G]

theorem zz_comm (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    F.zz i * F.zz j = F.zz j * F.zz i :=
  c.comm_W _ (F.hW i) _ (F.hW j)

theorem zz0_mul_mem_vGrp (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) (j : Fin 4) :
    F.zz 0 * F.zz j ∈ vGrp F := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.FrameData.zz0_mul_mem_vGroupE_of c.comm_W F j

theorem mul_mem_vGrp (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    F.zz i * F.zz j ∈ vGrp F := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.FrameData.mul_mem_vGroupE_of c.comm_W F i j

theorem vGrp_eq_of_members {W' K' J' : Subgroup G} {z' t' : G} (c : Q3CL.Thompson.Ctx Ω W)
    (c' : Q3CL.Thompson.Ctx Ω W') (F : FrameData Ω W K J z t) (F' : FrameData Ω W' K' J' z' t')
    (hmem : ∀ j, ∃ i, (F'.ρ j).K = (F.ρ i).K) : vGrp F' = vGrp F := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.FrameData.vGroupE_eq_of_members_of c.comm_W c'.comm_W F F'
    hmem

theorem isElemAbelian2_vGrp (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) :
    IsElemAbelian2 (vGrp F) 2 := by
  have hVa : (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 1) = 1 :=
    T8.mul_self_of_commute (F.hz 0).sq (F.hz 1).sq (zz_comm c F 0 1)
  have hVb : (F.zz 0 * F.zz 2) * (F.zz 0 * F.zz 2) = 1 :=
    T8.mul_self_of_commute (F.hz 0).sq (F.hz 2).sq (zz_comm c F 0 2)
  have hVcomm : (F.zz 0 * F.zz 1) * (F.zz 0 * F.zz 2) =
      (F.zz 0 * F.zz 2) * (F.zz 0 * F.zz 1) := by
    have h1 : Commute (F.zz 0 * F.zz 1) (F.zz 0) :=
      Commute.mul_left (Commute.refl _) (zz_comm c F 1 0)
    have h2 : Commute (F.zz 0 * F.zz 1) (F.zz 2) :=
      Commute.mul_left (zz_comm c F 0 2) (zz_comm c F 1 2)
    exact (Commute.mul_right h1 h2).eq
  unfold vGrp
  exact T7A.isElemAbelian2_closure_pair hVa hVb (frame_mul_ne_one F 0 1 (by decide))
    (frame_mul_ne_one F 0 2 (by decide)) (fun h => F.hinj 1 2 (by decide) (mul_left_cancel h))
    hVcomm

theorem frame_rep_le_centralizer (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t)
    (i : Fin 4) : (F.ρ i).R ≤ Subgroup.centralizer ({z * t} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff, zt_eq F]
  exact commute_frame_prod_of_mem_DSet c F.ρ F.hadj F.hclos F.hz (F.ρ i).hR hx 0 1

theorem frame_xMem (hs : Std8Core Ω K J S R T W z t) (F : FrameData Ω W K J z t) (i : Fin 4) :
    T8.XMem Ω (z * t) (F.ρ i).K := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  refine ⟨(F.ρ i).hK, ?_, (F.ρ i).R, (F.ρ i).hRK, fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (frame_rep_le_centralizer c F i hx)⟩
  refine T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (F.ρ i).hK
    (hnt _ (F.ρ i).hK) (F.hz i) ?_
  rw [Subgroup.mem_centralizer_singleton_iff, zt_eq F]
  calc F.zz 0 * F.zz 1 * F.zz i = F.zz 0 * (F.zz 1 * F.zz i) := by group
    _ = F.zz 0 * (F.zz i * F.zz 1) := by rw [zz_comm c F 1 i]
    _ = (F.zz 0 * F.zz i) * F.zz 1 := by group
    _ = (F.zz i * F.zz 0) * F.zz 1 := by rw [zz_comm c F 0 i]
    _ = F.zz i * (F.zz 0 * F.zz 1) := by group

variable {r : ℕ}

theorem frame_secImg_ne (h : TypeRFam r Ω) (hs : Std8Core Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) {i j : Fin 4} (hij : i ≠ j) :
    secImg Ω (z * t) (F.ρ i).K ≠ secImg Ω (z * t) (F.ρ j).K :=
  secImg_ne h (frame_xMem hs F i) (frame_xMem hs F j) (F.hz i) (F.hz j)
    (zz_comm (Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1) F i j) (F.hinj i j hij)

theorem frame_secImg_nbr (h : TypeRFam r Ω) (hs : Std8Core Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) {i j : Fin 4} (hij : i ≠ j) :
    secImg Ω (z * t) (F.ρ j).K ∈ omegaNbr (secFam Ω (z * t)) (secImg Ω (z * t) (F.ρ i).K) := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  have hPN : (F.ρ j).R ≤ Subgroup.normalizer ((F.ρ i).K : Set G) := fun y hy =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (F.ρ i).hK (hnt _ (F.ρ i).hK)
      (F.hz i) (rep_le_centralizer_gen c (F.ρ j) (F.ρ i) (Or.inr (F.hadj j i (Ne.symm hij)))
        (F.hz i) hy)
  exact secImg_mem_omegaNbr (frame_xMem hs F i) (frame_xMem hs F j) (F.ρ j).hRK
    (frame_rep_le_centralizer c F j) hPN (frame_secImg_ne h hs F hij)

end Frame

end Wyl

end CFSG.ClassicalInvolution.Q3.TL4
