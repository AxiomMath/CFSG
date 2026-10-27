module

public import CFSG.ClassicalInvolution.Q3.TL4WylD3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.wyl_frame_facts (hS : TightSecFrameR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hnc : ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t)
    (M : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    (hM : M ∈ omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd))) :
    ∃ j, M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (F.ρ j).K := by
  have h := TightLargeHypR.typeRFam hs.large
  have hfacts := Wyl.frame_facts hS hs.natCard_secQuot_lt h.secFam secQuot_oddCore_eq_bot
    omegaGen_secFam (aEmpty_secFam h) hnc (fun i => secImg_mem (Wyl.frame_xMem hs.toStd8Core F i))
    (fun i j hij => Wyl.frame_secImg_ne h hs.toStd8Core F hij)
    (fun i j hij => Wyl.frame_secImg_nbr h hs.toStd8Core F hij)
    (fun i => isUniqueInvolution_secImg h (Wyl.frame_xMem hs.toStd8Core F i) (F.hz i))
  refine hfacts.2 M ?_
  show M ∈ omegaNbr _ (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (F.ρ 0).K)
  rw [F.h0]
  exact hM

theorem TightStd8R.wyl_oddCore_commutes_zz (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) (j : Fin 4)
    {g : Y} (hg : g ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) :
    g * F.zz j = F.zz j * g := by
  have c0 := Q3CL.T8.ctxOf (partIHyp_of_std8 hs.toStd8Core) hs.hW.1
  have hαV : alphaOf (Wyl.vGrp F) = ⊥ := (hs.alphaOf_vGrp_eq hH F).trans hα
  have hgC := oddCoreOf_layerY_le hs.hyp.conjInvariant hg
  have hzt1 : z * t ≠ 1 := T8.zt_ne_one hs.noTwins hs.hJ hs.hz hs.ht
  have hzA : z ∈ Subgroup.closure ({t, z} : Set Y) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have htA : t ∈ Subgroup.closure ({t, z} : Set Y) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgz : g * z = z * g :=
    T8.oddCoreOf_centralizer_commutes hα (Subgroup.mul_mem _ hzA htA) hzt1 hzA g hgC
  have h1 : Commute g (F.zz 0) := by
    show g * F.zz 0 = F.zz 0 * g
    rw [F.hz0]
    exact hgz
  have h2 : Commute g (F.zz 0 * F.zz j) :=
    T8.oddCoreOf_centralizer_commutes hαV (Wyl.zt_mem_vGrp F) hzt1
      (Wyl.zz0_mul_mem_vGrp c0 F j) g hgC
  have h3 := h1.mul_right h2
  rw [← mul_assoc, (F.hz 0).sq, one_mul] at h3
  exact h3.eq

theorem TightStd8R.wyl_eq_frame_of_secImg_eq (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) (j : Fin 4)
    {L : Subgroup Y} (hL : T8.XMem (CoreAssembly.conjClass (tightCore Rd)) (z * t) L)
    (heq : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) L =
      secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (F.ρ j).K) :
    L = (F.ρ j).K := by
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨ν, hν, hLν⟩ :=
    exists_conj_of_secImg_eq h (Wyl.frame_xMem hs.toStd8Core F j) hL heq.symm
  have hcomm := hs.wyl_oddCore_commutes_zz hH hα F j (g := (ν : Y)) ⟨ν, hν, rfl⟩
  have hz' : IsUniqueInvolution L (F.zz j) := by
    have h1 := (F.hz j).conj (ν : Y)
    rw [← hLν] at h1
    have e : (ν : Y) * F.zz j * (ν : Y)⁻¹ = F.zz j := by
      rw [hcomm]
      group
    rwa [e] at h1
  exact h.noTwins _ (F.ρ j).hK L ⟨hL.1, F.zz j, F.hz j, hz'⟩

theorem TightStd8R.wyl_commonNbr_mem_frame (hS : TightSecFrameR r n) (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hnc : ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t)
    {L : Subgroup Y} (hLK : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hLJ : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J) :
    ∃ j : Fin 4, j ≠ 0 ∧ L = (F.ρ j).K := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ := hs.hyp
  have hnt : ∀ M ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ M' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.trans hs.noTwins hM
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hLK.1
  have hKL := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.mem hLK.1 hLK
  have hJL := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.hJ.1 hLJ.1 hLJ
  have hzt : z ≠ t := T8.ne_of_mem_omegaNbr (hnt _ hs.mem) hs.hJ hs.hz hs.ht
  have hczt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  obtain ⟨P, hP, -, hPz, hPt⟩ :=
    exists_isSylow2In_member_le_centralizer hs.large hLK.1 hu hKL hJL hs.hz hs.ht hzt hczt
  have hzu : z * u = u * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hLK hu
  have htu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.ht hLJ hu
  have hzN := h.tight L hLK.1 u hu (Subgroup.mem_centralizer_singleton_iff.mpr hzu)
  have htN := h.tight L hLK.1 u hu (Subgroup.mem_centralizer_singleton_iff.mpr htu)
  have hPx : P ≤ Subgroup.centralizer ({z * t} : Set Y) := by
    intro p hp
    have e1 := Subgroup.mem_centralizer_singleton_iff.mp (hPz hp)
    have e2 := Subgroup.mem_centralizer_singleton_iff.mp (hPt hp)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc p * (z * t) = (p * z) * t := by group
      _ = (z * p) * t := by rw [e1]
      _ = z * (p * t) := by group
      _ = z * (t * p) := by rw [e2]
      _ = z * t * p := by group
  have hXL : T8.XMem (CoreAssembly.conjClass (tightCore Rd)) (z * t) L :=
    ⟨hLK.1, Subgroup.mul_mem _ hzN htN, P, hP, fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.mp (hPx hp)⟩
  have hne := secImg_ne h hs.xMem_K hXL hs.hz hu hzu
    (T8.ne_of_mem_omegaNbr (hnt _ hs.mem) hLK hs.hz hu)
  have hPN : P ≤ Subgroup.normalizer (tightCore Rd : Set Y) := fun p hp =>
    h.tight _ hs.mem z hs.hz (hPz hp)
  obtain ⟨j, hj⟩ := hs.wyl_frame_facts hS hnc F _
    (secImg_mem_omegaNbr hs.xMem_K hXL hP hPx hPN hne)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (by rw [hj, F.h0])
  exact ⟨j, hj0, hs.wyl_eq_frame_of_secImg_eq hH hα F j hXL hj⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
