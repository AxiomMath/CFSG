module

public import CFSG.ClassicalInvolution.Q3.TL4WylD4
public import CFSG.ClassicalInvolution.Q3.TL4OddBadW

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

theorem Wyl.frame_mem_omegaNbr {G : Type} [Group G] {Ω : Set (Subgroup G)} {W K J : Subgroup G}
    {z t : G} (F : FrameData Ω W K J z t) {i : Fin 4} (hi : i ≠ 0) : (F.ρ i).K ∈ omegaNbr Ω K := by
  have := F.hadj 0 i (Ne.symm hi)
  rwa [F.h0] at this

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.wyl_ncard_commonNbr_le (hS : TightSecFrameR r n) (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s)))
    (hαall : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s → alphaOf (Subgroup.closure ({s, z} : Set Y)) = ⊥)
    {M : Subgroup Y} (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    (omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∩
      omegaNbr (CoreAssembly.conjClass (tightCore Rd)) M).ncard ≤ 2 := by
  obtain ⟨s, hs'⟩ := Sec6Gen.exists_uniqueInvolution hs.hyp hM.1
  obtain ⟨g, S', R', T', hstd⟩ := TightLargeHypR.exists_std8_of_wset hs.large hM hs' hs.hW.1
  have hμ' := muIsoWylD4_conjSub hs.hyp hμ g
  obtain ⟨F'⟩ := Wyl.exists_frameData hstd.toStd8Core hμ'
    (Wyl.not_dbarConnected_of_ne hstd.toStd8Core hne)
  have hsub : omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∩
      omegaNbr (CoreAssembly.conjClass (tightCore Rd)) M ⊆ {(F'.ρ 2).K, (F'.ρ 3).K} := by
    rintro L ⟨hLK, hLM⟩
    obtain ⟨j, hj0, hjL⟩ := hstd.wyl_commonNbr_mem_frame hS hH (huni M hM s hs')
      (hαall M hM s hs') F' hLK hLM
    have hj1 : j ≠ 1 := by
      rintro rfl
      exact hLM.2.1 (hjL.trans F'.h1)
    fin_cases j
    · exact absurd rfl hj0
    · exact absurd rfl hj1
    · exact Or.inl hjL
    · exact Or.inr hjL
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  rw [Set.ncard_singleton]

theorem TightStd8R.wyl_commonNbr_frame_eq (hS : TightSecFrameR r n) (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s)))
    (hαall : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s → alphaOf (Subgroup.closure ({s, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t)
    {j : Fin 4} (hj : j ≠ 0) {L : Subgroup Y}
    (hLK : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hLj : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ j).K) :
    ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ L = (F.ρ i).K := by
  have hjK : (F.ρ j).K ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    have := F.hadj 0 j (Ne.symm hj)
    rwa [F.h0] at this
  have hcard := hs.wyl_ncard_commonNbr_le hS hH hμ hne huni hαall hjK
  let E : Set (Subgroup Y) := {L | ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ L = (F.ρ i).K}
  have hEsub : E ⊆ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∩
      omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ j).K := by
    rintro _ ⟨i, hi0, hij, rfl⟩
    refine ⟨?_, F.hadj j i (Ne.symm hij)⟩
    have := F.hadj 0 i (Ne.symm hi0)
    rwa [F.h0] at this
  have hinj : Function.Injective (fun i : Fin 4 => (F.ρ i).K) := by
    intro a b hab
    by_contra hne'
    exact F.hne a b hne' hab
  have hEcard : E.ncard = 2 := by
    have h1 : E = (fun i : Fin 4 => (F.ρ i).K) '' {i : Fin 4 | i ≠ 0 ∧ i ≠ j} := by
      ext L
      constructor
      · rintro ⟨i, hi0, hij, rfl⟩
        exact ⟨i, ⟨hi0, hij⟩, rfl⟩
      · rintro ⟨i, ⟨hi0, hij⟩, rfl⟩
        exact ⟨i, hi0, hij, rfl⟩
    have h2 : {i : Fin 4 | i ≠ 0 ∧ i ≠ j} =
        (((Finset.univ.erase 0).erase j : Finset (Fin 4)) : Set (Fin 4)) := by
      ext i
      simp [and_comm]
    rw [h1, Set.ncard_image_of_injective _ hinj, h2, Set.ncard_coe_finset,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp
  have heq : E = omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∩
      omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ j).K :=
    Set.eq_of_subset_of_ncard_le hEsub (by rw [hEcard]; exact hcard) (Set.toFinite _)
  have hL : L ∈ E := by
    rw [heq]
    exact ⟨hLK, hLj⟩
  exact hL

theorem TightStd8R.wyl_frame_xMem_z (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) (i : Fin 4) :
    T8.XMem (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K := by
  by_cases hi : i = 0
  · rw [hi, F.h0]
    exact xMem_core hs.large
  · exact xMem_of_mem_omegaNbr_core hs.large (Wyl.frame_mem_omegaNbr F hi)

theorem TightStd8R.wyl_frame_secImg_ne_z (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) {i j : Fin 4}
    (hij : i ≠ j) :
    secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K ≠
      secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ j).K :=
  secImg_ne (TightLargeHypR.typeRFam hs.large) (hs.wyl_frame_xMem_z F i) (hs.wyl_frame_xMem_z F j)
    (F.hz i) (F.hz j) (Wyl.zz_comm (Q3CL.T8.ctxOf (partIHyp_of_std8 hs.toStd8Core) hs.hW.1) F i j)
    (F.hinj i j hij)

theorem TightStd8R.wyl_frame_secImg_nbr_z (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) {i j : Fin 4}
    (hij : i ≠ j) :
    secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ j).K ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) z)
        (secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K) := by
  have hΩ := hs.hyp
  have h := TightLargeHypR.typeRFam hs.large
  have c0 := Q3CL.T8.ctxOf (partIHyp_of_std8 hs.toStd8Core) hs.hW.1
  have hz0 : IsUniqueInvolution (F.ρ 0).K z := by
    have := F.hz 0
    rwa [F.hz0] at this
  have hRz : (F.ρ j).R ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine rep_le_centralizer_gen c0 (F.ρ j) (F.ρ 0) ?_ hz0
    by_cases hj : j = 0
    · exact Or.inl (by rw [hj])
    · exact Or.inr (F.hadj j 0 hj)
  have hPN : (F.ρ j).R ≤ Subgroup.normalizer ((F.ρ i).K : Set Y) := fun y hy =>
    h.tight _ (F.ρ i).hK _ (F.hz i)
      (rep_le_centralizer_gen c0 (F.ρ j) (F.ρ i) (Or.inr (F.hadj j i (Ne.symm hij))) (F.hz i) hy)
  exact secImg_mem_omegaNbr (hs.wyl_frame_xMem_z F i) (hs.wyl_frame_xMem_z F j) (F.ρ j).hRK hRz
    hPN (hs.wyl_frame_secImg_ne_z F hij)

theorem TightStd8R.wyl_eq_of_secImg_eq_z (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hαall : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s → alphaOf (Subgroup.closure ({s, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) (i : Fin 4)
    {M : Subgroup Y} (hM : T8.XMem (CoreAssembly.conjClass (tightCore Rd)) z M)
    (heq : secImg (CoreAssembly.conjClass (tightCore Rd)) z M =
      secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K) : M = (F.ρ i).K := by
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨ν, hν, hMν⟩ := exists_conj_of_secImg_eq h (hs.wyl_frame_xMem_z F i) hM heq.symm
  have hνC : (ν : Y) ∈ oddCoreOf (Subgroup.centralizer ({z} : Set Y)) :=
    oddCoreOf_layerY_le hs.hyp.conjInvariant ⟨ν, hν, rfl⟩
  have hcomm : (ν : Y) * F.zz i = F.zz i * (ν : Y) := by
    by_cases hi : i = 0
    · rw [hi, F.hz0]
      exact Subgroup.mem_centralizer_singleton_iff.mp (layerY_le_centralizer ν.2)
    · have hα := hαall _ (Wyl.frame_mem_omegaNbr F hi) _ (F.hz i)
      have hzA : z ∈ Subgroup.closure ({F.zz i, z} : Set Y) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      have hiA : F.zz i ∈ Subgroup.closure ({F.zz i, z} : Set Y) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      exact T8.oddCoreOf_centralizer_commutes hα hzA hs.hz.ne_one hiA _ hνC
  have hz' : IsUniqueInvolution M (F.zz i) := by
    have h1 := (F.hz i).conj (ν : Y)
    rw [← hMν] at h1
    have e : (ν : Y) * F.zz i * (ν : Y)⁻¹ = F.zz i := by
      rw [hcomm]
      group
    rwa [e] at h1
  exact h.noTwins _ (F.ρ i).hK M ⟨hM.1, F.zz i, F.hz i, hz'⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
