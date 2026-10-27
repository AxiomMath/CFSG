module

public import CFSG.ClassicalInvolution.Q3.TL4WylD5
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLay
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.wyl_secImg_nbr_in_frame_z (hS : TightSecFrameR r n) (hH : TightHyp51TriR r n)
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
    (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hadj : secImg (CoreAssembly.conjClass (tightCore Rd)) z L ∈
        omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) z)
          (secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ j).K) ∨
      secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ j).K ∈
        omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) z)
          (secImg (CoreAssembly.conjClass (tightCore Rd)) z L)) :
    ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ secImg (CoreAssembly.conjClass (tightCore Rd)) z L =
      secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ := hs.hyp
  have hLx := xMem_of_mem_omegaNbr_core hs.large hL
  have hKj := hs.wyl_frame_xMem_z F j
  have key : ∃ ν : ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) z),
      ν ∈ classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) z) ∧
        conjSub (ν : Y) L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ j).K := by
    rcases hadj with h1 | h1
    · obtain ⟨ν, hν, hLν⟩ := exists_conj_omegaNbr_of_secImg h hKj hLx h1
      refine ⟨ν⁻¹, (classicalInvolutionOddCore _).inv_mem hν, ?_⟩
      have h2 := omegaNbr_conj hΩ.conjInvariant hLν (ν : Y)⁻¹
      rw [conjSub_inv_conjSub] at h2
      rw [Subgroup.coe_inv]
      exact h2
    · obtain ⟨ν, hν, hjν⟩ := exists_conj_omegaNbr_of_secImg h hLx hKj h1
      exact ⟨ν, hν, Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (hΩ.conjInvariant _ L hL.1)
        (F.ρ j).hK hjν⟩
  obtain ⟨ν, hν, hνL⟩ := key
  have hνK := conjSub_mem_omegaNbr_core hs.large hL (layerY_le_centralizer ν.2)
  obtain ⟨i, hi0, hij, hi⟩ := hs.wyl_commonNbr_frame_eq hS hH hμ hne huni hαall F hj hνK hνL
  exact ⟨i, hi0, hij, by rw [← secImg_conj_of_mem hν L, hi]⟩

theorem TightStd8R.wyl_link_dConnected (hS : TightSecFrameR r n) (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s)))
    (hαall : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s → alphaOf (Subgroup.closure ({s, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) :
    DConnected (restrictFamily (coreLinkFam Rd z) (linkGrp Rd z)) := by
  by_contra hc
  have hT : TypeRFam r (restrictFamily (coreLinkFam Rd z) (linkGrp Rd z)) :=
    (typeRFam_coreLinkFam hs.large).restrict _
  have hA : ∀ L ∈ restrictFamily (coreLinkFam Rd z) (linkGrp Rd z),
      AEmpty (restrictFamily (coreLinkFam Rd z) (linkGrp Rd z)) L := fun L hL =>
    aEmpty_of_noTwins hT.hyp hL (hT.noTwins _ hL)
  have hn : Nat.card ↥(linkGrp Rd z) < n :=
    (Subgroup.card_le_card_group _).trans_lt (AlphaFr.natCard_secQuot_lt_of_large hs.large)
  have hKi : ∀ a : Fin 3, (F.ρ a.succ).K ∈
      omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := fun a =>
    Wyl.frame_mem_omegaNbr F (Fin.succ_ne_zero a)
  let B' : Fin 3 → Subgroup ↥(linkGrp Rd z) := fun a =>
    (secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ a.succ).K).subgroupOf (linkGrp Rd z)
  have hB' : ∀ a, B' a ∈ restrictFamily (coreLinkFam Rd z) (linkGrp Rd z) := fun a =>
    subgroupOf_mem_linkRestrict (hKi a)
  have hinj : Function.Injective B' := by
    intro a b hab
    by_contra hne'
    exact subgroupOf_linkGrp_ne (hKi b) (hKi a)
      (hs.wyl_frame_secImg_ne_z F (fun h => hne' (Fin.succ_injective _ h))) hab
  have hadj : ∀ a b, a ≠ b →
      B' b ∈ omegaNbr (restrictFamily (coreLinkFam Rd z) (linkGrp Rd z)) (B' a) :=
    fun a b hab => omegaNbr_link_of_secFam hs.large (hKi a) (hKi b)
      (hs.wyl_frame_secImg_nbr_z F (fun h => hab (Fin.succ_injective _ h)))
  choose u hu using fun a => Sec6Gen.exists_uniqueInvolution hT.hyp (hB' a)
  obtain ⟨-, B₃, hB₃, hB₃1, hB₃2, -⟩ := hS _ hn _ hT (oddCore_linkGrp_eq_bot hs.large)
    omegaGen_linkRestrict hA hc B' hB' hinj hadj u hu
  obtain ⟨C, hC, -, rfl⟩ := hB₃.1
  obtain ⟨L, hL, rfl⟩ := hC
  have h1 := omegaNbr_secFam_of_link hs.large (hKi 0) hL hB₃
  obtain ⟨i, hi0, hi1, hiL⟩ := hs.wyl_secImg_nbr_in_frame_z hS hH hμ hne huni hαall F
    (j := 1) (by decide) hL (Or.inl h1)
  simp only [B'] at hB₃1 hB₃2
  fin_cases i
  · exact hi0 rfl
  · exact hi1 rfl
  · exact hB₃1 (by rw [hiL]; rfl)
  · exact hB₃2 (by rw [hiL]; rfl)

theorem TightStd8R.wyl_secImg_mem_frame_z (hS : TightSecFrameR r n) (hH : TightHyp51TriR r n)
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
    {M : Subgroup Y} (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    ∃ i : Fin 4, i ≠ 0 ∧ secImg (CoreAssembly.conjClass (tightCore Rd)) z M =
      secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K := by
  have hconn := hs.wyl_link_dConnected hS hH hμ hne huni hαall F
  have hK1 : (F.ρ 1).K ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
    Wyl.frame_mem_omegaNbr F (by decide)
  have key : ∀ A, Relation.ReflTransGen
      (fun A B => B ∈ restrictFamily (coreLinkFam Rd z) (linkGrp Rd z) ∧
        dAdj (restrictFamily (coreLinkFam Rd z) (linkGrp Rd z)) A B)
      ((secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ 1).K).subgroupOf (linkGrp Rd z)) A →
      ∃ i : Fin 4, i ≠ 0 ∧
        A = (secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K).subgroupOf
          (linkGrp Rd z) := by
    intro A hA
    induction hA with
    | refl => exact ⟨1, by decide, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨i, hi0, rfl⟩ := ih
      obtain ⟨⟨C, hC, -, rfl⟩, hadj⟩ := hbc
      obtain ⟨L, hL, rfl⟩ := hC
      have hKi := Wyl.frame_mem_omegaNbr F hi0
      have hadj' : secImg (CoreAssembly.conjClass (tightCore Rd)) z L ∈
          omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) z)
            (secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K) ∨
          secImg (CoreAssembly.conjClass (tightCore Rd)) z (F.ρ i).K ∈
            omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) z)
              (secImg (CoreAssembly.conjClass (tightCore Rd)) z L) := by
        rcases hadj with h1 | h1
        · exact Or.inl (omegaNbr_secFam_of_link hs.large hKi hL h1)
        · exact Or.inr (omegaNbr_secFam_of_link hs.large hL hKi h1)
      obtain ⟨i', hi'0, -, hi'⟩ :=
        hs.wyl_secImg_nbr_in_frame_z hS hH hμ hne huni hαall F hi0 hL hadj'
      exact ⟨i', hi'0, by rw [hi']⟩
  obtain ⟨i, hi0, hi⟩ := key _ (hconn _ (subgroupOf_mem_linkRestrict hK1) _
    (subgroupOf_mem_linkRestrict hM))
  refine ⟨i, hi0, ?_⟩
  have h1 := Subgroup.subgroupOf_inj.mp hi
  rwa [inf_of_le_left (le_linkGrp hM),
    inf_of_le_left (le_linkGrp (Wyl.frame_mem_omegaNbr F hi0))] at h1

theorem TightStd8R.wyl_singleFrame0 (hS : TightSecFrameR r n) (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s)))
    (hαall : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s → alphaOf (Subgroup.closure ({s, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) :
    ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∃ j, M = (F.ρ j).K := by
  intro M hM
  obtain ⟨i, -, hi⟩ := hs.wyl_secImg_mem_frame_z hS hH hμ hne huni hαall F hM
  exact ⟨i, hs.wyl_eq_of_secImg_eq_z hαall F i (xMem_of_mem_omegaNbr_core hs.large hM) hi⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
