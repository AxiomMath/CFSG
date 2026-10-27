module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrLink
public import CFSG.ClassicalInvolution.Q3.TL4Conn274MLift
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Balance.Bootstrap (rankTwoSpan le_rankTwoSpan_of_le_centralizer)

section Link

variable {Y : Type} [Group Y]

@[expose] def coreLinkFam (R : Subgroup Y) (t : Y) :
    Set (Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t)) :=
  {Lb | ∃ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
    secImg (CoreAssembly.conjClass (tightCore R)) t J = Lb}

end Link

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem xMem_of_mem_omegaNbr_core (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    XMem (CoreAssembly.conjClass (tightCore R)) t J := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  have h := TightLargeHypR.typeRFam hL
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  have htu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := hJ
  refine ⟨hJΩ, h.tight J hJΩ u hu (Subgroup.mem_centralizer_singleton_iff.mpr htu), T,
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ, fun p hp => ?_⟩
  have hpt : p * t * p⁻¹ = t := ht.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hp))
  calc p * t = (p * t * p⁻¹) * p := by group
    _ = t * p := by rw [hpt]

theorem coreLinkFam_subset (hL : TightLargeHypR r n Y R S t) :
    coreLinkFam R t ⊆ secFam (CoreAssembly.conjClass (tightCore R)) t := by
  rintro _ ⟨J, hJ, rfl⟩
  exact secImg_mem (xMem_of_mem_omegaNbr_core hL hJ)

theorem omegaNbr_secFam_of_coreLinkFam (hL : TightLargeHypR r n Y R S t)
    {Mb Nb : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t)}
    (h : Nb ∈ omegaNbr (coreLinkFam R t) Mb) :
    Nb ∈ omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t) Mb := by
  obtain ⟨hN, hne, T, ⟨L, hL', P, rfl⟩, hTN, hTM⟩ := h
  exact ⟨coreLinkFam_subset hL hN, hne, _, ⟨L, coreLinkFam_subset hL hL', P, rfl⟩, hTN, hTM⟩

theorem conjSub_core_of_mem_centralizer (hL : TightLargeHypR r n Y R S t) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) : conjSub c (tightCore R) = tightCore R := by
  have hd := hL.datum
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  refine eq_core_of_isUniqueInvolution hL (hd.hypOmegaGen.conjInvariant c _
    (CoreAssembly.mem_conjClass_self _)) ?_
  have h1 := hd.isUniqueInvolution_core.conj c
  rwa [hct] at h1

theorem conjSub_mem_omegaNbr_core (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  have h1 := omegaNbr_conj hL.datum.hypOmegaGen.conjInvariant hJ c
  rwa [conjSub_core_of_mem_centralizer hL hc] at h1

theorem oddCoreOf_layerY_le_rankTwoSpan (hL : TightLargeHypR r n Y R S t) {J L : Subgroup Y}
    (hG : GAdj R t J L) {u z' : Y} (hu : IsUniqueInvolution J u)
    (hz' : IsUniqueInvolution L z') :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤
      rankTwoSpan (Subgroup.closure ({t, u, z'} : Set Y)) := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  obtain ⟨hJ, hLK, hLJ, u₀, z₀, hu₀, hz₀, hne⟩ := hG
  obtain rfl : u = u₀ := hu.eq hu₀
  obtain rfl : z' = z₀ := hz'.eq hz₀
  have hA : IsElemAbelian 2 (Subgroup.closure ({t, u, z'} : Set Y)) :=
    isElemAbelian_closure_triangle hΩ ht hu hz' hJ hLK hLJ
  have h8 : Nat.card ↥(Subgroup.closure ({t, u, z'} : Set Y)) = 8 :=
    natCard_closure_triangle hΩ (noTwins_of_large hL) (CoreAssembly.mem_conjClass_self _) ht hu
      hz' hJ hLK hLJ hne
  have hAt : Subgroup.closure ({t, u, z'} : Set Y) ≤ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hLK hz').symm
  have hnorm : Subgroup.closure ({t, u, z'} : Set Y) ≤ Subgroup.normalizer
      (oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) : Set Y) := by
    intro a ha
    rw [mem_normalizer_iff_conjSub_eq, ← Thompson.oddCoreOf_conjSub_eq,
      layerY_conjSub_eq hΩ.conjInvariant (hAt ha)]
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two _ _ hA (by rw [h8]; norm_num) hnorm
    (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem gLinkStep_conj_oddCore (hL : TightLargeHypR r n Y R S t) (hA : TriNbrAll R t)
    {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {ν : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)}
    (hν : ν ∈ classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) :
    GLinkStep R t J (conjSub (ν : Y) J) := by
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
  obtain ⟨K', hK'K, hK'J, z', hz', hne⟩ := hA J hJ u hu
  have hG : GAdj R t J K' := ⟨hJ, hK'K, hK'J, u, z', hu, hz', hne⟩
  exact Or.inr ⟨K', hG, u, z', hu, hz', (ν : Y), layerY_le_centralizer ν.2,
    oddCoreOf_layerY_le_rankTwoSpan hL hG hu hz' ⟨ν, hν, rfl⟩, rfl⟩

theorem reflTransGen_gLinkStep_of_mem_omegaNbr (hL : TightLargeHypR r n Y R S t)
    (hA : TriNbrAll R t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) :
    Relation.ReflTransGen (GLinkStep R t) J M := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  have hnt := noTwins_of_large hL
  have h := TightLargeHypR.typeRFam hL
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM.1
  by_cases hwu : w = t * u
  · obtain ⟨K', hK'K, hK'J, z', hz', hne⟩ := hA J hJ u hu
    have hG₁ : GAdj R t J K' := ⟨hJ, hK'K, hK'J, u, z', hu, hz', hne⟩
    have hKK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hK'K.1 hK'K
    have hJK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hK'K.1 hK'J
    have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
    have ntu : t ≠ u := fun h => hJ.2.1 (hnt _ hK J ⟨hJ.1, t, ht, h ▸ hu⟩)
    obtain ⟨P, hP, -, hPt, hPu⟩ :=
      exists_isSylow2In_member_le_centralizer hL hK'K.1 hz' hKK' hJK' ht hu ntu ctu
    have hPw : P ≤ Subgroup.centralizer ({w} : Set Y) := by
      intro p hp
      have e1 : p * t = t * p := Subgroup.mem_centralizer_singleton_iff.mp (hPt hp)
      have e2 : p * u = u * p := Subgroup.mem_centralizer_singleton_iff.mp (hPu hp)
      rw [Subgroup.mem_centralizer_singleton_iff, hwu]
      calc p * (t * u) = (p * t) * u := by group
        _ = (t * p) * u := by rw [e1]
        _ = t * (p * u) := by group
        _ = t * (u * p) := by rw [e2]
        _ = t * u * p := by group
    have hne' : K' ≠ M := by
      intro e
      subst e
      exact hne (hwu ▸ hz'.eq hw)
    have hK'M : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M :=
      ⟨hK'K.1, hne', P, mem_RSet_of_isSylow2In hK'K.1 hP, hP.1,
        hPw.trans (h.tight M hM.1 w hw)⟩
    have hMK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hM.1 hK'K.1 hK'M
    have nuz : u ≠ z' := fun h => hK'J.2.1 (hnt _ hJ.1 K' ⟨hK'K.1, u, hu, h ▸ hz'⟩)
    have hG₂ : GAdj R t K' M := ⟨hK'K, hM, hMK', z', w, hz', hw, fun h => nuz (by
      rw [hwu] at h
      exact mul_left_cancel h)⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Or.inl hG₁)) (Or.inl hG₂)
  · exact Relation.ReflTransGen.single (Or.inl ⟨hJ, hM, hMJ, u, w, hu, hw, hwu⟩)

theorem reflTransGen_gLinkStep_of_secImg_eq (hL : TightLargeHypR r n Y R S t)
    (hA : TriNbrAll R t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (heq : secImg (CoreAssembly.conjClass (tightCore R)) t J =
      secImg (CoreAssembly.conjClass (tightCore R)) t M) :
    Relation.ReflTransGen (GLinkStep R t) J M := by
  obtain ⟨ν, hν, rfl⟩ := exists_conj_of_secImg_eq (TightLargeHypR.typeRFam hL)
    (xMem_of_mem_omegaNbr_core hL hJ) (xMem_of_mem_omegaNbr_core hL hM) heq
  exact Relation.ReflTransGen.single (gLinkStep_conj_oddCore hL hA hJ hν)

theorem reflTransGen_gLinkStep_of_secImg_nbr (hL : TightLargeHypR r n Y R S t)
    (hA : TriNbrAll R t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hnbr : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    Relation.ReflTransGen (GLinkStep R t) J M := by
  obtain ⟨ν, hν, hMν⟩ := exists_conj_omegaNbr_of_secImg (TightLargeHypR.typeRFam hL)
    (xMem_of_mem_omegaNbr_core hL hJ) (xMem_of_mem_omegaNbr_core hL hM) hnbr
  have hJν := conjSub_mem_omegaNbr_core hL hJ (layerY_le_centralizer ν.2)
  exact (Relation.ReflTransGen.single (gLinkStep_conj_oddCore hL hA hJ hν)).trans
    (reflTransGen_gLinkStep_of_mem_omegaNbr hL hA hJν hM hMν)

theorem gLinkStep_of_linkConn (hL : TightLargeHypR r n Y R S t) (hA : TriNbrAll R t)
    (hconn : DConnected (coreLinkFam R t)) {J J' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    Relation.ReflTransGen (GLinkStep R t) J J' := by
  have hΦ := ((TightLargeHypR.typeRFam hL).secFam (x := t)).hyp
  have key : ∀ b, Relation.ReflTransGen
      (fun Mb Nb => Nb ∈ coreLinkFam R t ∧ dAdj (coreLinkFam R t) Mb Nb)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J) b →
      b ∈ coreLinkFam R t ∧
        ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          secImg (CoreAssembly.conjClass (tightCore R)) t M = b →
            Relation.ReflTransGen (GLinkStep R t) J M := by
    intro b hb
    induction hb with
    | refl => exact ⟨⟨J, hJ, rfl⟩, fun M hM hMb =>
        reflTransGen_gLinkStep_of_secImg_eq hL hA hJ hM hMb.symm⟩
    | @tail b c _ hbc ih =>
      obtain ⟨⟨M₁, hM₁, rfl⟩, hP⟩ := ih
      obtain ⟨hc, hadj⟩ := hbc
      refine ⟨hc, fun M hM hMc => ?_⟩
      subst hMc
      have hnbr : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
          omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
            (secImg (CoreAssembly.conjClass (tightCore R)) t M₁) := by
        rcases hadj with h1 | h2
        · exact omegaNbr_secFam_of_coreLinkFam hL h1
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM))
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM₁))
            (omegaNbr_secFam_of_coreLinkFam hL h2)
      exact (hP M₁ hM₁ rfl).trans (reflTransGen_gLinkStep_of_secImg_nbr hL hA hM₁ hM hnbr)
  exact (key _ (hconn _ ⟨J, hJ, rfl⟩ _ ⟨J', hJ', rfl⟩)).2 J' hJ' rfl

@[expose] def TightGraphLinkAR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      TriNbrAll R t → ¬ DConnected (coreLinkFam R t) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (GLinkStep R t) J J'

theorem tightGraphLinkR_of_caseA (hgA : TightGraphLinkAR r n) : TightGraphLinkR r n := by
  intro Y _ _ R S t hL hc hA J hJ J' hJ'
  by_cases hP : DConnected (coreLinkFam R t)
  · exact gLinkStep_of_linkConn hL hA hP hJ hJ'
  · exact hgA Y R S t hL hc hA hP J hJ J' hJ'

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
