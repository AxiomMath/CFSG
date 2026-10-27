module

public import CFSG.ClassicalInvolution.Q3.TL4LinkCases

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

namespace LinkDisc

section Graph

variable {Y : Type} [Group Y]

@[expose] def HasGNbr (R : Subgroup Y) (t : Y) (J : Subgroup Y) : Prop :=
  ∀ u : Y, IsUniqueInvolution J u →
    ∃ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J ∧
        ∃ z' : Y, IsUniqueInvolution K' z' ∧ z' ≠ t * u

theorem hasGNbr_of_not_noGNbr {R : Subgroup Y} {t : Y} {J : Subgroup Y}
    (h : ¬ NoGNbr R t J) : HasGNbr R t J := by
  unfold NoGNbr at h
  push Not at h
  obtain ⟨K', hK'K, hK'J, u, z', hu, hz', hne⟩ := h
  intro u' hu'
  obtain rfl := hu.eq hu'
  exact ⟨K', hK'K, hK'J, z', hz', hne⟩

theorem secImg_eq_of_subgroupOf_eq {R : Subgroup Y} {t : Y} {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (e : (secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t) =
      (secImg (CoreAssembly.conjClass (tightCore R)) t M).subgroupOf (linkGrp R t)) :
    secImg (CoreAssembly.conjClass (tightCore R)) t J =
      secImg (CoreAssembly.conjClass (tightCore R)) t M := by
  have h1 := Subgroup.subgroupOf_inj.mp e
  rwa [inf_of_le_left (le_linkGrp hJ), inf_of_le_left (le_linkGrp hM)] at h1

end Graph

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hasGNbr_conj (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hP : HasGNbr R t J) {c : Y} (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    HasGNbr R t (conjSub c J) := by
  intro u' hu'
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
  obtain ⟨K', hK'K, hK'J, z', hz', hne⟩ := hP u hu
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have hu'' : c * u * c⁻¹ = u' := (hu.conj c).eq hu'
  refine ⟨conjSub c K', conjSub_mem_omegaNbr_core hL hK'K hc,
    omegaNbr_conj hL.datum.hypOmegaGen.conjInvariant hK'J c, c * z' * c⁻¹, hz'.conj c, ?_⟩
  intro h
  apply hne
  have h2 : c * z' * c⁻¹ = c * (t * u) * c⁻¹ := by
    rw [h, ← hu'']
    nth_rewrite 1 [← hct]
    group
  calc z' = c⁻¹ * (c * z' * c⁻¹) * c := by group
    _ = c⁻¹ * (c * (t * u) * c⁻¹) * c := by rw [h2]
    _ = t * u := by group

theorem hasGNbr_of_mem_omegaNbr (hL : TightLargeHypR r n Y R S t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hMJ : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) (hP : HasGNbr R t J) :
    HasGNbr R t M := by
  intro w hw
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have ht := hd.isUniqueInvolution_core
  have hnt := noTwins_of_large hL
  have h := TightLargeHypR.typeRFam hL
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ht2 : t * t = 1 := ht.sq
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  have hJM : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hM.1 hMJ
  by_cases hwu : w = t * u
  · obtain ⟨K', hK'K, hK'J, z', hz', hne⟩ := hP u hu
    have hKK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hK'K.1 hK'K
    have hJK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hK'K.1 hK'J
    have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
    have ntu : t ≠ u := fun e => hJ.2.1 (hnt _ hK J ⟨hJ.1, t, ht, e ▸ hu⟩)
    obtain ⟨P, hP', -, hPt, hPu⟩ :=
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
      ⟨hK'K.1, hne', P, mem_RSet_of_isSylow2In hK'K.1 hP', hP'.1,
        hPw.trans (h.tight M hM.1 w hw)⟩
    refine ⟨K', hK'K, hK'M, z', hz', fun e => ?_⟩
    have hzu : z' = u := by rw [e, hwu, ← mul_assoc, ht2, one_mul]
    exact hK'J.2.1 (hnt _ hJ.1 K' ⟨hK'K.1, u, hu, hzu ▸ hz'⟩)
  · refine ⟨J, hJ, hJM, u, hu, fun e => hwu ?_⟩
    rw [e, ← mul_assoc, ht2, one_mul]

theorem hasGNbr_of_secImg_eq (hL : TightLargeHypR r n Y R S t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (heq : secImg (CoreAssembly.conjClass (tightCore R)) t J =
      secImg (CoreAssembly.conjClass (tightCore R)) t M) (hP : HasGNbr R t J) :
    HasGNbr R t M := by
  obtain ⟨ν, -, rfl⟩ := exists_conj_of_secImg_eq (TightLargeHypR.typeRFam hL)
    (xMem_of_mem_omegaNbr_core hL hJ) (xMem_of_mem_omegaNbr_core hL hM) heq
  exact hasGNbr_conj hL hJ hP (layerY_le_centralizer ν.2)

theorem hasGNbr_of_secImg_nbr (hL : TightLargeHypR r n Y R S t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hnbr : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J)) (hP : HasGNbr R t J) :
    HasGNbr R t M := by
  obtain ⟨ν, -, hMν⟩ := exists_conj_omegaNbr_of_secImg (TightLargeHypR.typeRFam hL)
    (xMem_of_mem_omegaNbr_core hL hJ) (xMem_of_mem_omegaNbr_core hL hM) hnbr
  have hc := layerY_le_centralizer ν.2
  exact hasGNbr_of_mem_omegaNbr hL (conjSub_mem_omegaNbr_core hL hJ hc) hM hMν
    (hasGNbr_conj hL hJ hP hc)

theorem triNbrAll_of_linkConn (hL : TightLargeHypR r n Y R S t)
    (hconn : DConnected (linkFam R t)) {J₀ : Subgroup Y}
    (hJ₀ : J₀ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hP₀ : HasGNbr R t J₀) : TriNbrAll R t := by
  have hΦ := ((TightLargeHypR.typeRFam hL).secFam (x := t)).hyp
  have key : ∀ b, Relation.ReflTransGen
      (fun Mb Nb => Nb ∈ linkFam R t ∧ dAdj (linkFam R t) Mb Nb)
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J₀).subgroupOf (linkGrp R t)) b →
      b ∈ linkFam R t ∧
        ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          (secImg (CoreAssembly.conjClass (tightCore R)) t M).subgroupOf (linkGrp R t) = b →
            HasGNbr R t M := by
    intro b hb
    induction hb with
    | refl =>
      refine ⟨subgroupOf_mem_linkRestrict hJ₀, fun M hM hMb => ?_⟩
      exact hasGNbr_of_secImg_eq hL hJ₀ hM (secImg_eq_of_subgroupOf_eq hJ₀ hM hMb.symm) hP₀
    | @tail b c _ hbc ih =>
      obtain ⟨⟨_, ⟨M₁, hM₁, rfl⟩, -, rfl⟩, hP⟩ := ih
      obtain ⟨hc, hadj⟩ := hbc
      refine ⟨hc, fun M hM hMc => ?_⟩
      subst hMc
      have hnbr : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
          omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
            (secImg (CoreAssembly.conjClass (tightCore R)) t M₁) := by
        rcases hadj with h1 | h2
        · exact omegaNbr_secFam_of_link hL hM₁ hM h1
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM))
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM₁))
            (omegaNbr_secFam_of_link hL hM hM₁ h2)
      exact hasGNbr_of_secImg_nbr hL hM₁ hM hnbr (hP M₁ hM₁ rfl)
  intro J hJ
  exact (key _ (hconn _ (subgroupOf_mem_linkRestrict hJ₀) _
    (subgroupOf_mem_linkRestrict hJ))).2 J hJ rfl

@[expose] def TightLinkDiscNoTriR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t →
      (∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J) →
        ¬ DConnected (linkFam R t)

theorem tightLinkDiscR_of (hB : TightLinkDiscNoTriR r n) : TightLinkDiscR r n := by
  intro Y _ _ R S t hL hc hT hα hconn
  by_cases hall : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      NoGNbr R t J
  · exact hB Y R S t hL hc hT hα hall hconn
  · push Not at hall
    obtain ⟨J₀, hJ₀, hnot⟩ := hall
    exact hT (triNbrAll_of_linkConn hL hconn hJ₀ (hasGNbr_of_not_noGNbr hnot))

end Cit3

end LinkDisc

end CFSG.ClassicalInvolution.Q3.TL4
