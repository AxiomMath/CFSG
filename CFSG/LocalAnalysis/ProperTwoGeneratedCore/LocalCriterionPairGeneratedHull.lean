module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def rightInvolutionCommutatorSubgroup (t : G) (J : Subgroup G) : Subgroup G :=
  Subgroup.closure (Set.range (fun j : J => t⁻¹ * (j : G)⁻¹ * t * j))

@[expose] def pairGeneratedHull (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t : G) : Subgroup G :=
  (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔
    rightInvolutionCommutatorSubgroup t (pairOddCore H beta)

theorem conjugacyWithin_of_odd_involution_product (K : Subgroup G) {s v : G}
    (hsK : s ∈ K) (hvK : v ∈ K) (hs : orderOf s = 2) (hv : orderOf v = 2)
    (hodd : Odd (orderOf (s * v))) : v ∈ conjugacyWithin K s := by
  have hsI : IsInvolution s :=
    ⟨(orderOf_eq_prime_iff.mp hs).2, (orderOf_eq_prime_iff.mp hs).1⟩
  have hvI : IsInvolution v :=
    ⟨(orderOf_eq_prime_iff.mp hv).2, (orderOf_eq_prime_iff.mp hv).1⟩
  obtain ⟨a, ha, hconjugate⟩ := exists_zpowers_conjugator_of_odd_product hsI hvI hodd
  have haK : a ∈ K := (Subgroup.zpowers_le.mpr (K.mul_mem hsK hvK)) ha
  exact ⟨⟨a, haK⟩, hconjugate⟩

theorem conjugacyWithin_trans {K : Subgroup G} {z t s : G}
    (ht : t ∈ conjugacyWithin K z) (hs : s ∈ conjugacyWithin K t) :
    s ∈ conjugacyWithin K z := by
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨b, rfl⟩ := hs
  refine ⟨a * b, ?_⟩
  simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]

theorem involution_product_order_swap {s t : G}
    (hs : orderOf s = 2) (ht : orderOf t = 2) : orderOf (s * t) = orderOf (t * s) := by
  calc
    orderOf (s * t) = orderOf ((s * t)⁻¹) := (orderOf_inv _).symm
    _ = orderOf (t * s) := by
      rw [mul_inv_rev, inv_eq_self_of_orderOf_eq_two hs, inv_eq_self_of_orderOf_eq_two ht]

theorem pair_commutator_eq_closure_inverted_set [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightInvolutionCommutatorSubgroup t (pairOddCore H beta) =
      Subgroup.closure (pairInvertedSet H beta t) := by
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two
    (order_two_of_mem_pointClass h.distinguished_order ht.1)
  have hclass := pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht
  have hI := pair_inverted_set_eq_products h S hzS hzcenter hbeta ht
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, rfl⟩
    have hsF : (j : G)⁻¹ * t * j ∈ rightPairFlipFiber H z beta :=
      hclass.symm ▸ (show (j : G)⁻¹ * t * j ∈
        conjugacyWithin (pairOddCore H beta) t from ⟨j, rfl⟩)
    have hproductI : ((j : G)⁻¹ * t * j) * t ∈ pairInvertedSet H beta t :=
      hI.symm ▸ (show ((j : G)⁻¹ * t * j) * t ∈
        rightPairFlipProducts H z beta t from ⟨_, hsF, rfl⟩)
    have heq : t⁻¹ * (j : G)⁻¹ * t * j = (((j : G)⁻¹ * t * j) * t)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, htinv]
      group
    change t⁻¹ * (j : G)⁻¹ * t * j ∈ Subgroup.closure (pairInvertedSet H beta t)
    rw [heq]
    exact (Subgroup.closure (pairInvertedSet H beta t)).inv_mem
      (Subgroup.subset_closure hproductI)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hI ▸ hx
    obtain ⟨j, rfl⟩ := hclass ▸ hs
    have hcommutator : t⁻¹ * (j : G)⁻¹ * t * j ∈
        rightInvolutionCommutatorSubgroup t (pairOddCore H beta) :=
      Subgroup.subset_closure ⟨j, rfl⟩
    have heq : ((j : G)⁻¹ * t * j) * t = (t⁻¹ * (j : G)⁻¹ * t * j)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, htinv]
      group
    change ((j : G)⁻¹ * t * j) * t ∈
      rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    rw [heq]
    exact (rightInvolutionCommutatorSubgroup t (pairOddCore H beta)).inv_mem hcommutator

theorem pair_commutator_le_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤ pairOddCore H beta ∧
      pairOddCore H beta ≤ H := by
  refine ⟨?_, (pairOddCore_le H beta t).2.2⟩
  rw [pair_commutator_eq_closure_inverted_set h S hzS hzcenter hbeta ht]
  exact (Subgroup.closure_le _).mpr (fun _ hx => hx.1)

theorem point_subgroup_class_le_pair_generated_hull [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    conjugacyWithin H z ⊆ (pairGeneratedHull H z beta t : Set G) := by
  let K := pairGeneratedHull H z beta t
  have hzK : z ∈ K := (show Subgroup.zpowers z ≤ K from
    le_sup_left.trans le_sup_left) (Subgroup.mem_zpowers z)
  have hR : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤ K := le_sup_right
  have hIK : pairInvertedSet H beta t ⊆ (K : Set G) := by
    intro i hi
    apply hR
    rw [pair_commutator_eq_closure_inverted_set h S hzS hzcenter hbeta ht]
    exact Subgroup.subset_closure hi
  rintro x ⟨a, rfl⟩
  have hfactor := point_subgroup_eq_centralizer_mul_inverted_set h S hzS hzcenter hbeta ht
  have ha : (a : G) ∈ (H : Set G) := a.property
  rw [hfactor] at ha
  obtain ⟨c, hc, i, hi, hci⟩ := Set.mem_mul.mp ha
  have hconjugateC : c⁻¹ * z * c = z := by
    have hccomm := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [mul_assoc, ← hccomm, inv_mul_cancel_left]
  have heq : (a : G)⁻¹ * z * a = i⁻¹ * z * i := by
    rw [← hci, mul_inv_rev]
    calc
      i⁻¹ * c⁻¹ * z * (c * i) = i⁻¹ * (c⁻¹ * z * c) * i := by group
      _ = i⁻¹ * z * i := by rw [hconjugateC]
  rw [heq]
  exact K.mul_mem (K.mul_mem (K.inv_mem (hIK hi)) hzK) (hIK hi)

theorem pair_flips_mem_internal_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightPairFlipFiber H z beta ⊆ conjugacyWithin (pairGeneratedHull H z beta t) z := by
  let K := pairGeneratedHull H z beta t
  let R := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  have hzK : z ∈ K := (show Subgroup.zpowers z ≤ K from
    le_sup_left.trans le_sup_left) (Subgroup.mem_zpowers z)
  have htK : t ∈ K := (show Subgroup.zpowers t ≤ K from
    le_sup_right.trans le_sup_left) (Subgroup.mem_zpowers t)
  have hRK : R ≤ K := le_sup_right
  have htorder := order_two_of_mem_pointClass h.distinguished_order ht.1
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two htorder
  have hoddzt : Odd (orderOf (z * t)) := by
    rw [involution_product_order_swap h.distinguished_order htorder]
    apply Nat.not_even_iff_odd.mp
    intro heven
    exact pair_flip_not_mem_point hbeta ht (pointClass_mem_of_even_product_order h ht.1 heven)
  have htclassK := conjugacyWithin_of_odd_involution_product K hzK htK
    h.distinguished_order htorder hoddzt
  have hclass := pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht
  have hI := pair_inverted_set_eq_products h S hzS hzcenter hbeta ht
  intro s hs
  have hsK : s ∈ K := by
    obtain ⟨j, rfl⟩ := hclass ▸ hs
    have hcR : t⁻¹ * (j : G)⁻¹ * t * j ∈ R := Subgroup.subset_closure ⟨j, rfl⟩
    have hmem := K.mul_mem htK (hRK hcR)
    simpa only [mul_assoc, mul_inv_cancel_left] using hmem
  have hstJ : s * t ∈ pairOddCore H beta := by
    have hstI : s * t ∈ pairInvertedSet H beta t :=
      hI.symm ▸ (show s * t ∈ rightPairFlipProducts H z beta t from ⟨s, hs, rfl⟩)
    exact hstI.1
  have hoddts : Odd (orderOf (t * s)) := by
    rw [involution_product_order_swap htorder
      (order_two_of_mem_pointClass h.distinguished_order hs.1)]
    exact (pairOddCore_odd H beta).of_dvd_nat
      ((Subgroup.orderOf_coe (⟨s * t, hstJ⟩ : pairOddCore H beta)).symm ▸
        orderOf_dvd_natCard (⟨s * t, hstJ⟩ : pairOddCore H beta))
  exact conjugacyWithin_trans htclassK
    (conjugacyWithin_of_odd_involution_product K htK hsK htorder
      (order_two_of_mem_pointClass h.distinguished_order hs.1) hoddts)

theorem pair_generated_hull_eq_internal_class_closure [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    pairGeneratedHull H z beta t =
      Subgroup.closure (conjugacyWithin (pairGeneratedHull H z beta t) z) := by
  let K := pairGeneratedHull H z beta t
  let L := Subgroup.closure (conjugacyWithin K z)
  have hzK : z ∈ K := (show Subgroup.zpowers z ≤ K from
    le_sup_left.trans le_sup_left) (Subgroup.mem_zpowers z)
  have hzL : z ∈ L := Subgroup.subset_closure ⟨1, by simp⟩
  have hF := pair_flips_mem_internal_class h S hzS hzcenter hbeta ht
  have htL : t ∈ L := Subgroup.subset_closure (hF ht)
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two
    (order_two_of_mem_pointClass h.distinguished_order ht.1)
  have hRL : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤ L := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, rfl⟩
    have hsF : (j : G)⁻¹ * t * j ∈ rightPairFlipFiber H z beta :=
      (pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht).symm ▸
        (show (j : G)⁻¹ * t * j ∈ conjugacyWithin (pairOddCore H beta) t from ⟨j, rfl⟩)
    have hsL : (j : G)⁻¹ * t * j ∈ L := Subgroup.subset_closure (hF hsF)
    change t⁻¹ * (j : G)⁻¹ * t * j ∈ L
    have heq : t⁻¹ * (j : G)⁻¹ * t * j = t * ((j : G)⁻¹ * t * j) := by
      rw [htinv]
      group
    rw [heq]
    exact L.mul_mem htL hsL
  apply le_antisymm
  · exact sup_le (sup_le (Subgroup.zpowers_le.mpr hzL) (Subgroup.zpowers_le.mpr htL)) hRL
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, rfl⟩
    exact K.mul_mem (K.mul_mem (K.inv_mem a.property) hzK) a.property

theorem involution_point_pair_generated_subgroup_hull [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    let J := pairOddCore H beta
    let I := pairInvertedSet H beta t
    let R := rightInvolutionCommutatorSubgroup t J
    let K := pairGeneratedHull H z beta t
    R = Subgroup.closure I ∧ R ≤ J ∧ J ≤ H ∧
      conjugacyWithin H z ⊆ (K : Set G) ∧
      K = Subgroup.closure (conjugacyWithin K z) ∧ ¬ K ≤ H := by
  have hR := pair_commutator_le_odd_core h S hzS hzcenter hbeta ht
  refine ⟨pair_commutator_eq_closure_inverted_set h S hzS hzcenter hbeta ht,
    hR.1, hR.2, point_subgroup_class_le_pair_generated_hull h S hzS hzcenter hbeta ht,
    pair_generated_hull_eq_internal_class_closure h S hzS hzcenter hbeta ht, ?_⟩
  intro hKH
  exact pair_flip_not_mem_point hbeta ht
    (hKH ((show Subgroup.zpowers t ≤ pairGeneratedHull H z beta t from
      le_sup_right.trans le_sup_left) (Subgroup.mem_zpowers t)))

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
