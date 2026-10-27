module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupIdeal
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv Topology
open scoped CFSG.ConvolutionPoints

theorem exists_isOpen_inter_subset_of_isConstructible {R : Type} [CommRing R]
    {C : Set (PrimeSpectrum R)} (hC : IsConstructible C) :
    ∀ {Y : Set (PrimeSpectrum R)}, IsIrreducible Y → Y ⊆ closure (C ∩ Y) →
      ∃ O : Set (PrimeSpectrum R), IsOpen O ∧ (O ∩ Y).Nonempty ∧ O ∩ Y ⊆ C := by
  induction C, hC using IsConstructible.induction_of_isTopologicalBasis
    (fun r : R => (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)))
    PrimeSpectrum.isTopologicalBasis_basic_opens
    (fun r => PrimeSpectrum.isCompact_basicOpen r) with
  | sdiff i s hs =>
    intro Y hY hdense
    refine ⟨PrimeSpectrum.basicOpen i, (PrimeSpectrum.basicOpen i).2, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hY.nonempty
      obtain ⟨y, hy⟩ := closure_nonempty_iff.1 ⟨x, hdense hx⟩
      exact ⟨y, hy.1.1, hy.2⟩
    · rintro x ⟨hxi, hxY⟩
      refine ⟨hxi, ?_⟩
      have hcl : IsClosed (⋃ j ∈ s, (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum R)))ᶜ :=
        (isOpen_biUnion fun j _ => (PrimeSpectrum.basicOpen j).2).isClosed_compl
      exact (hcl.closure_subset_iff.2 fun y hy => hy.1.2) (hdense hxY)
  | union s hs t ht ihs iht =>
    intro Y hY hdense
    have h : Y ⊆ closure (s ∩ Y) ∪ closure (t ∩ Y) := by
      rw [← closure_union, ← Set.union_inter_distrib_right]
      exact hdense
    rcases isPreirreducible_iff_isClosed_union_isClosed.1 hY.isPreirreducible _ _
      isClosed_closure isClosed_closure h with h | h
    · obtain ⟨O, hO, hne, hsub⟩ := ihs hY h
      exact ⟨O, hO, hne, hsub.trans Set.subset_union_left⟩
    · obtain ⟨O, hO, hne, hsub⟩ := iht hY h
      exact ⟨O, hO, hne, hsub.trans Set.subset_union_right⟩

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

theorem exists_basicOpen_subset_subgroupPoints (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hcons : IsPointConstructible k (subgroupPoints H))
    (hirr : IsPointIrreducible k (subgroupPoints H)) :
    ∃ f : A, (∃ u ∈ pointsZero k (subgroupIdeal H), u f ≠ 0) ∧
      ∀ v ∈ pointsZero k (subgroupIdeal H), v f ≠ 0 → v ∈ subgroupPoints H := by
  obtain ⟨C, hC, hCH⟩ := hcons
  set Y := closure (pointSpec '' subgroupPoints H)
  have hY : IsIrreducible Y := hirr.closure
  have hdense : Y ⊆ closure (C ∩ Y) := by
    refine closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, subset_closure ⟨y, hy, rfl⟩⟩
    rw [hCH] at hy
    exact hy
  obtain ⟨O, hO, hne, hsub⟩ := exists_isOpen_inter_subset_of_isConstructible hC hY hdense
  obtain ⟨u, hu⟩ := exists_algHom_mem_of_isLocallyClosed k A
    (hO.isLocallyClosed.inter isClosed_closure.isLocallyClosed) hne
  obtain ⟨_, ⟨f, rfl⟩, huf, hfO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hu.1 hO
  have hZ : ∀ v : A →ₐ[k] k, v ∈ pointsZero k (subgroupIdeal H) ↔ pointSpec v ∈ Y := by
    intro v
    rw [pointsZero_pointsIdeal]
    rfl
  refine ⟨f, ⟨u, (hZ u).2 hu.2, huf⟩, fun v hv hvf => ?_⟩
  have h1 : pointSpec v ∈ O := hfO hvf
  have h2 : pointSpec v ∈ C := hsub ⟨h1, (hZ v).1 hv⟩
  rw [hCH]
  exact h2

theorem pointsZero_subgroupIdeal_eq (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hcons : IsPointConstructible k (subgroupPoints H))
    (hirr : IsPointIrreducible k (subgroupPoints H)) :
    pointsZero k (subgroupIdeal H) = subgroupPoints H := by
  obtain ⟨f, ⟨u, hu, huf⟩, hf⟩ := exists_basicOpen_subset_subgroupPoints H hcons hirr
  have : (subgroupIdeal H).IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hirr
  refine Set.Subset.antisymm (fun z hz => ?_) (subset_pointsZero_pointsIdeal _)
  have hzZ : toConv z ∈ closureSubgroup H := hz
  have huZ : toConv u ∈ closureSubgroup H := hu
  set fz := rightTransCo (toConv z) f
  have hfz_apply : ∀ y : WithConv (A →ₐ[k] k), y.ofConv fz = (y * toConv z).ofConv f := by
    intro y
    have h := congrArg (fun p : WithConv (A →ₐ[k] k) => p.ofConv f)
      (point_comp_rightTransCo (toConv z) y)
    exact h
  have hf_notMem : Ideal.Quotient.mk (subgroupIdeal H) f ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => huf (hu f h)
  have hfz_notMem : Ideal.Quotient.mk (subgroupIdeal H) fz ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    have hmem : toConv u * (toConv z)⁻¹ ∈ closureSubgroup H :=
      (closureSubgroup H).mul_mem huZ ((closureSubgroup H).inv_mem hzZ)
    have h1 := hmem fz h
    rw [hfz_apply, inv_mul_cancel_right] at h1
    exact huf h1
  obtain ⟨w', hw'⟩ : ∃ w' : (A ⧸ subgroupIdeal H) →ₐ[k] k,
      w' (Ideal.Quotient.mk (subgroupIdeal H) (f * fz)) ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [map_mul] at hall
    exact mul_ne_zero hf_notMem hfz_notMem
      (eq_zero_of_forall_algHom k (A ⧸ subgroupIdeal H) _ fun w' => by
        rw [← map_mul]
        exact hall w')
  set w := w'.comp (Ideal.Quotient.mkₐ k (subgroupIdeal H)) with hw
  have hwZ : w ∈ pointsZero k (subgroupIdeal H) := fun a ha => by
    simp [hw, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have hwf : w f * w fz ≠ 0 := by
    rw [← map_mul]
    exact hw'
  have hwH : toConv w ∈ H := hf w hwZ (left_ne_zero_of_mul hwf)
  have hwzZ : toConv w * toConv z ∈ closureSubgroup H :=
    (closureSubgroup H).mul_mem hwZ hzZ
  have hwzH : toConv w * toConv z ∈ H := by
    have hne : (toConv w * toConv z).ofConv f ≠ 0 := by
      rw [← hfz_apply]
      exact right_ne_zero_of_mul hwf
    exact hf _ hwzZ hne
  have h := H.mul_mem (H.inv_mem hwH) hwzH
  rwa [inv_mul_cancel_left] at h

theorem isPointClosed_subgroupPoints (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hcons : IsPointConstructible k (subgroupPoints H))
    (hirr : IsPointIrreducible k (subgroupPoints H)) :
    IsPointClosed k (subgroupPoints H) :=
  ⟨closure (pointSpec '' subgroupPoints H), isClosed_closure, by
    rw [← pointsZero_pointsIdeal, pointsZero_subgroupIdeal_eq H hcons hirr]⟩

theorem pointsIdeal_pointsZero_of_isRadical {B : Type} [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] {J : Ideal B} (hJ : J.IsRadical) :
    pointsIdeal (pointsZero k J) = J := by
  refine le_antisymm (fun a ha => ?_) (fun a ha => mem_pointsIdeal.2 fun y hy => hy a ha)
  have : IsReduced (B ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).1 hJ
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_zero_of_forall_algHom k (B ⧸ J) _ fun φ => ?_
  have hφ : φ.comp (Ideal.Quotient.mkₐ k J) ∈ pointsZero k J := fun b hb => by
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hb]
  exact mem_pointsIdeal.1 ha _ hφ

theorem eq_subgroupIdeal_of_pointsZero_eq (H : Subgroup (WithConv (A →ₐ[k] k)))
    {J : Ideal A} (hJ : J.IsRadical) (hJH : pointsZero k J = subgroupPoints H) :
    J = subgroupIdeal H := by
  rw [← pointsIdeal_pointsZero_of_isRadical (k := k) hJ, hJH]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem closureSubgroup_eq (H : Subgroup (WithConv (A →ₐ[k] k)))
    (h : pointsZero k (subgroupIdeal H) = subgroupPoints H) : closureSubgroup H = H := by
  ext y
  rw [mem_closureSubgroup, h]
  rfl

@[expose] def subgroupQuotientPointsEquiv (H : Subgroup (WithConv (A →ₐ[k] k)))
    (h : pointsZero k (subgroupIdeal H) = subgroupPoints H) :
    WithConv ((A ⧸ subgroupIdeal H) →ₐ[k] k) ≃* H :=
  (quotientPointsEquiv H).trans (MulEquiv.subgroupCongr (closureSubgroup_eq H h))

theorem subgroupQuotientPointsEquiv_apply (H : Subgroup (WithConv (A →ₐ[k] k)))
    (h : pointsZero k (subgroupIdeal H) = subgroupPoints H)
    (φ : WithConv ((A ⧸ subgroupIdeal H) →ₐ[k] k)) :
    ((subgroupQuotientPointsEquiv H h φ : H) : WithConv (A →ₐ[k] k)).ofConv =
      φ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal H)) :=
  rfl

variable (k) in
structure IsConnectedAlgebraicSubgroup (H : Subgroup (WithConv (A →ₐ[k] k))) : Prop where
  isPointClosed : IsPointClosed k (subgroupPoints H)
  pointsZero_eq : pointsZero k (subgroupIdeal H) = subgroupPoints H
  isHopfIdeal : (subgroupIdeal H).IsHopfIdeal k
  isRadical : (subgroupIdeal H).IsRadical
  isPrime : (subgroupIdeal H).IsPrime
  isReduced : IsReduced (A ⧸ subgroupIdeal H)
  finiteType : Algebra.FiniteType k (A ⧸ subgroupIdeal H)
  isDomain : IsDomain (A ⧸ subgroupIdeal H)
  connectedSpace : ConnectedSpace (PrimeSpectrum (A ⧸ subgroupIdeal H))
  points : ∃ e : WithConv ((A ⧸ subgroupIdeal H) →ₐ[k] k) ≃* H, ∀ φ,
    ((e φ : H) : WithConv (A →ₐ[k] k)).ofConv =
      φ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal H))
  unique : ∀ J : Ideal A, J.IsRadical → pointsZero k J = subgroupPoints H → J = subgroupIdeal H

theorem isConnectedAlgebraicSubgroup (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hcons : IsPointConstructible k (subgroupPoints H))
    (hirr : IsPointIrreducible k (subgroupPoints H)) :
    IsConnectedAlgebraicSubgroup k H := by
  have hZ := pointsZero_subgroupIdeal_eq H hcons hirr
  have hprime : (subgroupIdeal H).IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hirr
  exact
    { isPointClosed := isPointClosed_subgroupPoints H hcons hirr
      pointsZero_eq := hZ
      isHopfIdeal := inferInstance
      isRadical := isRadical_pointsIdeal _
      isPrime := hprime
      isReduced := inferInstance
      finiteType := inferInstance
      isDomain := inferInstance
      connectedSpace := inferInstance
      points := ⟨subgroupQuotientPointsEquiv H hZ, subgroupQuotientPointsEquiv_apply H hZ⟩
      unique := fun _ hJ hJH => eq_subgroupIdeal_of_pointsZero_eq H hJ hJH }

end CFSG.LieType.AlgebraicGroups
