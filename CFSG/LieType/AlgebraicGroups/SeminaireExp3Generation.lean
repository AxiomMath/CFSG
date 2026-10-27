module

public import CFSG.LieType.AlgebraicGroups.SeminaireExp3Rational

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.SeminaireExp3

open Topology Pointwise WithConv
open scoped CFSG.ConvolutionPoints

section Hopf

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

theorem exists_inv_mul_of_pointsIdeal_eq (H : Subgroup (WithConv (A →ₐ[k] k)))
    {C : Set (A →ₐ[k] k)} (hcons : IsPointConstructible k C) (hirr : IsPointIrreducible k C)
    (hI : pointsIdeal C = subgroupIdeal H) {z : A →ₐ[k] k}
    (hz : z ∈ pointsZero k (subgroupIdeal H)) :
    ∃ w ∈ C, ∃ w' ∈ C, toConv z = (toConv w)⁻¹ * toConv w' := by
  obtain ⟨C', hC', hCC'⟩ := hcons
  set Y := closure (pointSpec '' C)
  have hY : IsIrreducible Y := hirr.closure
  have hdense : Y ⊆ closure (C' ∩ Y) := by
    refine closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, subset_closure ⟨y, hy, rfl⟩⟩
    rw [hCC'] at hy
    exact hy
  obtain ⟨O, hO, hne, hsub⟩ := exists_isOpen_inter_subset_of_isConstructible hC' hY hdense
  obtain ⟨u, hu⟩ := exists_algHom_mem_of_isLocallyClosed k A
    (hO.isLocallyClosed.inter isClosed_closure.isLocallyClosed) hne
  obtain ⟨_, ⟨f, rfl⟩, huf, hfO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hu.1 hO
  have hZ : ∀ v : A →ₐ[k] k, v ∈ pointsZero k (subgroupIdeal H) ↔ pointSpec v ∈ Y := by
    intro v
    rw [← hI, pointsZero_pointsIdeal]
    rfl
  have hf : ∀ v ∈ pointsZero k (subgroupIdeal H), v f ≠ 0 → v ∈ C := fun v hv hvf => by
    have h1 : pointSpec v ∈ O := hfO hvf
    have h2 : pointSpec v ∈ C' := hsub ⟨h1, (hZ v).1 hv⟩
    rw [hCC']
    exact h2
  have hu' : u ∈ pointsZero k (subgroupIdeal H) := (hZ u).2 hu.2
  have : (subgroupIdeal H).IsPrime := by
    rw [← hI]
    exact PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hirr
  have hzZ : toConv z ∈ closureSubgroup H := hz
  have huZ : toConv u ∈ closureSubgroup H := hu'
  set fz := rightTransCo (toConv z) f
  have hfz_apply : ∀ y : WithConv (A →ₐ[k] k), y.ofConv fz = (y * toConv z).ofConv f := by
    intro y
    exact congrArg (fun p : WithConv (A →ₐ[k] k) => p.ofConv f)
      (point_comp_rightTransCo (toConv z) y)
  have hf_notMem : Ideal.Quotient.mk (subgroupIdeal H) f ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => huf (hu' f h)
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
  have hwC : w ∈ C := hf w hwZ (left_ne_zero_of_mul hwf)
  have hwzZ : toConv w * toConv z ∈ closureSubgroup H := (closureSubgroup H).mul_mem hwZ hzZ
  have hwzC : (toConv w * toConv z).ofConv ∈ C := by
    have hne : (toConv w * toConv z).ofConv f ≠ 0 := by
      rw [← hfz_apply]
      exact right_ne_zero_of_mul hwf
    exact hf _ hwzZ hne
  exact ⟨w, hwC, _, hwzC, by rw [toConv_ofConv, inv_mul_cancel_left]⟩

end Hopf

namespace ZariskiGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : Type} [Field k] {I : Type*}

@[expose] def wordSet (W : I → Set (ZariskiGL ι k)) (a : List (I × ℤˣ)) : Set (ZariskiGL ι k) :=
  (a.map fun p => W p.1 ^ (p.2 : ℤ)).prod

@[expose] def invWord (a : List (I × ℤˣ)) : List (I × ℤˣ) :=
  (a.map fun p => (p.1, -p.2)).reverse

variable (W : I → Set (ZariskiGL ι k))

theorem wordSet_nil : wordSet W [] = 1 :=
  rfl

theorem wordSet_cons (p : I × ℤˣ) (a : List (I × ℤˣ)) :
    wordSet W (p :: a) = W p.1 ^ (p.2 : ℤ) * wordSet W a := by
  simp [wordSet]

theorem wordSet_append (a b : List (I × ℤˣ)) :
    wordSet W (a ++ b) = wordSet W a * wordSet W b := by
  simp [wordSet]

theorem wordSet_invWord (a : List (I × ℤˣ)) : wordSet W (invWord a) = (wordSet W a)⁻¹ := by
  induction a with
  | nil => simp [invWord, wordSet]
  | cons p a ih =>
    have h : invWord (p :: a) = invWord a ++ [(p.1, -p.2)] := by simp [invWord]
    rw [h, wordSet_append, ih, wordSet_cons, wordSet_cons, wordSet_nil, mul_one, mul_inv_rev,
      Units.val_neg, zpow_neg]

theorem one_mem_wordSet (h1 : ∀ i, (1 : ZariskiGL ι k) ∈ W i) (a : List (I × ℤˣ)) :
    (1 : ZariskiGL ι k) ∈ wordSet W a := by
  induction a with
  | nil => exact Set.mem_one.2 rfl
  | cons p a ih =>
    rw [wordSet_cons]
    refine ⟨1, ?_, 1, ih, mul_one 1⟩
    rcases Int.units_eq_one_or p.2 with h | h
    · rw [h, Units.val_one, zpow_one]
      exact h1 p.1
    · rw [h, Units.val_neg, Units.val_one, zpow_neg_one, Set.mem_inv, inv_one]
      exact h1 p.1

theorem coe_closure_eq_iUnion_wordSet :
    (Subgroup.closure (⋃ i, W i) : Set (ZariskiGL ι k)) = ⋃ a, wordSet W a := by
  let U : Subgroup (ZariskiGL ι k) :=
    { carrier := ⋃ a, wordSet W a
      one_mem' := Set.mem_iUnion.2 ⟨[], Set.mem_one.2 rfl⟩
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
        obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hy
        refine Set.mem_iUnion.2 ⟨a ++ b, ?_⟩
        rw [wordSet_append]
        exact Set.mul_mem_mul ha hb
      inv_mem' := fun {x} hx => by
        obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
        refine Set.mem_iUnion.2 ⟨invWord a, ?_⟩
        rw [wordSet_invWord]
        exact Set.inv_mem_inv.2 ha }
  have hle : Subgroup.closure (⋃ i, W i) ≤ U := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    refine Set.mem_iUnion.2 ⟨[(i, 1)], ?_⟩
    rw [wordSet_cons, wordSet_nil, mul_one, Units.val_one, zpow_one]
    exact hi
  have hge : ∀ a, wordSet W a ⊆ Subgroup.closure (⋃ i, W i) := by
    intro a
    induction a with
    | nil =>
      intro x hx
      rw [wordSet_nil, Set.mem_one] at hx
      rw [hx]
      exact one_mem _
    | cons p a ih =>
      rw [wordSet_cons]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      refine mul_mem ?_ (ih hy)
      have hW : W p.1 ⊆ Subgroup.closure (⋃ i, W i) :=
        fun w hw => Subgroup.subset_closure (Set.mem_iUnion.2 ⟨p.1, hw⟩)
      rcases Int.units_eq_one_or p.2 with h | h
      · rw [h, Units.val_one, zpow_one] at hx
        exact hW hx
      · rw [h, Units.val_neg, Units.val_one, zpow_neg_one, Set.mem_inv] at hx
        simpa using inv_mem (hW hx)
  refine Set.Subset.antisymm (fun x hx => hle hx) ?_
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
  exact hge a ha

theorem wordSet_invWord_append (a : List (I × ℤˣ)) :
    wordSet W (invWord a ++ a) = (wordSet W a)⁻¹ * wordSet W a := by
  rw [wordSet_append, wordSet_invWord]

variable [IsAlgClosed k]

theorem isDomainImage_wordSet (hW : ∀ i, IsDomainImage k (pt '' W i)) (a : List (I × ℤˣ)) :
    IsDomainImage k (pt '' wordSet W a) := by
  induction a with
  | nil => exact isDomainImage_one
  | cons p a ih =>
    rw [wordSet_cons]
    exact isDomainImage_mul (isDomainImage_zpow_units (hW p.1) p.2) ih

theorem closure_eq_wordSet (hW : ∀ i, IsDomainImage k (pt '' W i))
    (h1 : ∀ i, (1 : ZariskiGL ι k) ∈ W i) :
    IsClosed (Subgroup.closure (⋃ i, W i) : Set (ZariskiGL ι k)) ∧
    IsIrreducible (Subgroup.closure (⋃ i, W i) : Set (ZariskiGL ι k)) ∧
    ∃ a : List (I × ℤˣ), (Subgroup.closure (⋃ i, W i) : Set (ZariskiGL ι k)) = wordSet W a := by
  have : IsNoetherianRing (GLCoord k ι) := Algebra.FiniteType.isNoetherianRing k _
  set H := Subgroup.closure (⋃ i, W i) with hHdef
  have hHw := coe_closure_eq_iUnion_wordSet W
  rw [← hHdef] at hHw
  set P : List (I × ℤˣ) → Ideal (GLCoord k ι) := fun a => pointsIdeal (pt '' wordSet W a)
    with hP
  have hprime : ∀ a, (P a).IsPrime := fun a =>
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1
      (isDomainImage_wordSet W hW a).isPointIrreducible
  obtain ⟨_, ⟨a₀, rfl⟩, ha₀⟩ := (wellFounded_lt (α := ℕ∞)).has_min
    (Set.range fun a => (P a).height) ⟨_, ⟨[], rfl⟩⟩
  have hmin : ∀ b, P b ≤ P a₀ → P b = P a₀ := by
    intro b hb
    by_contra hne
    have := hprime b
    exact ha₀ _ ⟨b, rfl⟩ (Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hb hne))
  have hanti : ∀ {S T : Set (ZariskiGL ι k)}, S ⊆ T →
      pointsIdeal (pt '' T) ≤ pointsIdeal (pt '' S) :=
    fun hST _ ha => mem_pointsIdeal.2 fun y hy => mem_pointsIdeal.1 ha y (Set.image_mono hST hy)
  have hclos : ∀ b, pt '' wordSet W b ⊆ pointsZero k (P a₀) := by
    intro b
    have hsub₁ : wordSet W a₀ ⊆ wordSet W (b ++ a₀) := fun x hx => by
      rw [wordSet_append]
      exact ⟨1, one_mem_wordSet W h1 b, x, hx, one_mul x⟩
    have hsub₂ : wordSet W b ⊆ wordSet W (b ++ a₀) := fun x hx => by
      rw [wordSet_append]
      exact ⟨x, hx, 1, one_mem_wordSet W h1 a₀, mul_one x⟩
    have heq : P (b ++ a₀) = P a₀ := hmin _ (hanti hsub₁)
    calc pt '' wordSet W b ⊆ pt '' wordSet W (b ++ a₀) := Set.image_mono hsub₂
      _ ⊆ pointsZero k (P (b ++ a₀)) := subset_pointsZero_pointsIdeal _
      _ = pointsZero k (P a₀) := by rw [heq]
  have hIH : pointsIdeal (pt '' (H : Set (ZariskiGL ι k))) = P a₀ := by
    refine le_antisymm (hanti ?_) fun f hf => mem_pointsIdeal.2 ?_
    · rw [hHw]
      exact Set.subset_iUnion (wordSet W) a₀
    · rintro _ ⟨h, hh, rfl⟩
      rw [hHw] at hh
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hh
      exact hclos b ⟨h, hb, rfl⟩ f hf
  have hpts : subgroupPoints (H.map point.toMonoidHom) = pt '' (H : Set (ZariskiGL ι k)) :=
    subgroupPoints_map point H
  have hclH : closure (H : Set (ZariskiGL ι k)) ⊆ wordSet W (invWord a₀ ++ a₀) := by
    intro g hg
    rw [closure_eq_preimage_pointsZero isInducing_pt, Set.mem_preimage] at hg
    have hg' : pt g ∈ pointsZero k (subgroupIdeal (H.map point.toMonoidHom)) := by
      rw [subgroupIdeal, hpts]
      exact hg
    have hdom := isDomainImage_wordSet W hW a₀
    have hex := exists_inv_mul_of_pointsIdeal_eq (C := pt '' wordSet W a₀)
      (H.map point.toMonoidHom) (z := pt g)
      (IsDomainImage.isPointConstructible hdom) (IsDomainImage.isPointIrreducible hdom)
      (by rw [subgroupIdeal, hpts, hIH]) hg'
    obtain ⟨c, ⟨w, hw, rfl⟩, c', ⟨w', hw', rfl⟩, hzw⟩ := hex
    have hg_eq : g = w⁻¹ * w' := by
      apply point.injective
      rw [map_mul, map_inv]
      exact hzw
    rw [hg_eq, wordSet_invWord_append]
    exact Set.mul_mem_mul (Set.inv_mem_inv.2 hw) hw'
  have hword_le : wordSet W (invWord a₀ ++ a₀) ⊆ (H : Set (ZariskiGL ι k)) := by
    rw [hHw]
    exact Set.subset_iUnion (wordSet W) _
  have hHeq : (H : Set (ZariskiGL ι k)) = wordSet W (invWord a₀ ++ a₀) :=
    Set.Subset.antisymm (subset_closure.trans hclH) hword_le
  refine ⟨?_, ?_, invWord a₀ ++ a₀, hHeq⟩
  · exact closure_subset_iff_isClosed.1 (hclH.trans hword_le)
  · rw [hHeq]
    exact isIrreducible_of_isDomainImage (isDomainImage_wordSet W hW _)

end ZariskiGL

end CFSG.LieType.AlgebraicGroups.SeminaireExp3
