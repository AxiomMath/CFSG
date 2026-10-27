module

public import CFSG.LieType.Chevalley.SignKernelComponentBorel

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {τ : Tag} (K : Type) [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}

variable (χ J) in
@[expose] def unionRoots : Set (Fin τ.rank → ℤ) :=
  {α | ∃ h : α ∈ kernelRoots χ, (⟦⟨α, h⟩⟧ : KernelComponent χ) ∈ J}

variable (χ J) in
@[expose] def unionSimpleRoots : Set (Fin τ.rank → ℤ) :=
  {β | ∃ i ∈ J, β ∈ simpleRoots (componentRoots χ i)}

variable (χ J) in
@[expose] def unionWeylGroup
    : Subgroup (WeylGroup τ) :=
  Subgroup.closure (rootReflection '' unionSimpleRoots χ J)

theorem mem_unionRoots_iff {α : Fin τ.rank → ℤ} :
    α ∈ unionRoots χ J ↔ ∃ i ∈ J, α ∈ componentRoots χ i := by
  constructor
  · rintro ⟨h, hJ⟩
    exact ⟨_, hJ, h, rfl⟩
  · rintro ⟨i, hi, h, rfl⟩
    exact ⟨h, hi⟩

theorem componentRoots_subset_unionRoots {i : KernelComponent χ} (hi : i ∈ J) :
    componentRoots χ i ⊆ unionRoots χ J :=
  fun _ hα => mem_unionRoots_iff.2 ⟨i, hi, hα⟩

theorem isRoot_of_mem_unionRoots {α : Fin τ.rank → ℤ} (hα : α ∈ unionRoots χ J) : IsRoot τ α :=
  hα.1.1

theorem neg_mem_unionRoots
    {α : Fin τ.rank → ℤ} (hα : α ∈ unionRoots χ J) :
    -α ∈ unionRoots χ J := by
  obtain ⟨i, hi, h⟩ := mem_unionRoots_iff.1 hα
  exact componentRoots_subset_unionRoots hi ((isRootComponent_componentRoots i).neg_mem α h)

theorem mem_unionRoots_of_mem_unionSimpleRoots {β : Fin τ.rank → ℤ}
    (hβ : β ∈ unionSimpleRoots χ J) : β ∈ unionRoots χ J := by
  obtain ⟨i, hi, h⟩ := hβ
  exact componentRoots_subset_unionRoots hi (simpleRoots_subset h)

theorem isRoot_of_mem_unionSimpleRoots
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J) :
    IsRoot τ β :=
  isRoot_of_mem_unionRoots (mem_unionRoots_of_mem_unionSimpleRoots hβ)

theorem mem_posRoots_of_mem_unionSimpleRoots {β : Fin τ.rank → ℤ}
    (hβ : β ∈ unionSimpleRoots χ J) : β ∈ posRoots (unionRoots χ J) := by
  obtain ⟨i, hi, h⟩ := hβ
  exact ⟨componentRoots_subset_unionRoots hi (simpleRoots_subset h), simpleRoots_height_pos h⟩

theorem eq_of_mem_componentRoots {i j : KernelComponent χ} {α : Fin τ.rank → ℤ}
    (hi : α ∈ componentRoots χ i) (hj : α ∈ componentRoots χ j) : i = j := by
  obtain ⟨h, rfl⟩ := hi
  obtain ⟨h', rfl⟩ := hj
  rfl

theorem iform_eq_zero_of_mem_componentRoots {i j : KernelComponent χ} (hij : i ≠ j)
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (hβ : β ∈ componentRoots χ j) :
    iform α β = 0 := by
  obtain ⟨hα', rfl⟩ := hα
  obtain ⟨hβ', rfl⟩ := hβ
  exact iform_eq_zero_of_mk_ne hij

theorem rootReflection_smul_eq_of_ne
    {i j : KernelComponent χ} (hij : i ≠ j)
    {β α : Fin τ.rank → ℤ} (hβ : β ∈ componentRoots χ i) (hα : α ∈ componentRoots χ j) :
    rootReflection β • α = α :=
  rootReflection_smul_of_iform_eq_zero (isRoot_of_mem_componentRoots hβ)
    (iform_eq_zero_of_mem_componentRoots hij hβ hα)

theorem rootReflection_smul_mem_unionRoots
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ unionSimpleRoots χ J) {α : Fin τ.rank → ℤ} (hα : α ∈ unionRoots χ J) :
    rootReflection β • α ∈ unionRoots χ J := by
  obtain ⟨i, hi, hβi⟩ := hβ
  obtain ⟨j, -, hαj⟩ := mem_unionRoots_iff.1 hα
  by_cases hij : i = j
  · subst hij
    exact componentRoots_subset_unionRoots hi
      ((isRootComponent_componentRoots i).reflection_mem α hαj β (simpleRoots_subset hβi))
  · rw [rootReflection_smul_eq_of_ne hij (simpleRoots_subset hβi) hαj]
    exact hα

theorem smul_mem_unionRoots_iff
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    (α : Fin τ.rank → ℤ) : w • α ∈ unionRoots χ J ↔ α ∈ unionRoots χ J := by
  induction hw using Subgroup.closure_induction generalizing α with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    refine ⟨fun h => ?_, rootReflection_smul_mem_unionRoots hβ⟩
    have h' := rootReflection_smul_mem_unionRoots hβ h
    rwa [smul_smul, rootReflection_mul_self (isRoot_of_mem_unionSimpleRoots hβ),
      one_smul] at h'
  | one => rw [one_smul]
  | mul x y _ _ hx hy => rw [mul_smul, hx, hy]
  | inv x _ hx => rw [← hx, smul_inv_smul]

theorem smul_mem_unionRoots
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    {α : Fin τ.rank → ℤ} (hα : α ∈ unionRoots χ J) : w • α ∈ unionRoots χ J :=
  (smul_mem_unionRoots_iff hw α).2 hα

theorem mem_posRoots_or_mem_negRoots_unionRoots
    {α : Fin τ.rank → ℤ}
    (hα : α ∈ unionRoots χ J) :
    α ∈ posRoots (unionRoots χ J) ∨ α ∈ negRoots (unionRoots χ J) := by
  rcases IsRoot.height_pos_or_neg (isRoot_of_mem_unionRoots hα) with h | h
  · exact Or.inl ⟨hα, h⟩
  · exact Or.inr ⟨neg_mem_unionRoots hα, by rw [height_neg]; omega⟩

theorem nsmul_add_mem_posRoots_unionRoots
    {α β : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (unionRoots χ J)) (hβ : β ∈ posRoots (unionRoots χ J)) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ posRoots (unionRoots χ J) := by
  obtain ⟨i, hi, hαi⟩ := mem_unionRoots_iff.1 hα.1
  obtain ⟨j, -, hβj⟩ := mem_unionRoots_iff.1 hβ.1
  by_cases hij : i = j
  · subst hij
    have h := mem_posRoots_of_nsmul_add ⟨hαi, hα.2⟩ ⟨hβj, hβ.2⟩ a b ha hb hr
    exact ⟨componentRoots_subset_unionRoots hi h.1, h.2⟩
  · exfalso
    obtain ⟨hα', rfl⟩ := hαi
    obtain ⟨hβ', rfl⟩ := hβj
    exact not_isRoot_of_mk_ne hij (by omega) (by omega) hr

theorem rootReflection_smul_mem_posRoots_unionRoots
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ unionSimpleRoots χ J) {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (unionRoots χ J)) (hne : α ≠ β) :
    rootReflection β • α ∈ posRoots (unionRoots χ J) := by
  obtain ⟨i, hi, hβi⟩ := hβ
  obtain ⟨j, -, hαj⟩ := mem_unionRoots_iff.1 hα.1
  by_cases hij : i = j
  · subst hij
    have h := (rootReflection_mem_posRoots (isRootComponent_componentRoots i) hβi
      ⟨hαj, hα.2⟩ hne).1
    exact ⟨componentRoots_subset_unionRoots hi h.1, h.2⟩
  · rw [rootReflection_smul_eq_of_ne hij (simpleRoots_subset hβi) hαj]
    exact hα

theorem componentWeylGroup_le_unionWeylGroup
    {i : KernelComponent χ} (hi : i ∈ J) :
    componentWeylGroup (componentRoots χ i) ≤ unionWeylGroup χ J :=
  Subgroup.closure_mono (Set.image_mono fun _ hβ => ⟨i, hi, hβ⟩)

theorem rootReflection_mem_unionWeylGroup
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ unionSimpleRoots χ J) : rootReflection β ∈ unionWeylGroup χ J :=
  Subgroup.subset_closure ⟨β, hβ, rfl⟩

theorem exists_smul_unionSimpleRoot
    {α : Fin τ.rank → ℤ} (hα : α ∈ unionRoots χ J) :
    ∃ u ∈ unionWeylGroup χ J, ∃ β ∈ unionSimpleRoots χ J, α = u • β := by
  obtain ⟨i, hi, hαi⟩ := mem_unionRoots_iff.1 hα
  obtain ⟨u, hu, β, hβ, e⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i) hαi
  exact ⟨u, componentWeylGroup_le_unionWeylGroup hi hu, β, ⟨i, hi, hβ⟩, e⟩

theorem smul_sub_mem_span_unionRoots
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    (v : Fin τ.rank → ℤ) : w • v - v ∈ Submodule.span ℤ (unionRoots χ J) := by
  have hpres : ∀ x ∈ unionWeylGroup χ J, ∀ s ∈ Submodule.span ℤ (unionRoots χ J),
      x • s ∈ Submodule.span ℤ (unionRoots χ J) := by
    intro x hx s hs
    induction hs using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (smul_mem_unionRoots hx hy)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy
  induction hw using Subgroup.closure_induction generalizing v with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    rw [rootReflection_smul (isRoot_of_mem_unionSimpleRoots hβ), sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _
      (Submodule.subset_span (mem_unionRoots_of_mem_unionSimpleRoots hβ)))
  | one => rw [one_smul, sub_self]; exact Submodule.zero_mem _
  | mul x y hx _ ihx ihy =>
    have e : (x * y) • v - v = x • (y • v - v) + (x • v - v) := by
      rw [smul_sub, mul_smul]
      abel
    rw [e]
    exact Submodule.add_mem _ (hpres x hx _ (ihy v)) (ihx v)
  | inv x hx ihx =>
    have e : x⁻¹ • v - v = -(x⁻¹ • (x • v - v)) := by
      rw [smul_sub, inv_smul_smul]
      abel
    rw [e]
    exact Submodule.neg_mem _ (hpres x⁻¹ (inv_mem hx) _ (ihx v))

theorem eq_one_of_forall_smul_eq
    {u : WeylGroup τ} (hu : u ∈ unionWeylGroup χ J)
    (h : ∀ α ∈ unionRoots χ J, u • α = α) : u = 1 := by
  have hfix : ∀ s ∈ Submodule.span ℤ (unionRoots χ J), u • s = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact smul_zero u
    | add x y _ _ hx hy => rw [smul_add, hx, hy]
    | smul c x _ hx => rw [smul_comm, hx]
  have hpow : ∀ (v : Fin τ.rank → ℤ) (m : ℕ), u ^ m • v = v + m • (u • v - v) := by
    intro v m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', mul_smul, ih, smul_add, smul_comm u m,
        hfix _ (smul_sub_mem_span_unionRoots hu v), succ_nsmul]
      abel
  refine eq_of_smul_eq_smul (α := Fin τ.rank → ℤ) fun v => ?_
  rw [one_smul]
  have hv := hpow v (orderOf u)
  rw [pow_orderOf_eq_one, one_smul, left_eq_add] at hv
  have hd := (smul_eq_zero.1 hv).resolve_left (orderOf_pos u).ne'
  exact sub_eq_zero.1 hd

section Groups

variable (χ J) in
@[expose] def unionRootSpan
    : Subgroup (ModGL τ K) :=
  rootSpan τ K (unionRoots χ J)

variable (χ J) in
@[expose] def unionTorus
    : Subgroup (ModGL τ K) :=
  unionRootSpan K χ J ⊓ torusGroup τ K

variable (χ J) in
@[expose] def unionUnipotent
    : Subgroup (ModGL τ K) :=
  rootSpan τ K (posRoots (unionRoots χ J))

variable (χ J) in
@[expose] def unionBorel
    : Subgroup (ModGL τ K) :=
  unionTorus K χ J ⊔ unionUnipotent K χ J

variable (χ J) in
@[expose] def unionMonomial
    (n : (Fin τ.rank → ℤ) → ModGL τ K) : Subgroup (ModGL τ K) :=
  Subgroup.closure ((unionTorus K χ J : Set (ModGL τ K)) ∪ n '' unionSimpleRoots χ J)

variable (χ J) in
@[expose] def unionLifts
    (n : (Fin τ.rank → ℤ) → ModGL τ K) (w : WeylGroup τ) :
    Set (ModGL τ K) :=
  {g | g ∈ unionMonomial K χ J n ∧ MapsRootLines g w}

variable (χ J) in
@[expose] def unionCell
    (n : (Fin τ.rank → ℤ) → ModGL τ K) (w : WeylGroup τ) :
    Set (ModGL τ K) :=
  (unionBorel K χ J : Set (ModGL τ K)) * unionLifts K χ J n w *
    (unionBorel K χ J : Set (ModGL τ K))

variable (χ J) in
@[expose] def unionInversionRoots
    (w : WeylGroup τ) : Set (Fin τ.rank → ℤ) :=
  {α | α ∈ posRoots (unionRoots χ J) ∧ height (w • α) < 0}

variable {K}

theorem unionTorus_le_torusGroup
    : unionTorus K χ J ≤ torusGroup τ K :=
  inf_le_right

theorem unionTorus_le_unionRootSpan
    : unionTorus K χ J ≤ unionRootSpan K χ J :=
  inf_le_left

theorem isRoot_height_pos_of_mem_posRoots_unionRoots {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (unionRoots χ J)) : IsRoot τ α ∧ 0 < height α :=
  ⟨isRoot_of_mem_unionRoots hα.1, hα.2⟩

theorem unionUnipotent_le_posUnipotent
    : unionUnipotent K χ J ≤ posUnipotent τ K :=
  rootSpan_le_posUnipotent fun _ hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα

theorem unionUnipotent_le_unionRootSpan
    : unionUnipotent K χ J ≤ unionRootSpan K χ J :=
  rootSpan_mono fun _ hα => hα.1

theorem rootSubgroup_le_unionRootSpan
    {α : Fin τ.rank → ℤ} (hα : α ∈ unionRoots χ J) :
    rootSubgroup τ K α ≤ unionRootSpan K χ J :=
  le_iSup₂_of_le α hα le_rfl

theorem mul_comm_of_mem_unionTorus
    {x y : ModGL τ K} (hx : x ∈ unionTorus K χ J)
    (hy : y ∈ unionTorus K χ J) : x * y = y * x :=
  (triangular_borel_structure.{0, 0} τ K).1 x (unionTorus_le_torusGroup hx) y
    (unionTorus_le_torusGroup hy)

theorem unionTorus_le_normalizer :
    unionTorus K χ J ≤ Subgroup.normalizer (unionUnipotent K χ J : Set (ModGL τ K)) :=
  unionTorus_le_torusGroup.trans (torusGroup_le_normalizer_rootSpan fun _ hα =>
    (isRoot_height_pos_of_mem_posRoots_unionRoots hα).1)

theorem unionTorus_inf_unionUnipotent
    : unionTorus K χ J ⊓ unionUnipotent K χ J = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  have h : g ∈ torusGroup τ K ⊓ posUnipotent τ K := Subgroup.mem_inf.2
    ⟨unionTorus_le_torusGroup h1, unionUnipotent_le_posUnipotent h2⟩
  rwa [(triangular_borel_structure.{0, 0} τ K).2.2.2.1] at h

theorem coe_unionBorel :
    (unionBorel K χ J : Set (ModGL τ K)) =
      (unionTorus K χ J : Set (ModGL τ K)) * (unionUnipotent K χ J : Set (ModGL τ K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ unionTorus_le_normalizer

theorem eq_and_eq_of_mul_eq_mul
    {t t' u u' : ModGL τ K} (ht : t ∈ unionTorus K χ J)
    (ht' : t' ∈ unionTorus K χ J) (hu : u ∈ unionUnipotent K χ J)
    (hu' : u' ∈ unionUnipotent K χ J) (h : t * u = t' * u') : t = t' ∧ u = u' := by
  have h1 : t'⁻¹ * t = u' * u⁻¹ := by
    calc t'⁻¹ * t = t'⁻¹ * (t * u) * u⁻¹ := by group
      _ = t'⁻¹ * (t' * u') * u⁻¹ := by rw [h]
      _ = u' * u⁻¹ := by group
  have hT : t'⁻¹ * t ∈ unionTorus K χ J := mul_mem (inv_mem ht') ht
  have hU : t'⁻¹ * t ∈ unionUnipotent K χ J := by
    rw [h1]
    exact mul_mem hu' (inv_mem hu)
  have h2 : t'⁻¹ * t = 1 := by
    have h3 := Subgroup.mem_inf.2 ⟨hT, hU⟩
    rwa [unionTorus_inf_unionUnipotent, Subgroup.mem_bot] at h3
  have htt : t = t' := (inv_mul_eq_one.1 h2).symm
  subst htt
  exact ⟨rfl, mul_left_cancel h⟩

theorem unionTorus_le_unionBorel
    : unionTorus K χ J ≤ unionBorel K χ J :=
  le_sup_left

theorem unionUnipotent_le_unionBorel
    : unionUnipotent K χ J ≤ unionBorel K χ J :=
  le_sup_right

theorem unionBorel_le_borelGroup
    : unionBorel K χ J ≤ borelGroup τ K :=
  sup_le (unionTorus_le_torusGroup.trans torusGroup_le_borelGroup)
    (unionUnipotent_le_posUnipotent.trans le_sup_right)

theorem unionBorel_le_unionRootSpan
    : unionBorel K χ J ≤ unionRootSpan K χ J :=
  sup_le unionTorus_le_unionRootSpan unionUnipotent_le_unionRootSpan

theorem isNilpotent_unionUnipotent
    : Group.IsNilpotent (unionUnipotent K χ J) := by
  have := (positive_root_height_series τ K).2.2.2.2.1
  refine Subgroup.isNilpotent_of_ker_le_center
    (Subgroup.inclusion (unionUnipotent_le_posUnipotent (K := K) (χ := χ) (J := J))) ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (Subgroup.inclusion_injective _)]
  exact bot_le

variable {n : (Fin τ.rank → ℤ) → ModGL τ K}

theorem unionTorus_le_unionMonomial
    : unionTorus K χ J ≤ unionMonomial K χ J n :=
  fun _ ht => Subgroup.subset_closure (Or.inl ht)

theorem lift_mem_unionMonomial
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J) :
    n β ∈ unionMonomial K χ J n :=
  Subgroup.subset_closure (Or.inr ⟨β, hβ, rfl⟩)

theorem mem_unionLifts
    {w : WeylGroup τ} {g : ModGL τ K} :
    g ∈ unionLifts K χ J n w ↔ g ∈ unionMonomial K χ J n ∧ MapsRootLines g w :=
  Iff.rfl

theorem mul_mem_unionLifts
    {w w' : WeylGroup τ} {g g' : ModGL τ K}
    (hg : g ∈ unionLifts K χ J n w) (hg' : g' ∈ unionLifts K χ J n w') :
    g * g' ∈ unionLifts K χ J n (w * w') :=
  ⟨mul_mem hg.1 hg'.1, hg.2.mul hg'.2⟩

theorem inv_mem_unionLifts
    {w : WeylGroup τ} {g : ModGL τ K} (hg : g ∈ unionLifts K χ J n w) :
    g⁻¹ ∈ unionLifts K χ J n w⁻¹ :=
  ⟨inv_mem hg.1, hg.2.inv⟩

theorem one_mem_unionLifts
    : (1 : ModGL τ K) ∈ unionLifts K χ J n 1 :=
  ⟨one_mem _, mapsRootLines_one⟩

variable
    (hn : ∀ β ∈ unionSimpleRoots χ J, n β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
  n β ∈ monomialSubgroup τ K ∧ MapsRootLines (n β) (rootReflection β))
include hn

theorem lift_mem_unionRootSpan
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J) :
    n β ∈ unionRootSpan K χ J :=
  sup_le (rootSubgroup_le_unionRootSpan (mem_unionRoots_of_mem_unionSimpleRoots hβ))
    (rootSubgroup_le_unionRootSpan (neg_mem_unionRoots (mem_unionRoots_of_mem_unionSimpleRoots hβ)))
    (hn β hβ).1

theorem unionMonomial_le_unionRootSpan
    : unionMonomial K χ J n ≤ unionRootSpan K χ J :=
  (Subgroup.closure_le _).2 (Set.union_subset (fun _ ht => unionTorus_le_unionRootSpan ht) (by
    rintro _ ⟨β, hβ, rfl⟩
    exact lift_mem_unionRootSpan hn hβ))

theorem unionMonomial_le_monomialSubgroup :
    unionMonomial K χ J n ≤ monomialSubgroup τ K :=
  (Subgroup.closure_le _).2 (Set.union_subset
    (fun _ ht => torusGroup_le_monomialSubgroup (unionTorus_le_torusGroup ht)) (by
      rintro _ ⟨β, hβ, rfl⟩
      exact (hn β hβ).2.1))

theorem exists_mapsRootLines_of_mem_unionMonomial
    {g : ModGL τ K}
    (hg : g ∈ unionMonomial K χ J n) : ∃ w ∈ unionWeylGroup χ J, MapsRootLines g w := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨β, hβ, rfl⟩
    · exact ⟨1, one_mem _, mapsRootLines_of_mem_torusGroup (unionTorus_le_torusGroup hx)⟩
    · exact ⟨_, rootReflection_mem_unionWeylGroup hβ, (hn β hβ).2.2⟩
  | one => exact ⟨1, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, hw, h⟩ := hx
    obtain ⟨w', hw', h'⟩ := hy
    exact ⟨w * w', mul_mem hw hw', h.mul h'⟩
  | inv x _ hx =>
    obtain ⟨w, hw, h⟩ := hx
    exact ⟨w⁻¹, inv_mem hw, h.inv⟩

theorem exists_mem_unionLifts
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J) :
    ∃ g, g ∈ unionLifts K χ J n w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact ⟨n β, lift_mem_unionMonomial hβ, (hn β hβ).2.2⟩
  | one => exact ⟨1, one_mem_unionLifts⟩
  | mul x y _ _ hx hy =>
    obtain ⟨g, hg⟩ := hx
    obtain ⟨g', hg'⟩ := hy
    exact ⟨g * g', mul_mem_unionLifts hg hg'⟩
  | inv x _ hx =>
    obtain ⟨g, hg⟩ := hx
    exact ⟨g⁻¹, inv_mem_unionLifts hg⟩

theorem mem_unionTorus_of_mapsRootLines_one
    {g : ModGL τ K} (hg : g ∈ unionMonomial K χ J n)
    (h1 : MapsRootLines g 1) : g ∈ unionTorus K χ J :=
  Subgroup.mem_inf.2 ⟨unionMonomial_le_unionRootSpan hn hg,
    mem_torusGroup_of_mapsRootLines_one (unionMonomial_le_monomialSubgroup hn hg) h1⟩

theorem conj_mem_unionTorus
    {g : ModGL τ K} (hg : g ∈ unionMonomial K χ J n) {t : ModGL τ K}
    (ht : t ∈ unionTorus K χ J) : g * t * g⁻¹ ∈ unionTorus K χ J := by
  obtain ⟨w, hw⟩ := exists_mapsRootLines_of_mem (unionMonomial_le_monomialSubgroup hn hg)
  refine mem_unionTorus_of_mapsRootLines_one hn
    (mul_mem (mul_mem hg (unionTorus_le_unionMonomial ht)) (inv_mem hg)) ?_
  simpa using (hw.mul (mapsRootLines_of_mem_torusGroup (unionTorus_le_torusGroup ht))).mul hw.inv

theorem inv_mul_mem_unionTorus
    {w : WeylGroup τ} {g g' : ModGL τ K}
    (hg : g ∈ unionLifts K χ J n w) (hg' : g' ∈ unionLifts K χ J n w) :
    g⁻¹ * g' ∈ unionTorus K χ J :=
  mem_unionTorus_of_mapsRootLines_one hn (mul_mem (inv_mem hg.1) hg'.1)
    (by simpa using hg.2.inv.mul hg'.2)

theorem lift_mem_unionLifts
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J) :
    n β ∈ unionLifts K χ J n (rootReflection β) :=
  ⟨lift_mem_unionMonomial hβ, (hn β hβ).2.2⟩

theorem lift_mul_self_mem_unionTorus
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J) :
    n β * n β ∈ unionTorus K χ J := by
  have h2 := (hn β hβ).2.2.mul (hn β hβ).2.2
  rw [rootReflection_mul_self (isRoot_of_mem_unionSimpleRoots hβ)] at h2
  exact mem_unionTorus_of_mapsRootLines_one hn
    (mul_mem (lift_mem_unionMonomial hβ) (lift_mem_unionMonomial hβ)) h2

omit hn in
theorem list_prod_mul_mem_unionLifts
    {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, β ∈ unionSimpleRoots χ J) {t : ModGL τ K} (ht : t ∈ unionTorus K χ J)
    {w : WeylGroup τ} (h : MapsRootLines ((l.map n).prod * t) w) :
    (l.map n).prod * t ∈ unionLifts K χ J n w := by
  refine ⟨mul_mem (Subgroup.list_prod_mem _ fun x hx => ?_) (unionTorus_le_unionMonomial ht), h⟩
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
  exact lift_mem_unionMonomial (hl β hβ)

end Groups

section Moves

variable
    {K} {n : (Fin τ.rank → ℤ) → ModGL τ K}
  (hn : ∀ β ∈ unionSimpleRoots χ J, n β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
    n β ∈ monomialSubgroup τ K ∧ MapsRootLines (n β) (rootReflection β))

variable (τ) in
theorem exists_rootWeylChoice
    : ∃ (v : (Fin τ.rank → ℤ) → WeylGroup τ)
    (j : (Fin τ.rank → ℤ) → Fin τ.rank),
      ∀ β, IsRoot τ β → v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β := by
  have h : ∀ β : Fin τ.rank → ℤ, ∃ (w : WeylGroup τ) (k : Fin τ.rank),
      IsRoot τ β → w • (Pi.single k 1 : Fin τ.rank → ℤ) = β := fun β => by
    by_cases hβ : IsRoot τ β
    · obtain ⟨w, k, h⟩ := isRoot_iff_exists_smul_single.1 hβ
      exact ⟨w, k, fun _ => h⟩
    · exact ⟨1, ⟨0, τ.rank_pos⟩, fun h => absurd h hβ⟩
  choose v j hvj using h
  exact ⟨v, j, hvj⟩

theorem componentRootSpan_le_unionRootSpan
    {i : KernelComponent χ} (hi : i ∈ J) :
    componentRootSpan K χ i ≤ unionRootSpan K χ J :=
  rootSpan_mono (componentRoots_subset_unionRoots hi)

theorem posRoots_componentRoots_subset {i : KernelComponent χ} (hi : i ∈ J) :
    posRoots (componentRoots χ i) ⊆ posRoots (unionRoots χ J) :=
  fun _ hα => ⟨componentRoots_subset_unionRoots hi hα.1, hα.2⟩

theorem componentBorel_le_unionBorel
    {i : KernelComponent χ} (hi : i ∈ J) :
    componentBorel K χ i ≤ unionBorel K χ J :=
  sup_le ((inf_le_inf_right _ (componentRootSpan_le_unionRootSpan hi)).trans
      unionTorus_le_unionBorel)
    ((rootSpan_mono (posRoots_componentRoots_subset hi)).trans unionUnipotent_le_unionBorel)

include hn in
theorem lift_mul_inv_componentWeylElt_mem
    {v : (Fin τ.rank → ℤ) → WeylGroup τ}
    {j : (Fin τ.rank → ℤ) → Fin τ.rank} {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J)
    (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) :
    n β * (componentWeylElt K v j β)⁻¹ ∈ unionTorus K χ J := by
  obtain ⟨i, hi, hβi⟩ := hβ
  have hS : n β * (componentWeylElt K v j β)⁻¹ ∈ unionRootSpan K χ J :=
    mul_mem (lift_mem_unionRootSpan hn ⟨i, hi, hβi⟩) (inv_mem (componentRootSpan_le_unionRootSpan hi
      (componentWeylElt_mem_componentRootSpan hβv (simpleRoots_subset hβi))))
  have hM : n β * (componentWeylElt K v j β)⁻¹ ∈ monomialSubgroup τ K :=
    mul_mem (hn β ⟨i, hi, hβi⟩).2.1 (inv_mem (componentWeylElt_mem_monomialSubgroup K v j β))
  have h1 := (hn β ⟨i, hi, hβi⟩).2.2.mul (mapsRootLines_componentWeylElt (K := K) hβv).inv
  rw [mul_inv_cancel] at h1
  exact Subgroup.mem_inf.2 ⟨hS, mem_torusGroup_of_mapsRootLines_one hM h1⟩

include hn in
theorem exists_mul_eq_mul_of_mem_unionLifts
    {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ unionLifts K χ J n w) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : w⁻¹ • α ∈ posRoots (unionRoots χ J)) {x : ModGL τ K}
    (hx : x ∈ rootSpan τ K {α}) : ∃ b ∈ unionBorel K χ J, x * g = g * b := by
  have hgM := unionMonomial_le_monomialSubgroup hn hg.1
  have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem hgM) hg.2.inv (S := {α})
    (by rintro _ rfl; exact hα) hx
  rw [Set.image_singleton, inv_inv] at h
  exact ⟨g⁻¹ * x * g, unionUnipotent_le_unionBorel
    (rootSpan_mono (Set.singleton_subset_iff.2 hpos) h), by group⟩

include hn in
theorem exists_lift_mul_eq
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J)
    {b : ModGL τ K} (hb : b ∈ unionBorel K χ J) :
    ∃ b' ∈ unionBorel K χ J, ∃ x ∈ rootSpan τ K {β}, n β * b = b' * (n β * x) := by
  rw [← SetLike.mem_coe, coe_unionBorel] at hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb
  have hβpos := mem_posRoots_of_mem_unionSimpleRoots hβ
  set S₁ := posRoots (unionRoots χ J) \ {β}
  have hsplit : posRoots (unionRoots χ J) = S₁ ∪ {β} :=
    (Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 hβpos)).symm
  have hu' : u ∈ rootSpan τ K (S₁ ∪ {β}) := by
    rw [← hsplit]
    exact hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_rootSpan_eq K (S₁ := S₁) (S₂ := {β})
    (fun α hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα.1)
    (fun α hα => by
      rw [Set.mem_singleton_iff.1 hα]
      exact isRoot_height_pos_of_mem_posRoots_unionRoots hβpos)
    Set.disjoint_sdiff_left
    (fun α hα γ hγ a a' ha ha' hr => by
      rw [← hsplit] at hα hγ ⊢
      exact nsmul_add_mem_posRoots_unionRoots hα hγ a a' ha ha' hr) hu'
  have hnt : n β * t * (n β)⁻¹ ∈ unionTorus K χ J :=
    conj_mem_unionTorus hn (lift_mem_unionMonomial hβ) ht
  have hnu : n β * u₁ * (n β)⁻¹ ∈ unionUnipotent K χ J := by
    have h := conj_mem_rootSpan_of_mapsRootLines (hn β hβ).2.1 (hn β hβ).2.2 (S := S₁)
      (fun α hα => (isRoot_height_pos_of_mem_posRoots_unionRoots hα.1).1) hu₁
    refine rootSpan_mono ?_ h
    rintro _ ⟨α, ⟨hα, hne⟩, rfl⟩
    exact rootReflection_smul_mem_posRoots_unionRoots hβ hα hne
  refine ⟨n β * t * (n β)⁻¹ * (n β * u₁ * (n β)⁻¹),
    mul_mem (unionTorus_le_unionBorel hnt) (unionUnipotent_le_unionBorel hnu), u₂, hu₂, ?_⟩
  group

include hn in
theorem exists_lift_mul_eq_of_ne_one
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J)
    {x : ModGL τ K} (hx : x ∈ rootSpan τ K {β}) (hx1 : x ≠ 1) :
    ∃ b₀ ∈ unionBorel K χ J, ∃ y ∈ rootSpan τ K {-β}, n β * x = b₀ * y := by
  obtain ⟨v, j, hvj⟩ := exists_rootWeylChoice τ
  obtain ⟨i, hi, hβi⟩ := hβ
  have hvji : ∀ γ ∈ simpleRoots (componentRoots χ i),
      v γ • (Pi.single (j γ) 1 : Fin τ.rank → ℤ) = γ := fun γ hγ => hvj γ (simpleRoots_isRoot hγ)
  obtain ⟨c, rfl⟩ := exists_componentXElt_eq (hvji β hβi) hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (componentXElt_zero β)
  obtain ⟨b₀, hb₀, h₀⟩ := exists_componentWeylElt_mul_componentXElt_eq hvji hβi hc
  have ht := lift_mul_inv_componentWeylElt_mem hn ⟨i, hi, hβi⟩ (hvji β hβi)
  refine ⟨n β * (componentWeylElt K v j β)⁻¹ * b₀,
    mul_mem (unionTorus_le_unionBorel ht) (componentBorel_le_unionBorel hi hb₀),
    componentYElt K v j β c⁻¹, componentYElt_mem (hvji β hβi) c⁻¹, ?_⟩
  calc n β * componentXElt K v j β c = n β * (componentWeylElt K v j β)⁻¹ *
        (componentWeylElt K v j β * componentXElt K v j β c) := by group
    _ = _ := by rw [h₀]; group

end Moves

section Cells

variable {K} {n : (Fin τ.rank → ℤ) → ModGL τ K}

theorem mem_unionCell
    {w : WeylGroup τ} {x : ModGL τ K} :
    x ∈ unionCell K χ J n w ↔ ∃ b ∈ unionBorel K χ J,
      ∃ g ∈ unionLifts K χ J n w, ∃ b' ∈ unionBorel K χ J, b * g * b' = x := by
  simp only [unionCell, Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, g, hg, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, g, hg, b', hb', rfl⟩
  · rintro ⟨b, hb, g, hg, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, g, hg, rfl⟩, b', hb', rfl⟩

theorem mem_unionCell_of_mem_unionLifts
    {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ unionLifts K χ J n w) : g ∈ unionCell K χ J n w :=
  mem_unionCell.2 ⟨1, one_mem _, g, hg, 1, one_mem _, by group⟩

theorem borel_mul_mem_unionCell
    {w : WeylGroup τ} {b x : ModGL τ K}
    (hb : b ∈ unionBorel K χ J) (hx : x ∈ unionCell K χ J n w) :
    b * x ∈ unionCell K χ J n w := by
  obtain ⟨b₁, hb₁, g, hg, b₂, hb₂, rfl⟩ := mem_unionCell.1 hx
  exact mem_unionCell.2 ⟨b * b₁, mul_mem hb hb₁, g, hg, b₂, hb₂, by group⟩

variable
    (hn : ∀ β ∈ unionSimpleRoots χ J, n β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
  n β ∈ monomialSubgroup τ K ∧ MapsRootLines (n β) (rootReflection β))
include hn

theorem unionCell_subset_bruhatCell
    (w : WeylGroup τ) :
    unionCell K χ J n w ⊆ bruhatCell τ K w := by
  intro x hx
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_unionCell.1 hx
  obtain ⟨w', k, hk, rfl⟩ :=
    monomialSubgroup_le_torusWeylCosets (unionMonomial_le_monomialSubgroup hn hg.1)
  have hmaps : MapsRootLines (k * canonicalRep (coxeterSystem τ) K w') w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
  rw [← hmaps.unique hg.2]
  exact mem_bruhatCell.2 ⟨b * k, mul_mem (unionBorel_le_borelGroup hb)
    (torusGroup_le_borelGroup hk), b', unionBorel_le_borelGroup hb', by group⟩

theorem disjoint_unionCell
    {w w' : WeylGroup τ} (h : w ≠ w') :
    Disjoint (unionCell K χ J n w) (unionCell K χ J n w') :=
  (disjoint_bruhatCell h).mono (unionCell_subset_bruhatCell hn w)
    (unionCell_subset_bruhatCell hn w')

theorem doubleCoset_eq_unionCell
    {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ unionLifts K χ J n w) :
    (unionBorel K χ J : Set (ModGL τ K)) * {g} * (unionBorel K χ J : Set (ModGL τ K)) =
      unionCell K χ J n w := by
  ext x
  rw [mem_unionCell]
  constructor
  · intro hx
    obtain ⟨b, hb, b', hb', e⟩ := DoubleCoset.mem_doubleCoset.1 hx
    exact ⟨b, hb, g, hg, b', hb', e.symm⟩
  · rintro ⟨b, hb, g', hg', b', hb', rfl⟩
    have ht := inv_mul_mem_unionTorus hn hg hg'
    exact DoubleCoset.mem_doubleCoset.2 ⟨b, hb, g⁻¹ * g' * b',
      mul_mem (unionTorus_le_unionBorel ht) hb', by group⟩

theorem unionCell_subset_unionRootSpan
    (w : WeylGroup τ) :
    unionCell K χ J n w ⊆ unionRootSpan K χ J := by
  intro x hx
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_unionCell.1 hx
  exact mul_mem (mul_mem (unionBorel_le_unionRootSpan hb)
    (unionMonomial_le_unionRootSpan hn hg.1)) (unionBorel_le_unionRootSpan hb')

theorem lift_mul_mem_unionCell_of_pos
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J)
    {w : WeylGroup τ} (hpos : w⁻¹ • β ∈ posRoots (unionRoots χ J)) {x : ModGL τ K}
    (hx : x ∈ unionCell K χ J n w) : n β * x ∈ unionCell K χ J n (rootReflection β * w) := by
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_unionCell.1 hx
  obtain ⟨b'', hb'', y, hy, hc⟩ := exists_lift_mul_eq hn hβ hb
  obtain ⟨b₁, hb₁, h₁⟩ := exists_mul_eq_mul_of_mem_unionLifts hn hg
    (isRoot_of_mem_unionSimpleRoots hβ) hpos hy
  refine mem_unionCell.2 ⟨b'', hb'', _, mul_mem_unionLifts (lift_mem_unionLifts hn hβ) hg,
    b₁ * b', mul_mem hb₁ hb', ?_⟩
  calc b'' * (n β * g) * (b₁ * b') = b'' * n β * (g * b₁) * b' := by group
    _ = b'' * n β * (y * g) * b' := by rw [← h₁]
    _ = b'' * (n β * y) * g * b' := by group
    _ = n β * b * g * b' := by rw [← hc]
    _ = n β * (b * g * b') := by group

theorem lift_mul_mem_unionCell_of_neg
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J)
    {w : WeylGroup τ} (hneg : w⁻¹ • (-β) ∈ posRoots (unionRoots χ J)) {x : ModGL τ K}
    (hx : x ∈ unionCell K χ J n w) :
    n β * x ∈ unionCell K χ J n (rootReflection β * w) ∨ n β * x ∈ unionCell K χ J n w := by
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_unionCell.1 hx
  obtain ⟨b'', hb'', y, hy, hc⟩ := exists_lift_mul_eq hn hβ hb
  by_cases hy1 : y = 1
  · left
    rw [hy1, mul_one] at hc
    refine mem_unionCell.2 ⟨b'', hb'', _, mul_mem_unionLifts (lift_mem_unionLifts hn hβ) hg, b',
      hb', ?_⟩
    calc b'' * (n β * g) * b' = b'' * n β * g * b' := by group
      _ = n β * b * g * b' := by rw [← hc]
      _ = n β * (b * g * b') := by group
  · right
    obtain ⟨b₀, hb₀, z, hz, h₀⟩ := exists_lift_mul_eq_of_ne_one hn hβ hy hy1
    obtain ⟨b₂, hb₂, h₂⟩ := exists_mul_eq_mul_of_mem_unionLifts hn hg
      (IsRoot.neg (isRoot_of_mem_unionSimpleRoots hβ)) hneg hz
    refine mem_unionCell.2 ⟨b'' * b₀, mul_mem hb'' hb₀, g, hg, b₂ * b', mul_mem hb₂ hb', ?_⟩
    calc b'' * b₀ * g * (b₂ * b') = b'' * b₀ * (g * b₂) * b' := by group
      _ = b'' * b₀ * (z * g) * b' := by rw [← h₂]
      _ = b'' * (b₀ * z) * g * b' := by group
      _ = b'' * (n β * y) * g * b' := by rw [← h₀]
      _ = n β * b * g * b' := by rw [← hc]
      _ = n β * (b * g * b') := by group

theorem unionRootSpan_le_of
    {H : Subgroup (ModGL τ K)} (hB : unionBorel K χ J ≤ H)
    (hN : unionMonomial K χ J n ≤ H) : unionRootSpan K χ J ≤ H := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨u, hu, β, hβ, e⟩ := exists_smul_unionSimpleRoot hα
  obtain ⟨g, hgN, hgu⟩ := exists_mem_unionLifts hn hu
  have hgM := unionMonomial_le_monomialSubgroup hn hgN
  intro x hx
  have hx' : x ∈ rootSpan τ K {α} := by
    rw [rootSpan, iSup_singleton]
    exact hx
  have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem hgM) hgu.inv (S := {α})
    (by rintro _ rfl; exact isRoot_of_mem_unionRoots hα) hx'
  rw [Set.image_singleton, inv_inv, e, inv_smul_smul] at h
  have hb : g⁻¹ * x * g ∈ H := hB (unionUnipotent_le_unionBorel
    (rootSpan_mono (Set.singleton_subset_iff.2 (mem_posRoots_of_mem_unionSimpleRoots hβ)) h))
  have e' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e']
  exact mul_mem (mul_mem (hN hgN) hb) (inv_mem (hN hgN))

theorem unionRootSpan_eq_sup :
    unionRootSpan K χ J = unionBorel K χ J ⊔ unionMonomial K χ J n :=
  le_antisymm (unionRootSpan_le_of hn le_sup_left le_sup_right)
    (sup_le unionBorel_le_unionRootSpan (unionMonomial_le_unionRootSpan hn))

theorem coe_unionRootSpan_eq_iUnion :
    (unionRootSpan K χ J : Set (ModGL τ K)) =
      ⋃ w ∈ unionWeylGroup χ J, unionCell K χ J n w := by
  set X := ⋃ w ∈ unionWeylGroup χ J, unionCell K χ J n w
  have hmemX : ∀ {x : ModGL τ K}, x ∈ X ↔
      ∃ w ∈ unionWeylGroup χ J, x ∈ unionCell K χ J n w := by
    intro x
    simp only [X, Set.mem_iUnion, exists_prop]
  refine Set.Subset.antisymm ?_ (Set.iUnion₂_subset fun w _ => unionCell_subset_unionRootSpan hn w)
  have hBX : ∀ b ∈ unionBorel K χ J, ∀ x ∈ X, b * x ∈ X := fun b hb x hx => by
    obtain ⟨w, hw, hxw⟩ := hmemX.1 hx
    exact hmemX.2 ⟨w, hw, borel_mul_mem_unionCell hb hxw⟩
  have hnX : ∀ β ∈ unionSimpleRoots χ J, ∀ x ∈ X, n β * x ∈ X := by
    intro β hβ x hx
    obtain ⟨w, hw, hxw⟩ := hmemX.1 hx
    have hrw : rootReflection β * w ∈ unionWeylGroup χ J :=
      mul_mem (rootReflection_mem_unionWeylGroup hβ) hw
    have hmem := smul_mem_unionRoots (inv_mem hw) (mem_unionRoots_of_mem_unionSimpleRoots hβ)
    rcases mem_posRoots_or_mem_negRoots_unionRoots hmem with hp | hneg
    · exact hmemX.2 ⟨_, hrw, lift_mul_mem_unionCell_of_pos hn hβ hp hxw⟩
    · have hneg' : w⁻¹ • (-β) ∈ posRoots (unionRoots χ J) := by
        rw [smul_neg]
        exact hneg
      rcases lift_mul_mem_unionCell_of_neg hn hβ hneg' hxw with h | h
      · exact hmemX.2 ⟨_, hrw, h⟩
      · exact hmemX.2 ⟨w, hw, h⟩
  let St : Subgroup (ModGL τ K) :=
    { carrier := {g | (∀ x ∈ X, g * x ∈ X) ∧ ∀ x ∈ X, g⁻¹ * x ∈ X}
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      mul_mem' := fun {a b} ha hb => ⟨fun x hx => by
          rw [mul_assoc]
          exact ha.1 _ (hb.1 x hx), fun x hx => by
          rw [mul_inv_rev, mul_assoc]
          exact hb.2 _ (ha.2 x hx)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, fun x hx => by rw [inv_inv]; exact ha.1 x hx⟩ }
  have hBSt : unionBorel K χ J ≤ St := fun b hb =>
    ⟨fun x hx => hBX b hb x hx, fun x hx => hBX b⁻¹ (inv_mem hb) x hx⟩
  have hNSt : unionMonomial K χ J n ≤ St := by
    refine (Subgroup.closure_le _).2 (Set.union_subset
      (fun t ht => hBSt (unionTorus_le_unionBorel ht)) ?_)
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨fun x hx => hnX β hβ x hx, fun x hx => ?_⟩
    have e : (n β)⁻¹ * x = (n β * n β)⁻¹ * (n β * x) := by group
    rw [e]
    exact hBX _ (inv_mem (unionTorus_le_unionBorel (lift_mul_self_mem_unionTorus hn hβ))) _
      (hnX β hβ x hx)
  have hSSt := unionRootSpan_le_of hn hBSt hNSt
  intro g hg
  have h1 : (1 : ModGL τ K) ∈ X := hmemX.2 ⟨1, one_mem _, mem_unionCell.2
    ⟨1, one_mem _, 1, one_mem_unionLifts, 1, one_mem _, by group⟩⟩
  simpa using (hSSt hg).1 1 h1

end Cells

section Factorization

variable
    {K} {n : (Fin τ.rank → ℤ) → ModGL τ K}
  (hn : ∀ β ∈ unionSimpleRoots χ J, n β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
    n β ∈ monomialSubgroup τ K ∧ MapsRootLines (n β) (rootReflection β))
include hn

theorem bijOn_mul_unionCell
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J) {g : ModGL τ K}
    (hg : g ∈ unionLifts K χ J n w) :
    Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * g * p.2)
      ((unionBorel K χ J : Set (ModGL τ K)) ×ˢ
        (rootSpan τ K (unionInversionRoots χ J w) : Set (ModGL τ K)))
      ((unionBorel K χ J : Set (ModGL τ K)) * {g} * (unionBorel K χ J : Set (ModGL τ K))) := by
  have hgM := unionMonomial_le_monomialSubgroup hn hg.1
  set I := unionInversionRoots χ J w with hIdef
  set J' := {α | α ∈ posRoots (unionRoots χ J) ∧ 0 < height (w • α)} with hJ'def
  have hIU : rootSpan τ K I ≤ unionUnipotent K χ J := rootSpan_mono fun _ hα => hα.1
  have hsplit : posRoots (unionRoots χ J) = J' ∪ I := by
    ext α
    constructor
    · intro hα
      rcases IsRoot.height_pos_or_neg (IsRoot.smul (isRoot_of_mem_unionRoots hα.1) w) with h | h
      · exact Or.inl ⟨hα, h⟩
      · exact Or.inr ⟨hα, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint J' I := Set.disjoint_left.2 fun α h1 h2 => by
    have := h1.2
    have := h2.2
    omega
  have hJ' : ∀ u ∈ rootSpan τ K J', g * u * g⁻¹ ∈ unionUnipotent K χ J := fun u hu => by
    have h := conj_mem_rootSpan_of_mapsRootLines hgM hg.2 (S := J')
      (fun α hα => (isRoot_height_pos_of_mem_posRoots_unionRoots hα.1).1) hu
    refine rootSpan_mono ?_ h
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨smul_mem_unionRoots hw hα.1.1, hα.2⟩
  have hI : ∀ u ∈ rootSpan τ K I, g * u * g⁻¹ ∈ negUnipotent τ K := fun u hu => by
    have h := conj_mem_rootSpan_of_mapsRootLines hgM hg.2 (S := I)
      (fun α hα => (isRoot_height_pos_of_mem_posRoots_unionRoots hα.1).1) hu
    refine rootSpan_le_negUnipotent ?_ h
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul (isRoot_of_mem_unionRoots hα.1.1) w, hα.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, u⟩ ⟨hb, hu⟩
    exact Set.mem_mul.2 ⟨b * g, Set.mem_mul.2 ⟨b, hb, g, Set.mem_singleton g, rfl⟩, u,
      unionUnipotent_le_unionBorel (hIU hu), rfl⟩
  · rintro ⟨b, u⟩ ⟨hb, hu⟩ ⟨b', u'⟩ ⟨hb', hu'⟩ h
    simp only at h
    have e : b'⁻¹ * b = g * (u' * u⁻¹) * g⁻¹ := by
      calc b'⁻¹ * b = b'⁻¹ * (b * g * u) * u⁻¹ * g⁻¹ := by group
        _ = b'⁻¹ * (b' * g * u') * u⁻¹ * g⁻¹ := by rw [h]
        _ = g * (u' * u⁻¹) * g⁻¹ := by group
    have h1 : b'⁻¹ * b ∈ borelGroup τ K ⊓ negUnipotent τ K := Subgroup.mem_inf.2
      ⟨unionBorel_le_borelGroup (mul_mem (inv_mem hb') hb),
        by rw [e]; exact hI _ (mul_mem hu' (inv_mem hu))⟩
    obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
    rw [(opposite_Borel_intersection τ K w₁ hw₁).2.2.2, Subgroup.mem_bot] at h1
    have hbb : b = b' := (inv_mul_eq_one.1 h1).symm
    subst hbb
    rw [mul_left_cancel h]
  · intro x hx
    obtain ⟨_, ⟨b, hb, g', hg', rfl⟩, b', hb', rfl⟩ := hx
    rw [Set.mem_singleton_iff] at hg'
    rw [hg']
    rw [coe_unionBorel] at hb'
    obtain ⟨t, ht, u, hu, rfl⟩ := hb'
    have hu' : u ∈ rootSpan τ K (J' ∪ I) := by
      rw [← hsplit]
      exact hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_rootSpan_eq K (S₁ := J') (S₂ := I)
      (fun α hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα.1)
      (fun α hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα.1) hdisj
      (fun α hα γ hγ a a' ha ha' hr => by
        rw [← hsplit] at hα hγ ⊢
        exact nsmul_add_mem_posRoots_unionRoots hα hγ a a' ha ha' hr) hu'
    refine ⟨(b * (g * t * g⁻¹) * (g * u₁ * g⁻¹), u₂), ⟨mul_mem (mul_mem hb
      (unionTorus_le_unionBorel (conj_mem_unionTorus hn hg.1 ht)))
      (unionUnipotent_le_unionBorel (hJ' u₁ hu₁)), hu₂⟩, ?_⟩
    simp only
    group

end Factorization

section Isometry

theorem toReal_injective : Function.Injective (toReal (τ := τ)) := fun u v h => funext fun i => by
  have := congrFun h i
  simpa [toReal] using this

theorem toReal_sub_zsmul (u v : Fin τ.rank → ℤ) (c : ℤ) :
    toReal (u - c • v) = toReal u - (c : ℝ) • toReal v := by
  ext i
  simp [toReal]

variable (χ J) in
@[expose] def IsUnionWeylConj
    (θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ))
    (w w' : WeylGroup τ) : Prop :=
  ∀ α ∈ unionRoots χ J, ∀ α' ∈ unionRoots χ J, θ (toReal α) = toReal α' →
    θ (toReal (w • α)) = toReal (w' • α')

variable {θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)}

theorem isUnionWeylConj_one
    : IsUnionWeylConj χ J θ 1 1 := fun _ _ _ _ h => by
  simpa using h

theorem IsUnionWeylConj.mul
    {w₁ w₂ w₁' w₂' : WeylGroup τ} (h₁ : IsUnionWeylConj χ J θ w₁ w₁')
    (h₂ : IsUnionWeylConj χ J θ w₂ w₂') (hw₂ : w₂ ∈ unionWeylGroup χ J)
    (hw₂' : w₂' ∈ unionWeylGroup χ J) : IsUnionWeylConj χ J θ (w₁ * w₂) (w₁' * w₂') :=
  fun α hα α' hα' h => by
    rw [mul_smul, mul_smul]
    exact h₁ _ (smul_mem_unionRoots hw₂ hα) _ (smul_mem_unionRoots hw₂' hα') (h₂ α hα α' hα' h)

theorem IsUnionWeylConj.inv
    (hθΨ : Set.MapsTo θ (toReal '' unionRoots χ J) (toReal '' unionRoots χ J))
    {w w' : WeylGroup τ} (h : IsUnionWeylConj χ J θ w w') (hw : w ∈ unionWeylGroup χ J) :
    IsUnionWeylConj χ J θ w⁻¹ w'⁻¹ := by
  intro α hα α' _ hαα'
  have hγ := smul_mem_unionRoots (inv_mem hw) hα
  obtain ⟨γ', hγ', hθγ⟩ := hθΨ ⟨_, hγ, rfl⟩
  have h1 := h _ hγ γ' hγ' hθγ.symm
  rw [smul_inv_smul, hαα'] at h1
  have h2 : α' = w' • γ' := toReal_injective h1
  rw [← hθγ, h2, inv_smul_smul]

theorem isUnionWeylConj_rootReflection
    (hθ : ∀ x y, rform (θ x) (θ y) = rform x y)
    {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβ' : IsRoot τ β')
    (h : θ (toReal β) = toReal β') :
    IsUnionWeylConj χ J θ (rootReflection β) (rootReflection β') := by
  intro α _ α' _ hαα'
  have hk : corootPair β' α' = corootPair β α := by
    have e1 := hθ (toReal β) (toReal α)
    have e2 := hθ (toReal β) (toReal β)
    rw [h, hαα', rform_toReal, rform_toReal] at e1
    rw [h, rform_toReal, rform_toReal] at e2
    have e1' : iform β' α' = iform β α := by exact_mod_cast e1
    have e2' : iform β' β' = iform β β := by exact_mod_cast e2
    rw [corootPair, corootPair, e1', e2']
  rw [rootReflection_smul hβ, rootReflection_smul hβ', toReal_sub_zsmul, toReal_sub_zsmul,
    map_sub, map_smul, h, hαα', hk]

theorem IsUnionWeylConj.unique
    (hθΨ : Set.SurjOn θ (toReal '' unionRoots χ J) (toReal '' unionRoots χ J))
    {w u u' : WeylGroup τ} (h : IsUnionWeylConj χ J θ w u) (h' : IsUnionWeylConj χ J θ w u')
    (hu : u ∈ unionWeylGroup χ J) (hu' : u' ∈ unionWeylGroup χ J) : u = u' := by
  have hfix : ∀ α' ∈ unionRoots χ J, (u'⁻¹ * u) • α' = α' := by
    intro α' hα'
    obtain ⟨_, ⟨α, hα, rfl⟩, hθα⟩ := hθΨ ⟨α', hα', rfl⟩
    have e3 : u • α' = u' • α' :=
      toReal_injective ((h α hα α' hα' hθα).symm.trans (h' α hα α' hα' hθα))
    rw [mul_smul, e3, inv_smul_smul]
  have h1 := eq_one_of_forall_smul_eq (mul_mem (inv_mem hu') hu) hfix
  exact (inv_mul_eq_one.1 h1).symm

theorem mem_posRoots_of_theta
    (hθΔ : Set.MapsTo θ (toReal '' unionSimpleRoots χ J) (toReal '' unionSimpleRoots χ J))
    {α α' : Fin τ.rank → ℤ} (hα : α ∈ posRoots (unionRoots χ J)) (hα' : α' ∈ unionRoots χ J)
    (h : θ (toReal α) = toReal α') : α' ∈ posRoots (unionRoots χ J) := by
  classical
  obtain ⟨i, hi, hαi⟩ := mem_unionRoots_iff.1 hα.1
  obtain ⟨c, hc, e⟩ := exists_nonneg_coords (isRootComponent_componentRoots i) ⟨hαi, hα.2⟩
  have hmaps : ∀ β ∈ simpleRoots (componentRoots χ i),
      ∃ β', β' ∈ unionSimpleRoots χ J ∧ toReal β' = θ (toReal β) :=
    fun β hβ => hθΔ ⟨β, ⟨i, hi, hβ⟩, rfl⟩
  choose! f hf hθf using hmaps
  have e' : α' = ∑ β ∈ simpleRoots (componentRoots χ i), c β • f β := by
    apply toReal_injective
    rw [← h, e, toReal_sum_smul, toReal_sum_smul, map_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [map_smul, hθf β hβ]
  have hht : 0 ≤ height α' := by
    rw [e', height_finset_sum]
    refine Finset.sum_nonneg fun β hβ => ?_
    rw [height_zsmul]
    exact mul_nonneg (hc β hβ) (mem_posRoots_of_mem_unionSimpleRoots (hf β hβ)).2.le
  refine ⟨hα', ?_⟩
  rcases IsRoot.height_pos_or_neg (isRoot_of_mem_unionRoots hα') with h1 | h1
  · exact h1
  · omega

end Isometry

section Automorphisms

variable {K}

theorem coe_mulAut_mem_rootSpan
    (F : MulAut (adjointGroup τ K)) {S S' : Set (Fin τ.rank → ℤ)}
    (hF : ∀ α ∈ S, ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSubgroup τ K α →
      (F x : ModGL τ K) ∈ rootSpan τ K S')
    {x : adjointGroup τ K} (hx : (x : ModGL τ K) ∈ rootSpan τ K S) :
    (F x : ModGL τ K) ∈ rootSpan τ K S' := by
  set R' := ((rootSpan τ K S').subgroupOf (adjointGroup τ K)).comap F.toMonoidHom
  have hle : rootSpan τ K S ≤ R'.map (adjointGroup τ K).subtype := by
    refine iSup₂_le fun α hα y hy => ?_
    have hyC : y ∈ adjointGroup τ K := rootSubgroup_le_adjointGroup α hy
    exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 (hF α hα ⟨y, hyC⟩ hy), rfl⟩
  obtain ⟨x', hx', hxx⟩ := hle hx
  rw [Subtype.ext hxx] at hx'
  exact Subgroup.mem_subgroupOf.1 hx'

theorem unionRootSpan_le_adjointGroup
    : unionRootSpan K χ J ≤ adjointGroup τ K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

end Automorphisms

section Equivariance

variable {K} {n : (Fin τ.rank → ℤ) → ModGL τ K}

theorem toReal_neg (u : Fin τ.rank → ℤ) : toReal (-u) = -toReal u := by
  ext i
  simp [toReal]

theorem exists_isUnionWeylConj_mulAut_mem_unionCell_iff
    (hn : ∀ β ∈ unionSimpleRoots χ J, n β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
      n β ∈ monomialSubgroup τ K ∧ MapsRootLines (n β) (rootReflection β))
    {θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)} {F : MulAut (adjointGroup τ K)}
    (hθ : ∀ x y, rform (θ x) (θ y) = rform x y)
    (hθΨ : Set.BijOn θ (toReal '' unionRoots χ J) (toReal '' unionRoots χ J))
    (hθΔ : Set.BijOn θ (toReal '' unionSimpleRoots χ J) (toReal '' unionSimpleRoots χ J))
    (hFH : ((torusGroup τ K).subgroupOf (adjointGroup τ K)).map F.toMonoidHom =
      (torusGroup τ K).subgroupOf (adjointGroup τ K))
    (hFU : ∀ α ∈ unionRoots χ J, ∀ α' ∈ unionRoots χ J, θ (toReal α) = toReal α' →
      ((rootSubgroup τ K α).subgroupOf (adjointGroup τ K)).map F.toMonoidHom =
        (rootSubgroup τ K α').subgroupOf (adjointGroup τ K))
    (hFn : ∀ β ∈ unionSimpleRoots χ J, ∀ β' ∈ unionSimpleRoots χ J, θ (toReal β) = toReal β' →
      ∀ x : adjointGroup τ K, (x : ModGL τ K) = n β →
        ∃ t ∈ unionTorus K χ J, (F x : ModGL τ K) = t * n β')
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J) :
    ∃ w' ∈ unionWeylGroup χ J, IsUnionWeylConj χ J θ w w' ∧
      (∀ u ∈ unionWeylGroup χ J, IsUnionWeylConj χ J θ w u → u = w') ∧
      ∀ x : adjointGroup τ K,
        ((F x : ModGL τ K) ∈ unionCell K χ J n w' ↔ (x : ModGL τ K) ∈ unionCell K χ J n w) := by
  have hSC : unionRootSpan K χ J ≤ adjointGroup τ K := unionRootSpan_le_adjointGroup
  have hFα : ∀ α ∈ unionRoots χ J, ∀ α' ∈ unionRoots χ J, θ (toReal α) = toReal α' →
      ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSubgroup τ K α →
        (F x : ModGL τ K) ∈ rootSubgroup τ K α' := by
    intro α hα α' hα' h x hx
    have h1 : F x ∈ ((rootSubgroup τ K α).subgroupOf (adjointGroup τ K)).map F.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    rw [hFU α hα α' hα' h] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hFα' : ∀ α ∈ unionRoots χ J, ∀ α' ∈ unionRoots χ J, θ (toReal α) = toReal α' →
      ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ rootSubgroup τ K α' →
        (F.symm x : ModGL τ K) ∈ rootSubgroup τ K α := by
    intro α hα α' hα' h x hx
    have h1 : x ∈ ((rootSubgroup τ K α).subgroupOf (adjointGroup τ K)).map F.toMonoidHom := by
      rw [hFU α hα α' hα' h]
      exact Subgroup.mem_subgroupOf.2 hx
    obtain ⟨y, hy, rfl⟩ := h1
    simpa using Subgroup.mem_subgroupOf.1 hy
  have himg : ∀ α ∈ unionRoots χ J, ∃ α' ∈ unionRoots χ J, θ (toReal α) = toReal α' :=
    fun α hα => by
      obtain ⟨α', hα', e⟩ := hθΨ.mapsTo ⟨α, hα, rfl⟩
      exact ⟨α', hα', e.symm⟩
  have hpre : ∀ α' ∈ unionRoots χ J, ∃ α ∈ unionRoots χ J, θ (toReal α) = toReal α' :=
    fun α' hα' => by
      obtain ⟨_, ⟨α, hα, rfl⟩, e⟩ := hθΨ.surjOn ⟨α', hα', rfl⟩
      exact ⟨α, hα, e⟩
  have hpos : ∀ α ∈ posRoots (unionRoots χ J), ∀ α' ∈ unionRoots χ J,
      θ (toReal α) = toReal α' → α' ∈ posRoots (unionRoots χ J) :=
    fun _ hα _ hα' h => mem_posRoots_of_theta hθΔ.mapsTo hα hα' h
  have hpos' : ∀ α' ∈ posRoots (unionRoots χ J), ∀ α ∈ unionRoots χ J,
      θ (toReal α) = toReal α' → α ∈ posRoots (unionRoots χ J) := by
    intro α' hα' α hα h
    rcases mem_posRoots_or_mem_negRoots_unionRoots hα with h1 | h1
    · exact h1
    · exfalso
      have h2 := hpos (-α) h1 (-α') (neg_mem_unionRoots hα'.1)
        (by rw [toReal_neg, map_neg, h, toReal_neg])
      have h3 := h2.2
      have h4 := hα'.2
      rw [height_neg] at h3
      omega
  have hFS : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionRootSpan K χ J →
      (F x : ModGL τ K) ∈ unionRootSpan K χ J := fun x hx =>
    coe_mulAut_mem_rootSpan F (fun α hα y hy => by
      obtain ⟨α', hα', h⟩ := himg α hα
      exact rootSubgroup_le_unionRootSpan hα' (hFα α hα α' hα' h y hy)) hx
  have hFS' : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionRootSpan K χ J →
      (F.symm x : ModGL τ K) ∈ unionRootSpan K χ J := fun x hx =>
    coe_mulAut_mem_rootSpan F.symm (fun α' hα' y hy => by
      obtain ⟨α, hα, h⟩ := hpre α' hα'
      exact rootSubgroup_le_unionRootSpan hα (hFα' α hα α' hα' h y hy)) hx
  have hFU' : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionUnipotent K χ J →
      (F x : ModGL τ K) ∈ unionUnipotent K χ J := fun x hx =>
    coe_mulAut_mem_rootSpan F (fun α hα y hy => by
      obtain ⟨α', hα', h⟩ := himg α hα.1
      exact (le_iSup₂_of_le α' (hpos α hα α' hα' h) le_rfl :
        rootSubgroup τ K α' ≤ unionUnipotent K χ J) (hFα α hα.1 α' hα' h y hy)) hx
  have hFU'' : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionUnipotent K χ J →
      (F.symm x : ModGL τ K) ∈ unionUnipotent K χ J := fun x hx =>
    coe_mulAut_mem_rootSpan F.symm (fun α' hα' y hy => by
      obtain ⟨α, hα, h⟩ := hpre α' hα'.1
      exact (le_iSup₂_of_le α (hpos' α' hα' α hα h) le_rfl :
        rootSubgroup τ K α ≤ unionUnipotent K χ J) (hFα' α hα α' hα'.1 h y hy)) hx
  have hFH' : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ torusGroup τ K →
      (F x : ModGL τ K) ∈ torusGroup τ K := fun x hx => by
    have h1 : F x ∈ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).map F.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    rw [hFH] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hFH'' : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ torusGroup τ K →
      (F.symm x : ModGL τ K) ∈ torusGroup τ K := fun x hx => by
    have h1 : x ∈ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).map F.toMonoidHom := by
      rw [hFH]
      exact Subgroup.mem_subgroupOf.2 hx
    obtain ⟨y, hy, rfl⟩ := h1
    simpa using Subgroup.mem_subgroupOf.1 hy
  have hFT : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionTorus K χ J →
      (F x : ModGL τ K) ∈ unionTorus K χ J := fun x hx =>
    Subgroup.mem_inf.2 ⟨hFS x hx.1, hFH' x hx.2⟩
  have hFT' : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionTorus K χ J →
      (F.symm x : ModGL τ K) ∈ unionTorus K χ J := fun x hx =>
    Subgroup.mem_inf.2 ⟨hFS' x hx.1, hFH'' x hx.2⟩
  have hB : ∀ G : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionTorus K χ J →
        (G x : ModGL τ K) ∈ unionTorus K χ J) →
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionUnipotent K χ J →
        (G x : ModGL τ K) ∈ unionUnipotent K χ J) →
      ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ unionBorel K χ J →
        (G x : ModGL τ K) ∈ unionBorel K χ J := by
    intro G hGT hGU x hx
    rw [← SetLike.mem_coe, coe_unionBorel] at hx
    obtain ⟨t, ht, u, hu, htu⟩ := hx
    have htC : t ∈ adjointGroup τ K := hSC (unionTorus_le_unionRootSpan ht)
    have huC : u ∈ adjointGroup τ K := hSC (unionUnipotent_le_unionRootSpan hu)
    have hx' : x = ⟨t, htC⟩ * ⟨u, huC⟩ := Subtype.ext htu.symm
    rw [hx', map_mul, Subgroup.coe_mul]
    exact mul_mem (unionTorus_le_unionBorel (hGT ⟨t, htC⟩ ht))
      (unionUnipotent_le_unionBorel (hGU ⟨u, huC⟩ hu))
  have hFB := hB F hFT hFU'
  have hFB' := hB F.symm hFT' hFU''
  have key : ∀ y ∈ unionMonomial K χ J n, ∀ x : adjointGroup τ K, (x : ModGL τ K) = y →
      ∃ w₀ ∈ unionWeylGroup χ J, MapsRootLines y w₀ ∧ ∃ w' ∈ unionWeylGroup χ J,
        IsUnionWeylConj χ J θ w₀ w' ∧ (F x : ModGL τ K) ∈ unionLifts K χ J n w' := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      intro x hxz
      rcases hz with hz | ⟨β, hβ, rfl⟩
      · have hT := hFT x (by rw [hxz]; exact hz)
        exact ⟨1, one_mem _, mapsRootLines_of_mem_torusGroup (unionTorus_le_torusGroup hz), 1,
          one_mem _, isUnionWeylConj_one, unionTorus_le_unionMonomial hT,
          mapsRootLines_of_mem_torusGroup (unionTorus_le_torusGroup hT)⟩
      · obtain ⟨β', hβ', hθβ⟩ := hθΔ.mapsTo ⟨β, hβ, rfl⟩
        obtain ⟨t, ht, hFx⟩ := hFn β hβ β' hβ' hθβ.symm x hxz
        refine ⟨rootReflection β, rootReflection_mem_unionWeylGroup hβ, (hn β hβ).2.2,
          rootReflection β', rootReflection_mem_unionWeylGroup hβ',
          isUnionWeylConj_rootReflection hθ (isRoot_of_mem_unionSimpleRoots hβ)
            (isRoot_of_mem_unionSimpleRoots hβ') hθβ.symm, ?_⟩
        rw [hFx]
        have h1 := (mapsRootLines_of_mem_torusGroup (unionTorus_le_torusGroup ht)).mul
          (hn β' hβ').2.2
        rw [one_mul] at h1
        exact ⟨mul_mem (unionTorus_le_unionMonomial ht) (lift_mem_unionMonomial hβ'), h1⟩
    | one =>
      intro x hx1
      have hx : x = 1 := Subtype.ext hx1
      subst hx
      refine ⟨1, one_mem _, mapsRootLines_one, 1, one_mem _, isUnionWeylConj_one, ?_⟩
      rw [map_one]
      exact one_mem_unionLifts
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      intro x hx
      have hy₁C : y₁ ∈ adjointGroup τ K := hSC (unionMonomial_le_unionRootSpan hn hy₁)
      have hy₂C : y₂ ∈ adjointGroup τ K := hSC (unionMonomial_le_unionRootSpan hn hy₂)
      obtain ⟨w₁, hw₁, hm₁, w₁', hw₁', hc₁, hl₁⟩ := ih₁ ⟨y₁, hy₁C⟩ rfl
      obtain ⟨w₂, hw₂, hm₂, w₂', hw₂', hc₂, hl₂⟩ := ih₂ ⟨y₂, hy₂C⟩ rfl
      have hx' : x = ⟨y₁, hy₁C⟩ * ⟨y₂, hy₂C⟩ := Subtype.ext hx
      refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, hm₁.mul hm₂, w₁' * w₂', mul_mem hw₁' hw₂',
        hc₁.mul hc₂ hw₂ hw₂', ?_⟩
      rw [hx', map_mul, Subgroup.coe_mul]
      exact mul_mem_unionLifts hl₁ hl₂
    | inv y hy ih =>
      intro x hx
      have hyC : y ∈ adjointGroup τ K := hSC (unionMonomial_le_unionRootSpan hn hy)
      obtain ⟨w₀, hw₀, hm, w', hw', hc, hl⟩ := ih ⟨y, hyC⟩ rfl
      have hx' : x = (⟨y, hyC⟩ : adjointGroup τ K)⁻¹ := Subtype.ext hx
      refine ⟨w₀⁻¹, inv_mem hw₀, hm.inv, w'⁻¹, inv_mem hw', hc.inv hθΨ.mapsTo hw₀, ?_⟩
      rw [hx', map_inv, InvMemClass.coe_inv]
      exact inv_mem_unionLifts hl
  obtain ⟨g, hg⟩ := exists_mem_unionLifts hn hw
  have hgC : g ∈ adjointGroup τ K := hSC (unionMonomial_le_unionRootSpan hn hg.1)
  obtain ⟨w₀, -, hm, w', hw', hc, hl⟩ := key g hg.1 ⟨g, hgC⟩ rfl
  have hw₀ : w₀ = w := hm.unique hg.2
  subst hw₀
  refine ⟨w', hw', hc, fun u hu hcu => IsUnionWeylConj.unique hθΨ.surjOn hcu hc hu hw',
    fun x => ⟨fun hFx => ?_, fun hx => ?_⟩⟩
  · rw [← doubleCoset_eq_unionCell hn hl] at hFx
    obtain ⟨b, hb, b', hb', e⟩ := DoubleCoset.mem_doubleCoset.1 hFx
    have hbC : b ∈ adjointGroup τ K := hSC (unionBorel_le_unionRootSpan hb)
    have hb'C : b' ∈ adjointGroup τ K := hSC (unionBorel_le_unionRootSpan hb')
    have e' : F x = ⟨b, hbC⟩ * F ⟨g, hgC⟩ * ⟨b', hb'C⟩ := Subtype.ext e
    have e'' : x = F.symm ⟨b, hbC⟩ * ⟨g, hgC⟩ * F.symm ⟨b', hb'C⟩ := by
      apply F.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, e']
    rw [← doubleCoset_eq_unionCell hn hg, e'']
    exact DoubleCoset.mem_doubleCoset.2 ⟨_, hFB' ⟨b, hbC⟩ hb, _, hFB' ⟨b', hb'C⟩ hb', rfl⟩
  · rw [← doubleCoset_eq_unionCell hn hg] at hx
    obtain ⟨b, hb, b', hb', e⟩ := DoubleCoset.mem_doubleCoset.1 hx
    have hbC : b ∈ adjointGroup τ K := hSC (unionBorel_le_unionRootSpan hb)
    have hb'C : b' ∈ adjointGroup τ K := hSC (unionBorel_le_unionRootSpan hb')
    have e' : x = ⟨b, hbC⟩ * ⟨g, hgC⟩ * ⟨b', hb'C⟩ := Subtype.ext e
    rw [← doubleCoset_eq_unionCell hn hl, e', map_mul, map_mul]
    exact DoubleCoset.mem_doubleCoset.2 ⟨_, hFB ⟨b, hbC⟩ hb, _, hFB ⟨b', hb'C⟩ hb', rfl⟩

end Equivariance

theorem orthogonal_union_Bruhat_cell_factorization
    (τ : Tag) (K : Type) [Field K] {M : Type*}
    [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (J : Set (KernelComponent χ))
    (n : (Fin τ.rank → ℤ) → ModGL τ K)
    (hn : ∀ β ∈ unionSimpleRoots χ J, n β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
      n β ∈ monomialSubgroup τ K ∧ MapsRootLines (n β) (rootReflection β)) :
    (∀ w ∈ unionWeylGroup χ J, (unionLifts K χ J n w).Nonempty) ∧
    (∀ w ∈ unionWeylGroup χ J, ∀ g ∈ unionLifts K χ J n w,
      (unionBorel K χ J : Set (ModGL τ K)) * {g} * (unionBorel K χ J : Set (ModGL τ K)) =
        unionCell K χ J n w) ∧
    (unionRootSpan K χ J : Set (ModGL τ K)) =
      ⋃ w ∈ unionWeylGroup χ J, unionCell K χ J n w ∧
    (∀ w ∈ unionWeylGroup χ J, ∀ w' ∈ unionWeylGroup χ J, w ≠ w' →
      Disjoint (unionCell K χ J n w) (unionCell K χ J n w')) ∧
    (∀ w ∈ unionWeylGroup χ J, ∀ g ∈ unionLifts K χ J n w,
      Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * g * p.2)
        ((unionBorel K χ J : Set (ModGL τ K)) ×ˢ
          (rootSpan τ K (unionInversionRoots χ J w) : Set (ModGL τ K)))
        ((unionBorel K χ J : Set (ModGL τ K)) * {g} *
          (unionBorel K χ J : Set (ModGL τ K)))) ∧
    (unionBorel K χ J : Set (ModGL τ K)) =
      (unionTorus K χ J : Set (ModGL τ K)) * (unionUnipotent K χ J : Set (ModGL τ K)) ∧
    (∀ t ∈ unionTorus K χ J, ∀ t' ∈ unionTorus K χ J, ∀ u ∈ unionUnipotent K χ J,
      ∀ u' ∈ unionUnipotent K χ J, t * u = t' * u' → t = t' ∧ u = u') ∧
    (∀ x ∈ unionTorus K χ J, ∀ y ∈ unionTorus K χ J, x * y = y * x) ∧
    Group.IsNilpotent (unionUnipotent K χ J) ∧
    ∀ (θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)) (F : MulAut (adjointGroup τ K)),
      (∀ x y, rform (θ x) (θ y) = rform x y) →
      Set.BijOn θ (toReal '' unionRoots χ J) (toReal '' unionRoots χ J) →
      Set.BijOn θ (toReal '' unionSimpleRoots χ J) (toReal '' unionSimpleRoots χ J) →
      ((torusGroup τ K).subgroupOf (adjointGroup τ K)).map F.toMonoidHom =
        (torusGroup τ K).subgroupOf (adjointGroup τ K) →
      (∀ α ∈ unionRoots χ J, ∀ α' ∈ unionRoots χ J, θ (toReal α) = toReal α' →
        ((rootSubgroup τ K α).subgroupOf (adjointGroup τ K)).map F.toMonoidHom =
          (rootSubgroup τ K α').subgroupOf (adjointGroup τ K)) →
      (∀ β ∈ unionSimpleRoots χ J, ∀ β' ∈ unionSimpleRoots χ J, θ (toReal β) = toReal β' →
        ∀ x : adjointGroup τ K, (x : ModGL τ K) = n β →
          ∃ t ∈ unionTorus K χ J, (F x : ModGL τ K) = t * n β') →
      ∀ w ∈ unionWeylGroup χ J, ∃ w' ∈ unionWeylGroup χ J, IsUnionWeylConj χ J θ w w' ∧
        (∀ u ∈ unionWeylGroup χ J, IsUnionWeylConj χ J θ w u → u = w') ∧
        ∀ x : adjointGroup τ K,
          ((F x : ModGL τ K) ∈ unionCell K χ J n w' ↔ (x : ModGL τ K) ∈ unionCell K χ J n w) :=
  ⟨fun _ hw => exists_mem_unionLifts hn hw, fun _ _ _ hg => doubleCoset_eq_unionCell hn hg,
    coe_unionRootSpan_eq_iUnion hn, fun _ _ _ _ h => disjoint_unionCell hn h,
    fun _ hw _ hg => bijOn_mul_unionCell hn hw hg, coe_unionBorel,
    fun _ ht _ ht' _ hu _ hu' h => eq_and_eq_of_mul_eq_mul ht ht' hu hu' h,
    fun _ hx _ hy => mul_comm_of_mem_unionTorus hx hy, isNilpotent_unionUnipotent,
    fun _ _ hθ hθΨ hθΔ hFH hFU hFn _ hw =>
      exists_isUnionWeylConj_mulAut_mem_unionCell_iff hn hθ hθΨ hθΔ hFH hFU hFn hw⟩

end CFSG.LieType.Chevalley
