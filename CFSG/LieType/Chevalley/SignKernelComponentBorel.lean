module

public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable
    {τ : Tag} (K : Type) [Field K] {M : Type*} [CommGroup M]
  (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
  (v : (Fin τ.rank → ℤ) → WeylGroup τ) (j : (Fin τ.rank → ℤ) → Fin τ.rank)

@[expose] def componentUnipotent
    : Subgroup (ModGL τ K) :=
  rootSpan τ K (posRoots (componentRoots χ i))

@[expose] def componentTorus
    : Subgroup (ModGL τ K) :=
  componentRootSpan K χ i ⊓ torusGroup τ K

@[expose] def componentBorel
    : Subgroup (ModGL τ K) :=
  componentTorus K χ i ⊔ componentUnipotent K χ i

@[expose] def componentWeylElt
    (β : Fin τ.rank → ℤ) : ModGL τ K :=
  canonicalRep (coxeterSystem τ) K (v β) * weylElt τ K (j β) 1 *
    (canonicalRep (coxeterSystem τ) K (v β))⁻¹

@[expose] def componentXElt
    (β : Fin τ.rank → ℤ) (c : K) : ModGL τ K :=
  canonicalRep (coxeterSystem τ) K (v β) * xUnit τ K (j β) c *
    (canonicalRep (coxeterSystem τ) K (v β))⁻¹

@[expose] def componentYElt
    (β : Fin τ.rank → ℤ) (c : K) : ModGL τ K :=
  canonicalRep (coxeterSystem τ) K (v β) * yUnit τ K (j β) c *
    (canonicalRep (coxeterSystem τ) K (v β))⁻¹

@[expose] def componentMonomial
    : Subgroup (ModGL τ K) :=
  Subgroup.closure ((componentTorus K χ i : Set (ModGL τ K)) ∪
    componentWeylElt K v j '' (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ)))

theorem componentWeylElt_mem_monomialSubgroup
    (β : Fin τ.rank → ℤ) :
    componentWeylElt K v j β ∈ monomialSubgroup τ K := by
  have hn : canonicalRep (coxeterSystem τ) K (v β) ∈ monomialSubgroup τ K :=
    Subgroup.mem_sup_right (canonicalRep_mem_closure _ K (v β))
  exact mul_mem (mul_mem hn (weylElt_mem_monomialSubgroup _)) (inv_mem hn)

theorem componentTorus_le_torusGroup
    : componentTorus K χ i ≤ torusGroup τ K :=
  inf_le_right

theorem componentTorus_le_componentRootSpan :
    componentTorus K χ i ≤ componentRootSpan K χ i :=
  inf_le_left

theorem componentMonomial_le_monomialSubgroup :
    componentMonomial K χ i v j ≤ monomialSubgroup τ K := by
  refine (Subgroup.closure_le _).2 (Set.union_subset (fun t ht => ?_) ?_)
  · exact torusGroup_le_monomialSubgroup (componentTorus_le_torusGroup K χ i ht)
  · rintro _ ⟨β, -, rfl⟩
    exact componentWeylElt_mem_monomialSubgroup K v j β

@[expose] def componentWeylHom :
    componentMonomial K χ i v j →* WeylGroup τ :=
  (weylQuotientHom τ K).comp
    (Subgroup.inclusion (componentMonomial_le_monomialSubgroup K χ i v j))

@[expose] def componentLifts
    (w : WeylGroup τ) : Set (ModGL τ K) :=
  {g | ∃ hg : g ∈ componentMonomial K χ i v j, componentWeylHom K χ i v j ⟨g, hg⟩ = w}

@[expose] def componentCell
    (w : WeylGroup τ) : Set (ModGL τ K) :=
  (componentBorel K χ i : Set (ModGL τ K)) * componentLifts K χ i v j w *
    (componentBorel K χ i : Set (ModGL τ K))

variable {K χ i v j}

theorem isRoot_of_mem_componentRoots
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) :
    IsRoot τ α :=
  (isRootComponent_componentRoots i).isRoot α hα

theorem mem_componentRoots_of_nsmul_add
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i)
    (hβ : β ∈ componentRoots χ i) (a b : ℕ) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ componentRoots χ i := by
  obtain ⟨hαk, hαi⟩ := hα
  obtain ⟨hβk, hβi⟩ := hβ
  have hγk : a • α + b • β ∈ kernelRoots χ := ⟨hr, chi_nsmul_add hαk.2 hβk.2 a b⟩
  refine ⟨hγk, ?_⟩
  have hpos := iform_self_pos_of_isRoot hr
  have e : ∀ γ, iform (a • α + b • β) γ = (a : ℤ) * iform α γ + (b : ℤ) * iform β γ :=
    fun γ => by
      rw [iform_add_left, ← Nat.cast_smul_eq_nsmul ℤ a α, ← Nat.cast_smul_eq_nsmul ℤ b β,
        iform_smul_left, iform_smul_left]
  by_cases h1 : iform α (a • α + b • β) = 0
  · have h2 : iform β (a • α + b • β) ≠ 0 := by
      intro h2
      have := e (a • α + b • β)
      rw [h1, h2, mul_zero, mul_zero, add_zero] at this
      omega
    exact (mk_eq_of_iform_ne_zero (α := ⟨_, hγk⟩) (β := ⟨β, hβk⟩)
      (by rw [iform_comm]; exact h2)).trans hβi
  · exact (mk_eq_of_iform_ne_zero (α := ⟨_, hγk⟩) (β := ⟨α, hαk⟩)
      (by rw [iform_comm]; exact h1)).trans hαi

theorem mem_posRoots_of_nsmul_add
    {α β : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (componentRoots χ i)) (hβ : β ∈ posRoots (componentRoots χ i)) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ posRoots (componentRoots χ i) := by
  refine ⟨mem_componentRoots_of_nsmul_add hα.1 hβ.1 a b hr, ?_⟩
  rw [height_nsmul_add_nsmul]
  have ha' : (0 : ℤ) < a := by omega
  have hb' : (0 : ℤ) < b := by omega
  exact add_pos (mul_pos ha' hα.2) (mul_pos hb' hβ.2)

theorem isRoot_height_pos_of_mem_posRoots
    {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (componentRoots χ i)) : IsRoot τ α ∧ 0 < height α :=
  ⟨isRoot_of_mem_componentRoots hα.1, hα.2⟩

theorem inv_smul_mem_posRoots_of_componentLength
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i))
    (h : componentLength (componentRoots χ i) (rootReflection β * w) =
      componentLength (componentRoots χ i) w + 1) :
    w⁻¹ • β ∈ posRoots (componentRoots χ i) := by
  have hΨ := isRootComponent_componentRoots i
  have hmem := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) β (simpleRoots_subset hβ)
  rcases mem_posRoots_or_mem_negRoots hΨ hmem with hp | hn
  · exact hp
  · have := (componentLength_rootReflection_mul hΨ hβ hw).1.2 hn
    omega

theorem inv_smul_neg_mem_posRoots_of_componentLength
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i))
    (h : componentLength (componentRoots χ i) (rootReflection β * w) =
      componentLength (componentRoots χ i) w - 1) :
    w⁻¹ • (-β) ∈ posRoots (componentRoots χ i) := by
  have hn := (componentLength_rootReflection_mul (isRootComponent_componentRoots i) hβ hw).1.1 h
  rw [smul_neg]
  exact hn

theorem componentUnipotent_le_posUnipotent :
    componentUnipotent K χ i ≤ posUnipotent τ K :=
  rootSpan_le_posUnipotent fun _ hα => isRoot_height_pos_of_mem_posRoots hα

theorem componentUnipotent_le_componentRootSpan :
    componentUnipotent K χ i ≤ componentRootSpan K χ i :=
  rootSpan_mono fun _ hα => hα.1

theorem mul_comm_of_mem_componentTorus
    {x y : ModGL τ K} (hx : x ∈ componentTorus K χ i)
    (hy : y ∈ componentTorus K χ i) : x * y = y * x :=
  (triangular_borel_structure.{0, 0} τ K).1 x (componentTorus_le_torusGroup K χ i hx) y
    (componentTorus_le_torusGroup K χ i hy)

theorem componentTorus_le_normalizer :
    componentTorus K χ i ≤ Subgroup.normalizer (componentUnipotent K χ i : Set (ModGL τ K)) :=
  (componentTorus_le_torusGroup K χ i).trans
    (torusGroup_le_normalizer_rootSpan fun _ hα => (isRoot_height_pos_of_mem_posRoots hα).1)

theorem componentTorus_inf_componentUnipotent :
    componentTorus K χ i ⊓ componentUnipotent K χ i = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  have h : g ∈ torusGroup τ K ⊓ posUnipotent τ K := Subgroup.mem_inf.2
    ⟨componentTorus_le_torusGroup K χ i h1, componentUnipotent_le_posUnipotent h2⟩
  rwa [(triangular_borel_structure.{0, 0} τ K).2.2.2.1] at h

theorem coe_componentBorel :
    (componentBorel K χ i : Set (ModGL τ K)) =
      (componentTorus K χ i : Set (ModGL τ K)) * (componentUnipotent K χ i : Set (ModGL τ K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ componentTorus_le_normalizer

theorem componentTorus_le_componentBorel
    : componentTorus K χ i ≤ componentBorel K χ i :=
  le_sup_left

theorem componentUnipotent_le_componentBorel :
    componentUnipotent K χ i ≤ componentBorel K χ i :=
  le_sup_right

theorem componentBorel_le_borelGroup
    : componentBorel K χ i ≤ borelGroup τ K :=
  sup_le ((componentTorus_le_torusGroup K χ i).trans torusGroup_le_borelGroup)
    (componentUnipotent_le_posUnipotent.trans le_sup_right)

theorem componentBorel_le_componentRootSpan :
    componentBorel K χ i ≤ componentRootSpan K χ i :=
  sup_le (componentTorus_le_componentRootSpan K χ i) componentUnipotent_le_componentRootSpan

theorem componentUnipotent_subgroupOf_normal :
    ((componentUnipotent K χ i).subgroupOf (componentBorel K χ i)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer componentUnipotent_le_componentBorel).2
    (sup_le componentTorus_le_normalizer Subgroup.le_normalizer)

theorem isNilpotent_componentUnipotent
    : Group.IsNilpotent (componentUnipotent K χ i) := by
  have := (positive_root_height_series τ K).2.2.2.2.1
  refine Subgroup.isNilpotent_of_ker_le_center
    (Subgroup.inclusion (componentUnipotent_le_posUnipotent (K := K) (χ := χ) (i := i))) ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (Subgroup.inclusion_injective _)]
  exact bot_le

theorem conj_mem_rootSpan_of_mapsRootLines
    {g : ModGL τ K} (hg : g ∈ monomialSubgroup τ K)
    {w : WeylGroup τ} (hgw : MapsRootLines g w) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {x : ModGL τ K} (hx : x ∈ rootSpan τ K S) :
    g * x * g⁻¹ ∈ rootSpan τ K ((fun α => w • α) '' S) := by
  obtain ⟨w', k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hg
  have hmaps : MapsRootLines (k * canonicalRep (coxeterSystem τ) K w') w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
  rw [← hmaps.unique hgw]
  have h1 := canonicalRep_conj_mem_rootSpan (w := w') hS hx
  have hS' : ∀ α ∈ (fun α => w' • α) '' S, IsRoot τ α := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul (hS α hα) w'
  have h2 := (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan hS' hk) _).1 h1
  rw [mul_inv_rev]
  simpa only [mul_assoc, SetLike.mem_coe] using h2

theorem canonicalRep_conj_mem_rootSpan_singleton
    (w : WeylGroup τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {x : ModGL τ K} (hx : x ∈ rootSpan τ K {γ}) :
    canonicalRep (coxeterSystem τ) K w * x * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      rootSpan τ K {w • γ} := by
  have h := canonicalRep_conj_mem_rootSpan (w := w) (S := {γ}) (by rintro _ rfl; exact hγ) hx
  rwa [Set.image_singleton] at h

theorem xUnit_mem_rootSpan_single
    (k : Fin τ.rank) (c : K) :
    xUnit τ K k c ∈ rootSpan τ K {(Pi.single k 1 : Fin τ.rank → ℤ)} := by
  rw [← pinnedX_single]
  exact pinnedX_mem_rootSpan (Set.mem_singleton _) c

theorem yUnit_mem_rootSpan_neg_single
    (k : Fin τ.rank) (c : K) :
    yUnit τ K k c ∈ rootSpan τ K {(-Pi.single k 1 : Fin τ.rank → ℤ)} := by
  rw [← pinnedX_neg_single]
  exact pinnedX_mem_rootSpan (Set.mem_singleton _) c

theorem componentXElt_mem
    {β : Fin τ.rank → ℤ}
    (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) (c : K) :
    componentXElt K v j β c ∈ rootSpan τ K {β} := by
  have h := canonicalRep_conj_mem_rootSpan_singleton (v β) (isRoot_single τ (j β))
    (xUnit_mem_rootSpan_single (j β) c)
  rwa [hβv] at h

theorem componentYElt_mem
    {β : Fin τ.rank → ℤ}
    (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) (c : K) :
    componentYElt K v j β c ∈ rootSpan τ K {-β} := by
  have h := canonicalRep_conj_mem_rootSpan_singleton (v β) (isRoot_neg_single τ (j β))
    (yUnit_mem_rootSpan_neg_single (j β) c)
  rwa [smul_neg, hβv] at h

theorem componentXElt_zero
    (β : Fin τ.rank → ℤ) : componentXElt K v j β 0 = 1 := by
  rw [componentXElt, xUnit_zero, mul_one, mul_inv_cancel]

theorem exists_componentXElt_eq
    {β : Fin τ.rank → ℤ}
    (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K {β}) : ∃ c : K, componentXElt K v j β c = u := by
  rw [rootSpan, iSup_singleton, ← hβv,
    ← (canonical_weyl_root_transport τ K).2.1 (v β) _ (isRoot_single τ (j β))] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  refine ⟨c, ?_⟩
  rw [componentXElt, pinnedX_single]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem canonicalRep_conj_weylElt_mem
    {w : WeylGroup τ} {k : Fin τ.rank}
    (hk : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ componentRoots χ i) (t : Kˣ) :
    canonicalRep (coxeterSystem τ) K w * weylElt τ K k t *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ componentRootSpan K χ i := by
  have hneg := (isRootComponent_componentRoots i).neg_mem _ hk
  set n := canonicalRep (coxeterSystem τ) K w
  have hx : ∀ c : K, n * xUnit τ K k c * n⁻¹ ∈ componentRootSpan K χ i := fun c =>
    rootSpan_mono (Set.singleton_subset_iff.2 hk)
      (canonicalRep_conj_mem_rootSpan_singleton w (isRoot_single τ k)
        (xUnit_mem_rootSpan_single k c))
  have hy : ∀ c : K, n * yUnit τ K k c * n⁻¹ ∈ componentRootSpan K χ i := fun c => by
    have h := canonicalRep_conj_mem_rootSpan_singleton w (isRoot_neg_single τ k)
      (yUnit_mem_rootSpan_neg_single k c)
    rw [smul_neg] at h
    exact rootSpan_mono (Set.singleton_subset_iff.2 hneg) h
  have e : weylElt τ K k t = xUnit τ K k t * yUnit τ K k (-((t⁻¹ : Kˣ) : K)) * xUnit τ K k t :=
    Units.ext rfl
  have e' : n * weylElt τ K k t * n⁻¹ = (n * xUnit τ K k t * n⁻¹) *
      (n * yUnit τ K k (-((t⁻¹ : Kˣ) : K)) * n⁻¹) * (n * xUnit τ K k t * n⁻¹) := by
    rw [e]
    group
  rw [e']
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem canonicalRep_conj_torusElt_mem
    {w : WeylGroup τ} {k : Fin τ.rank}
    (hk : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ componentRoots χ i) (t : Kˣ) :
    canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ componentTorus K χ i := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have e : canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ =
          (canonicalRep (coxeterSystem τ) K w * weylElt τ K k t *
            (canonicalRep (coxeterSystem τ) K w)⁻¹) *
          (canonicalRep (coxeterSystem τ) K w * weylElt τ K k (-1) *
            (canonicalRep (coxeterSystem τ) K w)⁻¹) := by
      rw [torusElt]
      group
    rw [e]
    exact mul_mem (canonicalRep_conj_weylElt_mem hk t) (canonicalRep_conj_weylElt_mem hk (-1))
  · exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w) _).1
      (torusElt_mem_torusGroup k t)

theorem mapsRootLines_componentWeylElt
    {β : Fin τ.rank → ℤ}
    (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) :
    MapsRootLines (componentWeylElt K v j β) (rootReflection β) := by
  rw [rootReflection_eq_conj hβv]
  exact ((mapsRootLines_canonicalRep (v β)).mul (mapsRootLines_weylElt (j β))).mul
    (mapsRootLines_canonicalRep (v β)).inv

theorem componentWeylElt_mem_componentRootSpan
    {β : Fin τ.rank → ℤ}
    (hβv : v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) (hβ : β ∈ componentRoots χ i) :
    componentWeylElt K v j β ∈ componentRootSpan K χ i :=
  canonicalRep_conj_weylElt_mem (by rw [hβv]; exact hβ) 1

theorem componentWeylElt_mul_componentXElt
    (β : Fin τ.rank → ℤ) (c : Kˣ) :
    componentWeylElt K v j β * componentXElt K v j β c =
      componentXElt K v j β (-((c⁻¹ : Kˣ) : K)) *
        (canonicalRep (coxeterSystem τ) K (v β) * torusElt τ K (j β) (-c⁻¹) *
          (canonicalRep (coxeterSystem τ) K (v β))⁻¹) *
        componentYElt K v j β ((c⁻¹ : Kˣ) : K) := by
  have h := weylElt_one_mul_xUnit (τ := τ) (R := K) (j β) c
  simp only [componentWeylElt, componentXElt, componentYElt]
  calc _ = canonicalRep (coxeterSystem τ) K (v β) * (weylElt τ K (j β) 1 * xUnit τ K (j β) c) *
        (canonicalRep (coxeterSystem τ) K (v β))⁻¹ := by group
    _ = _ := by rw [h]; group

variable (hvj : ∀ β ∈ simpleRoots (componentRoots χ i),
  v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
include hvj

theorem componentMonomial_le_componentRootSpan :
    componentMonomial K χ i v j ≤ componentRootSpan K χ i := by
  refine (Subgroup.closure_le _).2 (Set.union_subset
    (fun t ht => componentTorus_le_componentRootSpan K χ i ht) ?_)
  rintro _ ⟨β, hβ, rfl⟩
  exact componentWeylElt_mem_componentRootSpan (hvj β hβ) (simpleRoots_subset hβ)

omit hvj in
theorem componentTorus_le_componentMonomial :
    componentTorus K χ i ≤ componentMonomial K χ i v j :=
  fun _ ht => Subgroup.subset_closure (Or.inl ht)

omit hvj in
theorem componentWeylElt_mem_componentMonomial
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) :
    componentWeylElt K v j β ∈ componentMonomial K χ i v j :=
  Subgroup.subset_closure (Or.inr ⟨β, hβ, rfl⟩)

theorem exists_mapsRootLines_of_mem_componentMonomial
    {g : ModGL τ K}
    (hg : g ∈ componentMonomial K χ i v j) :
    ∃ w ∈ componentWeylGroup (componentRoots χ i), MapsRootLines g w := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨β, hβ, rfl⟩
    · exact ⟨1, one_mem _,
        mapsRootLines_of_mem_torusGroup (componentTorus_le_torusGroup K χ i hx)⟩
    · exact ⟨_, rootReflection_mem_componentWeylGroup hβ,
        mapsRootLines_componentWeylElt (hvj β hβ)⟩
  | one => exact ⟨1, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, hw, h⟩ := hx
    obtain ⟨w', hw', h'⟩ := hy
    exact ⟨w * w', mul_mem hw hw', h.mul h'⟩
  | inv x _ hx =>
    obtain ⟨w, hw, h⟩ := hx
    exact ⟨w⁻¹, inv_mem hw, h.inv⟩

theorem exists_mem_componentMonomial_mapsRootLines
    {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i)) :
    ∃ g ∈ componentMonomial K χ i v j, MapsRootLines g w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact ⟨_, componentWeylElt_mem_componentMonomial hβ,
      mapsRootLines_componentWeylElt (hvj β hβ)⟩
  | one => exact ⟨1, one_mem _, mapsRootLines_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨g, hg, h⟩ := hx
    obtain ⟨g', hg', h'⟩ := hy
    exact ⟨g * g', mul_mem hg hg', h.mul h'⟩
  | inv x _ hx =>
    obtain ⟨g, hg, h⟩ := hx
    exact ⟨g⁻¹, inv_mem hg, h.inv⟩

theorem mem_componentTorus_of_mapsRootLines_one
    {g : ModGL τ K}
    (hg : g ∈ componentMonomial K χ i v j) (h1 : MapsRootLines g 1) :
    g ∈ componentTorus K χ i :=
  Subgroup.mem_inf.2 ⟨componentMonomial_le_componentRootSpan hvj hg,
    mem_torusGroup_of_mapsRootLines_one (componentMonomial_le_monomialSubgroup K χ i v j hg) h1⟩

theorem conj_mem_componentTorus
    {g : ModGL τ K} (hg : g ∈ componentMonomial K χ i v j)
    {t : ModGL τ K} (ht : t ∈ componentTorus K χ i) : g * t * g⁻¹ ∈ componentTorus K χ i := by
  have hgM := componentMonomial_le_monomialSubgroup K χ i v j hg
  have htH := componentTorus_le_torusGroup K χ i ht
  obtain ⟨w, hw⟩ := exists_mapsRootLines_of_mem hgM
  refine mem_componentTorus_of_mapsRootLines_one hvj
    (mul_mem (mul_mem hg (componentTorus_le_componentMonomial ht)) (inv_mem hg)) ?_
  simpa using (hw.mul (mapsRootLines_of_mem_torusGroup htH)).mul hw.inv

omit hvj in
theorem componentWeylHom_apply
    (g : componentMonomial K χ i v j) :
    componentWeylHom K χ i v j g =
      weylQuotientHom τ K
        (Subgroup.inclusion (componentMonomial_le_monomialSubgroup K χ i v j) g) :=
  rfl

omit hvj in
theorem componentWeylHom_eq_iff
    {g : componentMonomial K χ i v j} {w : WeylGroup τ} :
    componentWeylHom K χ i v j g = w ↔ MapsRootLines (g : ModGL τ K) w := by
  rw [componentWeylHom_apply]
  refine ⟨fun h => ?_, fun h => weylQuotientHom_eq h⟩
  rw [← h]
  exact mapsRootLines_weylQuotientHom
    (Subgroup.inclusion (componentMonomial_le_monomialSubgroup K χ i v j) g)

theorem ker_componentWeylHom :
    (componentWeylHom K χ i v j).ker =
      (componentTorus K χ i).subgroupOf (componentMonomial K χ i v j) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, componentWeylHom_eq_iff]
  exact ⟨fun h => mem_componentTorus_of_mapsRootLines_one hvj g.2 h,
    fun h => mapsRootLines_of_mem_torusGroup (componentTorus_le_torusGroup K χ i h)⟩

theorem range_componentWeylHom :
    (componentWeylHom K χ i v j).range = componentWeylGroup (componentRoots χ i) := by
  ext w
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨w', hw', h⟩ := exists_mapsRootLines_of_mem_componentMonomial hvj g.2
    rwa [componentWeylHom_eq_iff.2 h]
  · intro hw
    obtain ⟨g, hg, h⟩ := exists_mem_componentMonomial_mapsRootLines (K := K) hvj hw
    exact ⟨⟨g, hg⟩, componentWeylHom_eq_iff.2 h⟩

omit hvj in
theorem componentBorel_inf_componentMonomial :
    componentBorel K χ i ⊓ componentMonomial K χ i v j = componentTorus K χ i := by
  refine le_antisymm (fun g hg => ?_)
    (le_inf componentTorus_le_componentBorel componentTorus_le_componentMonomial)
  obtain ⟨hB, hN⟩ := Subgroup.mem_inf.1 hg
  have hH : g ∈ torusGroup τ K := by
    rw [← (borel_weyl_intersection τ K).1]
    exact Subgroup.mem_inf.2 ⟨componentBorel_le_borelGroup hB,
      componentMonomial_le_monomialSubgroup K χ i v j hN⟩
  exact Subgroup.mem_inf.2 ⟨componentBorel_le_componentRootSpan hB, hH⟩

omit hvj in
theorem mem_componentLifts
    {w : WeylGroup τ} {g : ModGL τ K} :
    g ∈ componentLifts K χ i v j w ↔ g ∈ componentMonomial K χ i v j ∧ MapsRootLines g w :=
  ⟨fun ⟨hg, h⟩ => ⟨hg, componentWeylHom_eq_iff.1 h⟩,
    fun ⟨hg, h⟩ => ⟨hg, componentWeylHom_eq_iff.2 h⟩⟩

theorem inv_mul_mem_componentTorus
    {w : WeylGroup τ} {g g' : ModGL τ K}
    (hg : g ∈ componentLifts K χ i v j w) (hg' : g' ∈ componentLifts K χ i v j w) :
    g⁻¹ * g' ∈ componentTorus K χ i := by
  obtain ⟨hgN, hgw⟩ := mem_componentLifts.1 hg
  obtain ⟨hgN', hgw'⟩ := mem_componentLifts.1 hg'
  refine mem_componentTorus_of_mapsRootLines_one hvj (mul_mem (inv_mem hgN) hgN') ?_
  simpa using hgw.inv.mul hgw'

omit hvj in
theorem mul_mem_componentLifts
    {w w' : WeylGroup τ} {g g' : ModGL τ K}
    (hg : g ∈ componentLifts K χ i v j w) (hg' : g' ∈ componentLifts K χ i v j w') :
    g * g' ∈ componentLifts K χ i v j (w * w') := by
  obtain ⟨hgN, hgw⟩ := mem_componentLifts.1 hg
  obtain ⟨hgN', hgw'⟩ := mem_componentLifts.1 hg'
  exact mem_componentLifts.2 ⟨mul_mem hgN hgN', hgw.mul hgw'⟩

omit hvj in
theorem inv_mem_componentLifts
    {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ componentLifts K χ i v j w) : g⁻¹ ∈ componentLifts K χ i v j w⁻¹ := by
  obtain ⟨hgN, hgw⟩ := mem_componentLifts.1 hg
  exact mem_componentLifts.2 ⟨inv_mem hgN, hgw.inv⟩

omit hvj in
theorem one_mem_componentLifts :
    (1 : ModGL τ K) ∈ componentLifts K χ i v j 1 :=
  mem_componentLifts.2 ⟨one_mem _, mapsRootLines_one⟩

theorem componentWeylElt_mem_componentLifts
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) :
    componentWeylElt K v j β ∈ componentLifts K χ i v j (rootReflection β) :=
  mem_componentLifts.2 ⟨componentWeylElt_mem_componentMonomial hβ,
    mapsRootLines_componentWeylElt (hvj β hβ)⟩

theorem componentWeylElt_mul_self_mem
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) :
    componentWeylElt K v j β * componentWeylElt K v j β ∈ componentTorus K χ i := by
  have h := mapsRootLines_componentWeylElt (K := K) (hvj β hβ)
  have h2 := h.mul h
  rw [rootReflection_mul_self (simpleRoots_isRoot hβ)] at h2
  have hN := componentWeylElt_mem_componentMonomial (K := K) (v := v) (j := j) hβ
  exact mem_componentTorus_of_mapsRootLines_one hvj (mul_mem hN hN) h2

theorem exists_componentWeylElt_mul_eq
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {b : ModGL τ K}
    (hb : b ∈ componentBorel K χ i) :
    ∃ b' ∈ componentBorel K χ i, ∃ c : K,
      componentWeylElt K v j β * b = b' * (componentWeylElt K v j β * componentXElt K v j β c) := by
  have hΨ := isRootComponent_componentRoots i
  have hβv := hvj β hβ
  rw [← SetLike.mem_coe, coe_componentBorel] at hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb
  set S₁ := posRoots (componentRoots χ i) \ {β}
  have hsplit : posRoots (componentRoots χ i) = S₁ ∪ {β} :=
    (Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ))).symm
  have hu' : u ∈ rootSpan τ K (S₁ ∪ {β}) := by
    rw [← hsplit]
    exact hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_rootSpan_eq K (S₁ := S₁) (S₂ := {β})
    (fun α hα => isRoot_height_pos_of_mem_posRoots hα.1)
    (fun α hα => by
      rw [Set.mem_singleton_iff.1 hα]
      exact isRoot_height_pos_of_mem_posRoots (simpleRoot_mem_posRoots hβ))
    Set.disjoint_sdiff_left
    (fun α hα γ hγ a a' ha ha' hr => by
      rw [← hsplit] at hα hγ ⊢
      exact mem_posRoots_of_nsmul_add hα hγ a a' ha ha' hr) hu'
  obtain ⟨c, rfl⟩ := exists_componentXElt_eq hβv hu₂
  set n := componentWeylElt K v j β
  have hnN : n ∈ componentMonomial K χ i v j := componentWeylElt_mem_componentMonomial hβ
  have hnt : n * t * n⁻¹ ∈ componentTorus K χ i := conj_mem_componentTorus hvj hnN ht
  have hnu : n * u₁ * n⁻¹ ∈ componentUnipotent K χ i := by
    have h := conj_mem_rootSpan_of_mapsRootLines (componentWeylElt_mem_monomialSubgroup K v j β)
      (mapsRootLines_componentWeylElt hβv) (S := S₁)
      (fun α hα => (isRoot_height_pos_of_mem_posRoots hα.1).1) hu₁
    refine rootSpan_mono ?_ h
    rintro _ ⟨α, ⟨hα, hne⟩, rfl⟩
    exact (rootReflection_mem_posRoots hΨ hβ hα hne).1
  refine ⟨n * t * n⁻¹ * (n * u₁ * n⁻¹), mul_mem (componentTorus_le_componentBorel hnt)
    (componentUnipotent_le_componentBorel hnu), c, ?_⟩
  group

theorem exists_componentWeylElt_mul_componentXElt_eq
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {c : K} (hc : c ≠ 0) :
    ∃ b₀ ∈ componentBorel K χ i, componentWeylElt K v j β * componentXElt K v j β c =
      b₀ * componentYElt K v j β c⁻¹ := by
  have hβv := hvj β hβ
  have h := componentWeylElt_mul_componentXElt (K := K) (v := v) (j := j) β (Units.mk0 c hc)
  rw [Units.val_inv_eq_inv_val, Units.val_mk0] at h
  refine ⟨_, mul_mem ?_ ?_, h⟩
  · exact componentUnipotent_le_componentBorel (rootSpan_mono
      (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ)) (componentXElt_mem hβv _))
  · exact componentTorus_le_componentBorel
      (canonicalRep_conj_torusElt_mem (by rw [hβv]; exact simpleRoots_subset hβ) _)

omit hvj in
theorem exists_mul_eq_mul_of_mem_componentLifts
    {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ componentLifts K χ i v j w) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : w⁻¹ • α ∈ posRoots (componentRoots χ i)) {x : ModGL τ K}
    (hx : x ∈ rootSpan τ K {α}) : ∃ b ∈ componentBorel K χ i, x * g = g * b := by
  obtain ⟨hgN, hgw⟩ := mem_componentLifts.1 hg
  have hgM := componentMonomial_le_monomialSubgroup K χ i v j hgN
  have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem hgM) hgw.inv (S := {α})
    (by rintro _ rfl; exact hα) hx
  rw [Set.image_singleton, inv_inv] at h
  exact ⟨g⁻¹ * x * g, componentUnipotent_le_componentBorel
    (rootSpan_mono (Set.singleton_subset_iff.2 hpos) h), by group⟩

end CFSG.LieType.Chevalley
