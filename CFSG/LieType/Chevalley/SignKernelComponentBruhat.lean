module

public import CFSG.LieType.Chevalley.SignKernelComponentBorel

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable
    {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
  {v : (Fin τ.rank → ℤ) → WeylGroup τ} {j : (Fin τ.rank → ℤ) → Fin τ.rank}

theorem mem_componentCell
    {w : WeylGroup τ} {x : ModGL τ K} :
    x ∈ componentCell K χ i v j w ↔ ∃ b ∈ componentBorel K χ i,
      ∃ g ∈ componentLifts K χ i v j w, ∃ b' ∈ componentBorel K χ i, b * g * b' = x := by
  simp only [componentCell, Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, g, hg, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, g, hg, b', hb', rfl⟩
  · rintro ⟨b, hb, g, hg, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, g, hg, rfl⟩, b', hb', rfl⟩

theorem borel_mul_mem_componentCell
    {w : WeylGroup τ} {b x : ModGL τ K}
    (hb : b ∈ componentBorel K χ i) (hx : x ∈ componentCell K χ i v j w) :
    b * x ∈ componentCell K χ i v j w := by
  obtain ⟨b₁, hb₁, g, hg, b₂, hb₂, rfl⟩ := mem_componentCell.1 hx
  exact mem_componentCell.2 ⟨b * b₁, mul_mem hb hb₁, g, hg, b₂, hb₂, by group⟩

theorem componentCell_subset_bruhatCell
    (w : WeylGroup τ) :
    componentCell K χ i v j w ⊆ bruhatCell τ K w := by
  intro x hx
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_componentCell.1 hx
  obtain ⟨hgN, hgw⟩ := mem_componentLifts.1 hg
  obtain ⟨w', k, hk, rfl⟩ :=
    monomialSubgroup_le_torusWeylCosets (componentMonomial_le_monomialSubgroup K χ i v j hgN)
  have hmaps : MapsRootLines (k * canonicalRep (coxeterSystem τ) K w') w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
  rw [← hmaps.unique hgw]
  exact mem_bruhatCell.2 ⟨b * k, mul_mem (componentBorel_le_borelGroup hb)
    (torusGroup_le_borelGroup hk), b', componentBorel_le_borelGroup hb', by group⟩

theorem disjoint_componentCell
    {w w' : WeylGroup τ} (h : w ≠ w') :
    Disjoint (componentCell K χ i v j w) (componentCell K χ i v j w') :=
  (disjoint_bruhatCell h).mono (componentCell_subset_bruhatCell w)
    (componentCell_subset_bruhatCell w')

variable (hvj : ∀ β ∈ simpleRoots (componentRoots χ i),
  v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
include hvj

theorem doubleCoset_eq_componentCell
    {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ componentLifts K χ i v j w) :
    (componentBorel K χ i : Set (ModGL τ K)) * {g} * (componentBorel K χ i : Set (ModGL τ K)) =
      componentCell K χ i v j w := by
  ext x
  rw [mem_componentCell]
  constructor
  · intro hx
    obtain ⟨b, hb, b', hb', e⟩ := DoubleCoset.mem_doubleCoset.1 hx
    exact ⟨b, hb, g, hg, b', hb', e.symm⟩
  · rintro ⟨b, hb, g', hg', b', hb', rfl⟩
    have ht := inv_mul_mem_componentTorus hvj hg hg'
    refine DoubleCoset.mem_doubleCoset.2 ⟨b, hb, g⁻¹ * g' * b',
      mul_mem (componentTorus_le_componentBorel ht) hb', by group⟩

theorem componentCell_subset_componentRootSpan
    (w : WeylGroup τ) :
    componentCell K χ i v j w ⊆ componentRootSpan K χ i := by
  intro x hx
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_componentCell.1 hx
  exact mul_mem (mul_mem (componentBorel_le_componentRootSpan hb)
    (componentMonomial_le_componentRootSpan hvj (mem_componentLifts.1 hg).1))
    (componentBorel_le_componentRootSpan hb')

theorem componentWeylElt_mul_mem_of_pos
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {w : WeylGroup τ}
    (hpos : w⁻¹ • β ∈ posRoots (componentRoots χ i)) {x : ModGL τ K}
    (hx : x ∈ componentCell K χ i v j w) :
    componentWeylElt K v j β * x ∈ componentCell K χ i v j (rootReflection β * w) := by
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_componentCell.1 hx
  obtain ⟨b'', hb'', c, hc⟩ := exists_componentWeylElt_mul_eq hvj hβ hb
  obtain ⟨b₁, hb₁, h₁⟩ := exists_mul_eq_mul_of_mem_componentLifts hg
    (simpleRoots_isRoot hβ) hpos (componentXElt_mem (hvj β hβ) c)
  have hlift := mul_mem_componentLifts (componentWeylElt_mem_componentLifts hvj hβ) hg
  refine mem_componentCell.2 ⟨b'', hb'', _, hlift, b₁ * b', mul_mem hb₁ hb', ?_⟩
  set n := componentWeylElt K v j β
  calc b'' * (n * g) * (b₁ * b') = b'' * n * (g * b₁) * b' := by group
    _ = b'' * n * (componentXElt K v j β c * g) * b' := by rw [← h₁]
    _ = b'' * (n * componentXElt K v j β c) * g * b' := by group
    _ = n * b * g * b' := by rw [← hc]
    _ = n * (b * g * b') := by group

theorem componentWeylElt_mul_mem_of_neg
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {w : WeylGroup τ}
    (hneg : w⁻¹ • (-β) ∈ posRoots (componentRoots χ i)) {x : ModGL τ K}
    (hx : x ∈ componentCell K χ i v j w) :
    componentWeylElt K v j β * x ∈ componentCell K χ i v j (rootReflection β * w) ∨
      componentWeylElt K v j β * x ∈ componentCell K χ i v j w := by
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_componentCell.1 hx
  obtain ⟨b'', hb'', c, hc⟩ := exists_componentWeylElt_mul_eq hvj hβ hb
  set n := componentWeylElt K v j β
  by_cases hc0 : c = 0
  ·
    left
    have hlift := mul_mem_componentLifts (componentWeylElt_mem_componentLifts hvj hβ) hg
    refine mem_componentCell.2 ⟨b'', hb'', _, hlift, b', hb', ?_⟩
    rw [hc0, componentXElt_zero, mul_one] at hc
    calc b'' * (n * g) * b' = b'' * n * g * b' := by group
      _ = n * b * g * b' := by rw [← hc]
      _ = n * (b * g * b') := by group
  ·
    right
    obtain ⟨b₀, hb₀, h₀⟩ := exists_componentWeylElt_mul_componentXElt_eq hvj hβ hc0
    obtain ⟨b₂, hb₂, h₂⟩ := exists_mul_eq_mul_of_mem_componentLifts hg
      (IsRoot.neg (simpleRoots_isRoot hβ)) hneg (componentYElt_mem (hvj β hβ) c⁻¹)
    refine mem_componentCell.2 ⟨b'' * b₀, mul_mem hb'' hb₀, g, hg, b₂ * b', mul_mem hb₂ hb', ?_⟩
    calc b'' * b₀ * g * (b₂ * b') = b'' * b₀ * (g * b₂) * b' := by group
      _ = b'' * b₀ * (componentYElt K v j β c⁻¹ * g) * b' := by rw [← h₂]
      _ = b'' * (b₀ * componentYElt K v j β c⁻¹) * g * b' := by group
      _ = b'' * (n * componentXElt K v j β c) * g * b' := by rw [← h₀]
      _ = n * b * g * b' := by rw [← hc]
      _ = n * (b * g * b') := by group

theorem exists_of_mem_componentCell_mul
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {w : WeylGroup τ} {y z : ModGL τ K}
    (hy : y ∈ componentCell K χ i v j (rootReflection β)) (hz : z ∈ componentCell K χ i v j w) :
    ∃ x ∈ componentCell K χ i v j w, ∃ b ∈ componentBorel K χ i,
      y * z = b * (componentWeylElt K v j β * x) := by
  obtain ⟨b₁, hb₁, g₁, hg₁, b₂, hb₂, rfl⟩ := mem_componentCell.1 hy
  have ht := inv_mul_mem_componentTorus hvj (componentWeylElt_mem_componentLifts hvj hβ) hg₁
  refine ⟨(componentWeylElt K v j β)⁻¹ * g₁ * b₂ * z, borel_mul_mem_componentCell
    (mul_mem (componentTorus_le_componentBorel ht) hb₂) hz, b₁, hb₁, by group⟩

theorem componentCell_rootReflection_mul_subset
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) (w : WeylGroup τ) :
    componentCell K χ i v j (rootReflection β * w) ⊆
      componentCell K χ i v j (rootReflection β) * componentCell K χ i v j w := by
  intro x hx
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_componentCell.1 hx
  have hn := componentWeylElt_mem_componentLifts hvj hβ (K := K)
  have hl : (componentWeylElt K v j β)⁻¹ * g ∈ componentLifts K χ i v j w := by
    have h := mul_mem_componentLifts (inv_mem_componentLifts hn) hg
    rwa [← mul_assoc, rootReflection_inv (simpleRoots_isRoot hβ),
      rootReflection_mul_self (simpleRoots_isRoot hβ), one_mul] at h
  refine Set.mem_mul.2 ⟨b * componentWeylElt K v j β,
    mem_componentCell.2 ⟨b, hb, _, hn, 1, one_mem _, by group⟩,
    (componentWeylElt K v j β)⁻¹ * g * b',
    mem_componentCell.2 ⟨1, one_mem _, _, hl, b', hb', by group⟩, by group⟩

theorem componentCell_mul_of_length_eq_add_one
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i))
    (h : componentLength (componentRoots χ i) (rootReflection β * w) =
      componentLength (componentRoots χ i) w + 1) :
    componentCell K χ i v j (rootReflection β) * componentCell K χ i v j w =
      componentCell K χ i v j (rootReflection β * w) := by
  have hpos := inv_smul_mem_posRoots_of_componentLength hβ hw h
  refine Set.Subset.antisymm (fun x hx => ?_) (componentCell_rootReflection_mul_subset hvj hβ w)
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
  obtain ⟨x, hx', b, hb, e⟩ := exists_of_mem_componentCell_mul hvj hβ hy hz
  rw [e]
  exact borel_mul_mem_componentCell hb (componentWeylElt_mul_mem_of_pos hvj hβ hpos hx')

theorem componentCell_mul_of_length_eq_sub_one
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i)) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (componentRoots χ i))
    (h : componentLength (componentRoots χ i) (rootReflection β * w) =
      componentLength (componentRoots χ i) w - 1) :
    componentCell K χ i v j (rootReflection β) * componentCell K χ i v j w =
      componentCell K χ i v j (rootReflection β * w) ∪ componentCell K χ i v j w := by
  have hneg := inv_smul_neg_mem_posRoots_of_componentLength hβ hw h
  refine Set.Subset.antisymm (fun x hx => ?_)
    (Set.union_subset (componentCell_rootReflection_mul_subset hvj hβ w) fun x hx => ?_)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨x, hx', b, hb, e⟩ := exists_of_mem_componentCell_mul hvj hβ hy hz
    rw [e]
    rcases componentWeylElt_mul_mem_of_neg hvj hβ hneg hx' with h' | h'
    · exact Or.inl (borel_mul_mem_componentCell hb h')
    · exact Or.inr (borel_mul_mem_componentCell hb h')
  ·
    obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_componentCell.1 hx
    obtain ⟨b₀, hb₀, h₀⟩ :=
      exists_componentWeylElt_mul_componentXElt_eq hvj hβ (one_ne_zero : (1 : K) ≠ 0)
    obtain ⟨b₂, hb₂, h₂⟩ := exists_mul_eq_mul_of_mem_componentLifts hg
      (IsRoot.neg (simpleRoots_isRoot hβ)) hneg (componentYElt_mem (hvj β hβ) (1 : K)⁻¹)
    have hn := componentWeylElt_mem_componentLifts hvj hβ (K := K)
    have hx1 : componentXElt K v j β 1 ∈ componentBorel K χ i :=
      componentUnipotent_le_componentBorel (rootSpan_mono
        (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ)) (componentXElt_mem (hvj β hβ) 1))
    set n := componentWeylElt K v j β
    refine Set.mem_mul.2 ⟨b * b₀⁻¹ * n * componentXElt K v j β 1,
      mem_componentCell.2 ⟨b * b₀⁻¹, mul_mem hb (inv_mem hb₀), n, hn, _, hx1, rfl⟩,
      g * (b₂⁻¹ * b'), mem_componentCell.2 ⟨1, one_mem _, g, hg, b₂⁻¹ * b',
        mul_mem (inv_mem hb₂) hb', by group⟩, ?_⟩
    calc b * b₀⁻¹ * n * componentXElt K v j β 1 * (g * (b₂⁻¹ * b')) =
        b * b₀⁻¹ * (n * componentXElt K v j β 1) * g * b₂⁻¹ * b' := by group
      _ = b * b₀⁻¹ * (b₀ * componentYElt K v j β (1 : K)⁻¹) * g * b₂⁻¹ * b' := by rw [h₀]
      _ = b * (componentYElt K v j β (1 : K)⁻¹ * g) * b₂⁻¹ * b' := by group
      _ = b * (g * b₂) * b₂⁻¹ * b' := by rw [h₂]
      _ = b * g * b' := by group

theorem componentRootSpan_le_of
    {H : Subgroup (ModGL τ K)} (hB : componentBorel K χ i ≤ H)
    (hN : componentMonomial K χ i v j ≤ H) : componentRootSpan K χ i ≤ H := by
  have hΨ := isRootComponent_componentRoots i
  refine iSup₂_le fun α hα => ?_
  obtain ⟨u, hu, β, hβ, e⟩ := exists_smul_simpleRoot hΨ hα
  obtain ⟨g, hgN, hgu⟩ := exists_mem_componentMonomial_mapsRootLines (K := K) hvj hu
  have hgM := componentMonomial_le_monomialSubgroup K χ i v j hgN
  intro x hx
  have hx' : x ∈ rootSpan τ K {α} := by
    rw [rootSpan, iSup_singleton]
    exact hx
  have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem hgM) hgu.inv (S := {α})
    (by rintro _ rfl; exact hΨ.isRoot _ hα) hx'
  rw [Set.image_singleton, inv_inv, e, inv_smul_smul] at h
  have hb : g⁻¹ * x * g ∈ H := hB (componentUnipotent_le_componentBorel
    (rootSpan_mono (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ)) h))
  have e' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e']
  exact mul_mem (mul_mem (hN hgN) hb) (inv_mem (hN hgN))

theorem componentRootSpan_eq_sup :
    componentRootSpan K χ i = componentBorel K χ i ⊔ componentMonomial K χ i v j :=
  le_antisymm (componentRootSpan_le_of hvj le_sup_left le_sup_right)
    (sup_le componentBorel_le_componentRootSpan (componentMonomial_le_componentRootSpan hvj))

theorem coe_componentRootSpan_eq_iUnion :
    (componentRootSpan K χ i : Set (ModGL τ K)) =
      ⋃ w ∈ componentWeylGroup (componentRoots χ i), componentCell K χ i v j w := by
  have hΨ := isRootComponent_componentRoots i
  set X := ⋃ w ∈ componentWeylGroup (componentRoots χ i), componentCell K χ i v j w
  have hmemX : ∀ {x : ModGL τ K}, x ∈ X ↔
      ∃ w ∈ componentWeylGroup (componentRoots χ i), x ∈ componentCell K χ i v j w := by
    intro x
    simp only [X, Set.mem_iUnion, exists_prop]
  refine Set.Subset.antisymm ?_
    (Set.iUnion₂_subset fun w _ => componentCell_subset_componentRootSpan hvj w)
  have hBX : ∀ b ∈ componentBorel K χ i, ∀ x ∈ X, b * x ∈ X := fun b hb x hx => by
    obtain ⟨w, hw, hxw⟩ := hmemX.1 hx
    exact hmemX.2 ⟨w, hw, borel_mul_mem_componentCell hb hxw⟩
  have hnX : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ x ∈ X,
      componentWeylElt K v j β * x ∈ X := by
    intro β hβ x hx
    obtain ⟨w, hw, hxw⟩ := hmemX.1 hx
    have hrw : rootReflection β * w ∈ componentWeylGroup (componentRoots χ i) :=
      mul_mem (rootReflection_mem_componentWeylGroup hβ) hw
    have hmem := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) β (simpleRoots_subset hβ)
    rcases mem_posRoots_or_mem_negRoots hΨ hmem with hp | hn
    · exact hmemX.2 ⟨_, hrw, componentWeylElt_mul_mem_of_pos hvj hβ hp hxw⟩
    · have hn' : w⁻¹ • (-β) ∈ posRoots (componentRoots χ i) := by
        rw [smul_neg]
        exact hn
      rcases componentWeylElt_mul_mem_of_neg hvj hβ hn' hxw with h | h
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
  have hBSt : componentBorel K χ i ≤ St := fun b hb =>
    ⟨fun x hx => hBX b hb x hx, fun x hx => hBX b⁻¹ (inv_mem hb) x hx⟩
  have hNSt : componentMonomial K χ i v j ≤ St := by
    refine (Subgroup.closure_le _).2 (Set.union_subset
      (fun t ht => hBSt (componentTorus_le_componentBorel ht)) ?_)
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨fun x hx => hnX β hβ x hx, fun x hx => ?_⟩
    have e : (componentWeylElt K v j β)⁻¹ * x =
        (componentWeylElt K v j β * componentWeylElt K v j β)⁻¹ *
          (componentWeylElt K v j β * x) := by group
    rw [e]
    exact hBX _ (inv_mem (componentTorus_le_componentBorel
      (componentWeylElt_mul_self_mem hvj hβ))) _ (hnX β hβ x hx)
  have hSSt := componentRootSpan_le_of hvj hBSt hNSt
  intro g hg
  have h1 : (1 : ModGL τ K) ∈ X := hmemX.2 ⟨1, one_mem _, mem_componentCell.2
    ⟨1, one_mem _, 1, one_mem_componentLifts, 1, one_mem _, by group⟩⟩
  simpa using (hSSt hg).1 1 h1

omit hvj in
variable (τ K χ i v j) in
theorem sign_kernel_root_component_Bruhat_structure
    (hvj : ∀ β ∈ simpleRoots (componentRoots χ i),
      v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) :
    (∀ x ∈ componentTorus K χ i, ∀ y ∈ componentTorus K χ i, x * y = y * x) ∧
    Group.IsNilpotent (componentUnipotent K χ i) ∧
    componentTorus K χ i ≤ Subgroup.normalizer (componentUnipotent K χ i : Set (ModGL τ K)) ∧
    componentTorus K χ i ⊓ componentUnipotent K χ i = ⊥ ∧
    (componentBorel K χ i : Set (ModGL τ K)) =
      (componentTorus K χ i : Set (ModGL τ K)) * (componentUnipotent K χ i : Set (ModGL τ K)) ∧
    componentBorel K χ i ≤ componentRootSpan K χ i ∧
    ((componentUnipotent K χ i).subgroupOf (componentBorel K χ i)).Normal ∧
    componentBorel K χ i ⊓ componentMonomial K χ i v j = componentTorus K χ i ∧
    componentTorus K χ i ≤ componentMonomial K χ i v j ∧
    (componentWeylHom K χ i v j).ker =
      (componentTorus K χ i).subgroupOf (componentMonomial K χ i v j) ∧
    (componentWeylHom K χ i v j).range = componentWeylGroup (componentRoots χ i) ∧
    (∀ w ∈ componentWeylGroup (componentRoots χ i), ∀ g (hg : g ∈ componentMonomial K χ i v j),
      componentWeylHom K χ i v j ⟨g, hg⟩ = w →
        (componentBorel K χ i : Set (ModGL τ K)) * {g} *
          (componentBorel K χ i : Set (ModGL τ K)) = componentCell K χ i v j w) ∧
    componentRootSpan K χ i = componentBorel K χ i ⊔ componentMonomial K χ i v j ∧
    (componentRootSpan K χ i : Set (ModGL τ K)) =
      ⋃ w ∈ componentWeylGroup (componentRoots χ i), componentCell K χ i v j w ∧
    (∀ w ∈ componentWeylGroup (componentRoots χ i), ∀ w' ∈ componentWeylGroup (componentRoots χ i),
      w ≠ w' → Disjoint (componentCell K χ i v j w) (componentCell K χ i v j w')) ∧
    (∀ β ∈ simpleRoots (componentRoots χ i), ∀ w ∈ componentWeylGroup (componentRoots χ i),
      componentLength (componentRoots χ i) (rootReflection β * w) =
        componentLength (componentRoots χ i) w + 1 →
      componentCell K χ i v j (rootReflection β) * componentCell K χ i v j w =
        componentCell K χ i v j (rootReflection β * w)) ∧
    ∀ β ∈ simpleRoots (componentRoots χ i), ∀ w ∈ componentWeylGroup (componentRoots χ i),
      componentLength (componentRoots χ i) (rootReflection β * w) =
        componentLength (componentRoots χ i) w - 1 →
      componentCell K χ i v j (rootReflection β) * componentCell K χ i v j w =
        componentCell K χ i v j (rootReflection β * w) ∪ componentCell K χ i v j w :=
  ⟨fun _ hx _ hy => mul_comm_of_mem_componentTorus hx hy, isNilpotent_componentUnipotent,
    componentTorus_le_normalizer, componentTorus_inf_componentUnipotent, coe_componentBorel,
    componentBorel_le_componentRootSpan, componentUnipotent_subgroupOf_normal,
    componentBorel_inf_componentMonomial, componentTorus_le_componentMonomial,
    ker_componentWeylHom hvj, range_componentWeylHom hvj,
    fun _ _ _ hg h => doubleCoset_eq_componentCell hvj ⟨hg, h⟩, componentRootSpan_eq_sup hvj,
    coe_componentRootSpan_eq_iUnion hvj, fun _ _ _ _ h => disjoint_componentCell h,
    fun _ hβ _ hw h => componentCell_mul_of_length_eq_add_one hvj hβ hw h,
    fun _ hβ _ hw h => componentCell_mul_of_length_eq_sub_one hvj hβ hw h⟩

end CFSG.LieType.Chevalley
