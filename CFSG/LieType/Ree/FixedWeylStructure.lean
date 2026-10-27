module

public import CFSG.LieType.Ree.FixedWeylStructureData
public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Ree.TitsWeyl

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable (t : ReeTag)

@[expose] def fixedRelLength
    (w : WeylGroup t.tag) : ℕ :=
  sInf {n | ∃ ω : List (Fin t.fixedOrbitCount), ω.length = n ∧
    (ω.map t.fixedOrbitElement).prod = w}

@[expose] def fixedRelElt
    (k : Fin t.fixedWeylOrder) : WeylGroup t.tag :=
  ((t.fixedRelWord k).map t.fixedOrbitElement).prod

variable {t}

theorem reeOrbitWord_eq (i : Fin t.tag.rank) :
    t.reeOrbitWord i = t.fixedOrbitWord (t.fixedOrbitIndex i) := by
  revert i
  cases t <;> decide

theorem blockElt_eq
    (i : Fin t.tag.rank) :
    t.blockElt i = t.fixedOrbitElement (t.fixedOrbitIndex i) := by
  rw [blockElt, reeOrbitWord_eq]
  rfl

theorem fixedOrbitElement_eq_blockElt
    (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j = t.blockElt (t.fixedOrbitRep j) := by
  rw [blockElt_eq, fixedOrbitIndex_fixedOrbitRep]

theorem range_blockElt
    : Set.range t.blockElt = Set.range t.fixedOrbitElement := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, (blockElt_eq i).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, (fixedOrbitElement_eq_blockElt j).symm⟩

theorem fixedOrbitElement_mul_self
    (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j * t.fixedOrbitElement j = 1 := by
  rw [fixedOrbitElement_eq_blockElt, blockElt_mul_self]

theorem fixedOrbitElement_inv
    (j : Fin t.fixedOrbitCount) :
    (t.fixedOrbitElement j)⁻¹ = t.fixedOrbitElement j :=
  inv_eq_of_mul_eq_one_right (fixedOrbitElement_mul_self j)

theorem fixedOrbitElement_mem
    (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j ∈ t.relWeylRee := by
  rw [fixedOrbitElement_eq_blockElt]
  exact reeOrbitWord_mem t _

theorem relWeylRee_eq_closure :
    t.relWeylRee = Subgroup.closure (Set.range t.fixedOrbitElement) := by
  refine le_antisymm (fun w hw => ?_) ((Subgroup.closure_le _).2 ?_)
  · rw [← range_blockElt]
    exact mem_closure_blockElt _ w rfl hw
  · rintro _ ⟨j, rfl⟩
    exact fixedOrbitElement_mem j

theorem fixedOrbitElement_smul
    (j : Fin t.fixedOrbitCount) (v : Fin t.tag.rank → ℤ) :
    t.fixedOrbitElement j • v = (t.fixedOrbitWord j).foldr (reflect t.tag) v :=
  CFSG.LieType.Ree.wordProd_smul _ v

theorem mem_fixedOrbitRoots_iff {j : Fin t.fixedOrbitCount} {α : Fin t.tag.rank → ℤ} :
    α ∈ t.fixedOrbitRoots j ↔
      IsRoot t.tag α ∧ 0 < height α ∧ ∀ i, t.fixedOrbitIndex i ≠ j → α i = 0 := by
  rw [mem_fixedOrbitRoots]
  simp only [mem_fixedOrbitSet]
  exact and_assoc

theorem mem_fixedOrbitComplementRoots_iff {j : Fin t.fixedOrbitCount}
    {α : Fin t.tag.rank → ℤ} :
    α ∈ t.fixedOrbitComplementRoots j ↔
      IsRoot t.tag α ∧ 0 < height α ∧ ∃ i, t.fixedOrbitIndex i ≠ j ∧ α i ≠ 0 := by
  rw [fixedOrbitComplementRoots_eq, Set.mem_sdiff, Set.mem_ofPred_eq, mem_fixedOrbitRoots_iff]
  constructor
  · rintro ⟨⟨hα, hpos⟩, h⟩
    refine ⟨hα, hpos, ?_⟩
    by_contra! h'
    exact h ⟨hα, hpos, h'⟩
  · rintro ⟨hα, hpos, i, hi, hαi⟩
    exact ⟨⟨hα, hpos⟩, fun h => hαi (h.2.2 i hi)⟩

theorem fixedOrbitRoots_subset (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitRoots j ⊆ {α | IsRoot t.tag α ∧ 0 < height α} :=
  fun _ hα => ⟨(mem_fixedOrbitRoots_iff.1 hα).1, (mem_fixedOrbitRoots_iff.1 hα).2.1⟩

theorem finite_fixedOrbitRoots
    (j : Fin t.fixedOrbitCount) : (t.fixedOrbitRoots j).Finite :=
  (finite_setOf_isRoot t.tag).subset fun _ hα => (mem_fixedOrbitRoots_iff.1 hα).1

theorem single_mem_fixedOrbitRoots
    (j : Fin t.fixedOrbitCount) :
    (Pi.single (t.fixedOrbitRep j) 1 : Fin t.tag.rank → ℤ) ∈ t.fixedOrbitRoots j := by
  refine mem_fixedOrbitRoots_iff.2 ⟨isRoot_single _ _, by rw [height_single]; exact one_pos,
    fun i hi => Pi.single_eq_of_ne ?_ _⟩
  rintro rfl
  exact hi (fixedOrbitIndex_fixedOrbitRep j)

theorem neg_smul_mem_fixedOrbitRoots
    {j : Fin t.fixedOrbitCount} {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ t.fixedOrbitRoots j) : -(t.fixedOrbitElement j • α) ∈ t.fixedOrbitRoots j := by
  obtain ⟨hroot, hpos, hsupp⟩ := mem_fixedOrbitRoots_iff.1 hα
  have hr : IsRoot t.tag (-(t.fixedOrbitElement j • α)) := IsRoot.neg (IsRoot.smul hroot _)
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hroot
  obtain ⟨h1, h2⟩ := fixedOrbitWord_root_check_mem t k hk j hpos hsupp
  rw [fixedOrbitElement_smul] at hr ⊢
  exact mem_fixedOrbitRoots_iff.2 ⟨hr, h1, fun i hi => by rw [Pi.neg_apply, h2 i hi, neg_zero]⟩

theorem smul_mem_fixedOrbitComplementRoots
    {j : Fin t.fixedOrbitCount}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ t.fixedOrbitComplementRoots j) :
    t.fixedOrbitElement j • α ∈ t.fixedOrbitComplementRoots j := by
  obtain ⟨hroot, hpos, hsupp⟩ := mem_fixedOrbitComplementRoots_iff.1 hα
  have hr : IsRoot t.tag (t.fixedOrbitElement j • α) := IsRoot.smul hroot _
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hroot
  obtain ⟨h1, h2⟩ := fixedOrbitWord_root_check_not_mem t k hk j hpos hsupp
  rw [fixedOrbitElement_smul] at hr ⊢
  exact mem_fixedOrbitComplementRoots_iff.2 ⟨hr, h1, h2⟩

theorem fixedOrbitElement_smul_smul
    (j : Fin t.fixedOrbitCount) (v : Fin t.tag.rank → ℤ) :
    t.fixedOrbitElement j • t.fixedOrbitElement j • v = v := by
  rw [← mul_smul, fixedOrbitElement_mul_self, one_smul]

theorem image_fixedOrbitRoots
    (j : Fin t.fixedOrbitCount) :
    (t.fixedOrbitElement j • ·) '' t.fixedOrbitRoots j = Neg.neg '' t.fixedOrbitRoots j := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨_, neg_smul_mem_fixedOrbitRoots hα, neg_neg _⟩
  · rintro ⟨α, hα, rfl⟩
    refine ⟨_, neg_smul_mem_fixedOrbitRoots hα, ?_⟩
    simp only [smul_neg, fixedOrbitElement_smul_smul]

theorem bijOn_fixedOrbitComplementRoots
    (j : Fin t.fixedOrbitCount) :
    Set.BijOn (t.fixedOrbitElement j • ·) (t.fixedOrbitComplementRoots j)
      (t.fixedOrbitComplementRoots j) :=
  Set.InvOn.bijOn ⟨fun v _ => fixedOrbitElement_smul_smul j v,
      fun v _ => fixedOrbitElement_smul_smul j v⟩
    (fun _ hα => smul_mem_fixedOrbitComplementRoots hα)
    (fun _ hα => smul_mem_fixedOrbitComplementRoots hα)

theorem fixedOrbitRoots_eq_list (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitRoots j = {α | α ∈ t.fixedOrbitRootList j} := by
  ext α
  constructor
  · intro hα
    obtain ⟨hroot, hpos, hsupp⟩ := mem_fixedOrbitRoots_iff.1 hα
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hroot
    exact ((fixedOrbitRootList_check t).1 k hk j).1 ⟨hpos, hsupp⟩
  · intro hα
    obtain ⟨k, hk, rfl⟩ := (fixedOrbitRootList_check t).2 j α hα
    obtain ⟨hpos, hsupp⟩ := ((fixedOrbitRootList_check t).1 k hk j).2 hα
    exact mem_fixedOrbitRoots_iff.2
      ⟨RootCertificate.isRoot_root t.tag.rootCertificate_check k hk, hpos, hsupp⟩

theorem ncard_fixedOrbitRoots (j : Fin t.fixedOrbitCount) :
    (t.fixedOrbitRoots j).ncard = (t.fixedOrbitRootList j).length := by
  rw [fixedOrbitRoots_eq_list, ← List.coe_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (fixedOrbitRootList_nodup t j)]

theorem length_mul_fixedOrbitElement_of_pos
    {w : WeylGroup t.tag} {j : Fin t.fixedOrbitCount}
    (hpos : ∀ α ∈ t.fixedOrbitRoots j, 0 < height (w • α)) :
    (coxeterSystem t.tag).length (w * t.fixedOrbitElement j) =
      (coxeterSystem t.tag).length w + (t.fixedOrbitRoots j).ncard := by
  have himage : ∀ β ∈ inversionSet w,
      t.fixedOrbitElement j • β ∈ t.fixedOrbitComplementRoots j := by
    rintro β ⟨hβ, hβpos, -, hneg⟩
    refine smul_mem_fixedOrbitComplementRoots (mem_fixedOrbitComplementRoots_iff.2 ⟨hβ, hβpos, ?_⟩)
    by_contra! h
    have := hpos β (mem_fixedOrbitRoots_iff.2 ⟨hβ, hβpos, h⟩)
    omega
  have hI : inversionSet (w * t.fixedOrbitElement j) =
      t.fixedOrbitRoots j ∪ (t.fixedOrbitElement j • ·) '' inversionSet w := by
    ext α
    simp only [inversionSet, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, mul_smul]
    constructor
    · rintro ⟨hα, hαpos, hr, hneg⟩
      by_cases hE : α ∈ t.fixedOrbitRoots j
      · exact Or.inl hE
      · have hS : α ∈ t.fixedOrbitComplementRoots j := by
          rw [fixedOrbitComplementRoots_eq]
          exact ⟨⟨hα, hαpos⟩, hE⟩
        obtain ⟨hzα, hzαpos, -⟩ :=
          mem_fixedOrbitComplementRoots_iff.1 (smul_mem_fixedOrbitComplementRoots hS)
        exact Or.inr ⟨t.fixedOrbitElement j • α, ⟨hzα, hzαpos, hr, hneg⟩,
          fixedOrbitElement_smul_smul j α⟩
    · rintro (hE | ⟨β, hβ, rfl⟩)
      · obtain ⟨hα, hαpos, -⟩ := mem_fixedOrbitRoots_iff.1 hE
        have h := hpos _ (neg_smul_mem_fixedOrbitRoots hE)
        rw [smul_neg, height_neg] at h
        exact ⟨hα, hαpos, IsRoot.smul (IsRoot.smul hα _) _, by omega⟩
      · obtain ⟨hzβ, hzβpos, -⟩ := mem_fixedOrbitComplementRoots_iff.1 (himage β hβ)
        rw [fixedOrbitElement_smul_smul]
        exact ⟨hzβ, hzβpos, hβ.2.2⟩
  have hdisj : Disjoint (t.fixedOrbitRoots j) ((t.fixedOrbitElement j • ·) '' inversionSet w) := by
    rw [Set.disjoint_left]
    rintro α hE ⟨β, hβ, rfl⟩
    have h := himage β hβ
    rw [fixedOrbitComplementRoots_eq] at h
    exact h.2 hE
  rw [(weyl_inversion_length _).1, (weyl_inversion_length _).1, hI,
    Set.ncard_union_eq hdisj (finite_fixedOrbitRoots j) ((inversionSet_finite w).image _),
    Set.ncard_image_of_injective _ (MulAction.injective (t.fixedOrbitElement j)), add_comm]

theorem length_mul_fixedOrbitElement_of_neg
    {w : WeylGroup t.tag} {j : Fin t.fixedOrbitCount}
    (hneg : ∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0) :
    (coxeterSystem t.tag).length (w * t.fixedOrbitElement j) + (t.fixedOrbitRoots j).ncard =
      (coxeterSystem t.tag).length w := by
  have h := length_mul_fixedOrbitElement_of_pos (w := w * t.fixedOrbitElement j) (j := j)
    fun α hα => by
      have := hneg _ (neg_smul_mem_fixedOrbitRoots hα)
      rw [smul_neg, height_neg, ← mul_smul] at this
      omega
  rw [mul_assoc, fixedOrbitElement_mul_self, mul_one] at h
  exact h.symm

theorem length_fixedOrbitElement
    (j : Fin t.fixedOrbitCount) :
    (coxeterSystem t.tag).length (t.fixedOrbitElement j) = (t.fixedOrbitRoots j).ncard := by
  have h := length_mul_fixedOrbitElement_of_pos (w := 1) (j := j) fun α hα => by
    rw [one_smul]
    exact (mem_fixedOrbitRoots_iff.1 hα).2.1
  rwa [one_mul, CoxeterSystem.length_one, zero_add] at h

theorem fixedOrbitElement_ne_one
    (j : Fin t.fixedOrbitCount) : t.fixedOrbitElement j ≠ 1 := by
  intro h
  have := (mem_fixedOrbitRoots_iff.1 (neg_smul_mem_fixedOrbitRoots
    (single_mem_fixedOrbitRoots j))).2.1
  rw [h, one_smul, height_neg, height_single] at this
  omega

theorem orderOf_fixedOrbitElement
    (j : Fin t.fixedOrbitCount) :
    orderOf (t.fixedOrbitElement j) = 2 :=
  orderOf_eq_prime (by rw [sq, fixedOrbitElement_mul_self]) (fixedOrbitElement_ne_one j)

theorem height_smul_neg_of_mem_fixedOrbitRoots
    {w : WeylGroup t.tag} {j : Fin t.fixedOrbitCount}
    (hw : ∀ i, t.fixedOrbitIndex i = j → height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0)
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ t.fixedOrbitRoots j) : height (w • α) < 0 := by
  obtain ⟨hroot, hpos, hsupp⟩ := mem_fixedOrbitRoots_iff.1 hα
  refine height_smul_neg_of_support (J := Finset.univ.filter fun i => t.fixedOrbitIndex i = j)
    (fun i hi => hw i (Finset.mem_filter.1 hi).2) (fun i hi => hsupp i fun h => hi ?_)
    ((IsRoot.height_pos_iff hroot).1 hpos) hroot.ne_zero
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩

theorem height_smul_single_neg_iff
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {i : Fin t.tag.rank} {j : Fin t.fixedOrbitCount} (hi : t.fixedOrbitIndex i = j) :
    height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 ↔
      height (w • (Pi.single (t.fixedOrbitRep j) 1 : Fin t.tag.rank → ℤ)) < 0 := by
  rcases (fixedOrbitIndex_eq_iff i j).1 hi with rfl | rfl
  · rfl
  · refine ⟨fun h => ?_, height_smul_perm_neg hw⟩
    have := height_smul_perm_neg hw h
    rwa [perm_perm] at this

theorem height_smul_neg_iff_of_mem_fixedOrbitRoots
    {w : WeylGroup t.tag}
    (hw : w ∈ t.relWeylRee) {j : Fin t.fixedOrbitCount} {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ t.fixedOrbitRoots j) :
    height (w • α) < 0 ↔
      height (w • (Pi.single (t.fixedOrbitRep j) 1 : Fin t.tag.rank → ℤ)) < 0 := by
  constructor
  · intro h
    by_contra hpos
    have hneg : height ((t.negOne * w) • α) < 0 := height_smul_neg_of_mem_fixedOrbitRoots
      (fun i hi => by
        have h1 := (height_smul_single_neg_iff hw hi).not.2 hpos
        have h2 := (IsRoot.smul (isRoot_single t.tag i) w).height_ne_zero
        rw [mul_smul, negOne_smul, height_neg]
        omega) hα
    rw [mul_smul, negOne_smul, height_neg] at hneg
    omega
  · intro h
    exact height_smul_neg_of_mem_fixedOrbitRoots
      (fun i hi => (height_smul_single_neg_iff hw hi).2 h) hα

theorem height_smul_pos_iff_of_mem_fixedOrbitRoots
    {w : WeylGroup t.tag}
    (hw : w ∈ t.relWeylRee) {j : Fin t.fixedOrbitCount} {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ t.fixedOrbitRoots j) :
    0 < height (w • α) ↔
      0 < height (w • (Pi.single (t.fixedOrbitRep j) 1 : Fin t.tag.rank → ℤ)) := by
  have h := height_smul_neg_iff_of_mem_fixedOrbitRoots hw hα
  have h1 := (IsRoot.smul (mem_fixedOrbitRoots_iff.1 hα).1 w).height_ne_zero
  have h2 := (IsRoot.smul (isRoot_single t.tag (t.fixedOrbitRep j)) w).height_ne_zero
  omega

theorem fixedOrbitRoots_sign
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (j : Fin t.fixedOrbitCount) :
    (∀ α ∈ t.fixedOrbitRoots j, 0 < height (w • α)) ∨
      ∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0 := by
  by_cases h : height (w • (Pi.single (t.fixedOrbitRep j) 1 : Fin t.tag.rank → ℤ)) < 0
  · exact Or.inr fun α hα => (height_smul_neg_iff_of_mem_fixedOrbitRoots hw hα).2 h
  · refine Or.inl fun α hα => (height_smul_pos_iff_of_mem_fixedOrbitRoots hw hα).2 ?_
    have := (IsRoot.smul (isRoot_single t.tag (t.fixedOrbitRep j)) w).height_ne_zero
    omega

theorem exists_fixedOrbitRoots_neg
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) (h1 : w ≠ 1) :
    ∃ j, ∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0 := by
  obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one h1
  exact ⟨t.fixedOrbitIndex i, fun α hα => (height_smul_neg_iff_of_mem_fixedOrbitRoots hw hα).2
    ((height_smul_single_neg_iff hw rfl).1 hi)⟩

theorem list_prod_map_fixedOrbitElement
    (ω : List (Fin t.fixedOrbitCount)) :
    (ω.map t.fixedOrbitElement).prod =
      (coxeterSystem t.tag).wordProd (ω.flatMap t.fixedOrbitWord) := by
  induction ω with
  | nil => rw [List.map_nil, List.prod_nil, List.flatMap_nil, CoxeterSystem.wordProd_nil]
  | cons j ω ih =>
    rw [List.map_cons, List.prod_cons, ih, List.flatMap_cons, CoxeterSystem.wordProd_append]
    rfl

theorem simpleImages_fixedRelElt
    (k : Fin t.fixedWeylOrder) :
    simpleImages (t.fixedRelElt k) = t.fixedRelMat k := by
  rw [fixedRelElt, list_prod_map_fixedOrbitElement, simpleImages_wordProd,
    wordImages_fixedRelWord]

theorem fixedRelElt_injective :
    Function.Injective t.fixedRelElt := fun k k' h =>
  fixedRelMat_injective t (by rw [← simpleImages_fixedRelElt, h, simpleImages_fixedRelElt])

theorem fixedRelElt_mul
    (k : Fin t.fixedWeylOrder) (j : Fin t.fixedOrbitCount) :
    t.fixedRelElt k * t.fixedOrbitElement j = t.fixedRelElt (t.fixedRelRight k j) := by
  refine simpleImages_injective ?_
  rw [simpleImages_fixedRelElt, ← wordImages_fixedRelWord_append, ← simpleImages_wordProd,
    CoxeterSystem.wordProd_append, ← list_prod_map_fixedOrbitElement]
  rfl

theorem fixedRelElt_mem
    (k : Fin t.fixedWeylOrder) : t.fixedRelElt k ∈ t.relWeylRee :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact fixedOrbitElement_mem j

theorem exists_fixedRelElt_eq_one :
    ∃ k : Fin t.fixedWeylOrder, t.fixedRelElt k = 1 ∧ (t.fixedRelWord k).length = 0 := by
  obtain ⟨k, hk⟩ := fixedRelWord_zero t
  exact ⟨k, by rw [fixedRelElt, hk, List.map_nil, List.prod_nil], by rw [hk, List.length_nil]⟩

theorem exists_fixedRelElt_eq
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    ∃ k, t.fixedRelElt k = w := by
  rw [relWeylRee_eq_closure] at hw
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨_, (exists_fixedRelElt_eq_one (t := t)).choose_spec.1⟩
  | mul_right x _ y hy ih =>
    obtain ⟨k, rfl⟩ := ih
    obtain ⟨j, rfl⟩ := hy
    exact ⟨_, (fixedRelElt_mul k j).symm⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨k, rfl⟩ := ih
    obtain ⟨j, rfl⟩ := hy
    exact ⟨_, by rw [fixedOrbitElement_inv, fixedRelElt_mul]⟩

theorem card_relWeylRee :
    Nat.card t.relWeylRee = t.fixedWeylOrder := by
  have hbij : Function.Bijective fun k : Fin t.fixedWeylOrder =>
      (⟨t.fixedRelElt k, fixedRelElt_mem k⟩ : t.relWeylRee) :=
    ⟨fun k k' h => fixedRelElt_injective (congrArg Subtype.val h), fun w => by
      obtain ⟨k, hk⟩ := exists_fixedRelElt_eq w.2
      exact ⟨k, Subtype.ext hk⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem fixedRelLength_le
    {ω : List (Fin t.fixedOrbitCount)} {w : WeylGroup t.tag}
    (h : (ω.map t.fixedOrbitElement).prod = w) : t.fixedRelLength w ≤ ω.length :=
  Nat.sInf_le ⟨ω, rfl, h⟩

theorem exists_fixedRelElt_of_word
    (ω : List (Fin t.fixedOrbitCount)) :
    ∃ k, t.fixedRelElt k = (ω.map t.fixedOrbitElement).prod ∧
      (t.fixedRelWord k).length ≤ ω.length := by
  induction ω using List.reverseRecOn with
  | nil =>
    obtain ⟨k, hk, hlen⟩ := exists_fixedRelElt_eq_one (t := t)
    exact ⟨k, by rw [hk, List.map_nil, List.prod_nil], by rw [hlen]; exact le_rfl⟩
  | append_singleton ω j ih =>
    obtain ⟨k, hk, hlen⟩ := ih
    refine ⟨t.fixedRelRight k j, ?_, ?_⟩
    · rw [← fixedRelElt_mul, hk, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton]
    · have h := fixedRelRight_length t k j
      rw [List.length_append, List.length_singleton]
      split_ifs at h <;> omega

theorem fixedRelLength_fixedRelElt
    (k : Fin t.fixedWeylOrder) :
    t.fixedRelLength (t.fixedRelElt k) = (t.fixedRelWord k).length := by
  refine le_antisymm (fixedRelLength_le rfl) ?_
  obtain ⟨ω, hω, hprod⟩ := Nat.sInf_mem (s := {n | ∃ ω : List (Fin t.fixedOrbitCount),
    ω.length = n ∧ (ω.map t.fixedOrbitElement).prod = t.fixedRelElt k}) ⟨_, _, rfl, rfl⟩
  obtain ⟨k', hk', hlen⟩ := exists_fixedRelElt_of_word ω
  rw [hprod] at hk'
  obtain rfl := fixedRelElt_injective hk'
  exact hlen.trans hω.le

theorem list_prod_map_reverse
    (ω : List (Fin t.fixedOrbitCount)) :
    (ω.reverse.map t.fixedOrbitElement).prod = ((ω.map t.fixedOrbitElement).prod)⁻¹ := by
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse]
  simp only [Function.comp_def, fixedOrbitElement_inv]

theorem fixedRelLength_inv
    (w : WeylGroup t.tag) :
    t.fixedRelLength w⁻¹ = t.fixedRelLength w := by
  have key : ∀ u : WeylGroup t.tag, ∀ n, (∃ ω : List (Fin t.fixedOrbitCount), ω.length = n ∧
      (ω.map t.fixedOrbitElement).prod = u) →
      ∃ ω : List (Fin t.fixedOrbitCount), ω.length = n ∧
        (ω.map t.fixedOrbitElement).prod = u⁻¹ := by
    rintro u n ⟨ω, rfl, rfl⟩
    exact ⟨ω.reverse, List.length_reverse, list_prod_map_reverse ω⟩
  unfold fixedRelLength
  congr 1
  ext n
  exact ⟨fun h => by simpa using key _ n h, key w n⟩

theorem fixedRelLength_mul_fixedOrbitElement
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (j : Fin t.fixedOrbitCount) :
    if 0 < height (w • (Pi.single (t.fixedOrbitRep j) 1 : Fin t.tag.rank → ℤ)) then
      t.fixedRelLength (w * t.fixedOrbitElement j) = t.fixedRelLength w + 1
    else t.fixedRelLength (w * t.fixedOrbitElement j) + 1 = t.fixedRelLength w := by
  obtain ⟨k, rfl⟩ := exists_fixedRelElt_eq hw
  have h := fixedRelRight_length t k j
  rw [← simpleImages_fixedRelElt, sum_getD_simpleImages] at h
  rwa [fixedRelElt_mul, fixedRelLength_fixedRelElt, fixedRelLength_fixedRelElt]

theorem lengths_mul_fixedOrbitElement_of_pos
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {j : Fin t.fixedOrbitCount} (hpos : ∀ α ∈ t.fixedOrbitRoots j, 0 < height (w • α)) :
    t.fixedRelLength (w * t.fixedOrbitElement j) = t.fixedRelLength w + 1 ∧
      (coxeterSystem t.tag).length (w * t.fixedOrbitElement j) =
        (coxeterSystem t.tag).length w + (t.fixedOrbitRoots j).ncard := by
  have h := fixedRelLength_mul_fixedOrbitElement hw j
  rw [ite_eq_left (hpos _ (single_mem_fixedOrbitRoots j))] at h
  exact ⟨h, length_mul_fixedOrbitElement_of_pos hpos⟩

theorem lengths_mul_fixedOrbitElement_of_neg
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {j : Fin t.fixedOrbitCount} (hneg : ∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0) :
    t.fixedRelLength (w * t.fixedOrbitElement j) + 1 = t.fixedRelLength w ∧
      (coxeterSystem t.tag).length (w * t.fixedOrbitElement j) + (t.fixedOrbitRoots j).ncard =
        (coxeterSystem t.tag).length w := by
  have h := fixedRelLength_mul_fixedOrbitElement hw j
  rw [ite_eq_right (not_lt.2 (hneg _ (single_mem_fixedOrbitRoots j)).le)] at h
  exact ⟨h, length_mul_fixedOrbitElement_of_neg hneg⟩

theorem fixedOrbitElement_mul_eq_inv
    (w : WeylGroup t.tag) (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j * w = (w⁻¹ * t.fixedOrbitElement j)⁻¹ := by
  rw [mul_inv_rev, fixedOrbitElement_inv, inv_inv]

theorem lengths_fixedOrbitElement_mul_of_pos
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {j : Fin t.fixedOrbitCount} (hpos : ∀ α ∈ t.fixedOrbitRoots j, 0 < height (w⁻¹ • α)) :
    t.fixedRelLength (t.fixedOrbitElement j * w) = t.fixedRelLength w + 1 ∧
      (coxeterSystem t.tag).length (t.fixedOrbitElement j * w) =
        (coxeterSystem t.tag).length w + (t.fixedOrbitRoots j).ncard := by
  obtain ⟨h1, h2⟩ := lengths_mul_fixedOrbitElement_of_pos (inv_mem hw) hpos
  rw [fixedOrbitElement_mul_eq_inv, fixedRelLength_inv, h1, fixedRelLength_inv,
    CoxeterSystem.length_inv, h2, CoxeterSystem.length_inv]
  exact ⟨rfl, rfl⟩

theorem lengths_fixedOrbitElement_mul_of_neg
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {j : Fin t.fixedOrbitCount} (hneg : ∀ α ∈ t.fixedOrbitRoots j, height (w⁻¹ • α) < 0) :
    t.fixedRelLength (t.fixedOrbitElement j * w) + 1 = t.fixedRelLength w ∧
      (coxeterSystem t.tag).length (t.fixedOrbitElement j * w) + (t.fixedOrbitRoots j).ncard =
        (coxeterSystem t.tag).length w := by
  obtain ⟨h1, h2⟩ := lengths_mul_fixedOrbitElement_of_neg (inv_mem hw) hneg
  rw [fixedRelLength_inv] at h1
  rw [CoxeterSystem.length_inv] at h2
  rw [fixedOrbitElement_mul_eq_inv, fixedRelLength_inv, CoxeterSystem.length_inv]
  exact ⟨h1, h2⟩

theorem fixedOrbitElement_mem_fixedOrbitWeyl
    (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j ∈ t.fixedOrbitWeyl j :=
  wordProd_mem_parabolicWeylGroup fun i hi =>
    (mem_fixedOrbitSet j i).2 (fixedOrbitIndex_of_mem_fixedOrbitWord j i hi)

theorem fixedOrbitWeyl_inter_relWeylRee
    (j : Fin t.fixedOrbitCount) :
    (t.fixedOrbitWeyl j : Set (WeylGroup t.tag)) ∩ t.relWeylRee = {1, t.fixedOrbitElement j} := by
  ext w
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hW, hw⟩
    obtain ⟨k, rfl⟩ := exists_fixedRelElt_eq hw
    rcases fixedRelMat_parabolic t k j with h | h | ⟨l, i, hi, hne⟩
    · left
      rw [fixedRelElt, h, List.map_nil, List.prod_nil]
    · right
      rw [fixedRelElt, h, List.map_singleton, List.prod_singleton]
    · refine absurd ?_ hne
      rw [← simpleImages_fixedRelElt, getD_simpleImages]
      exact smul_apply_of_mem_parabolicWeylGroup hW _ fun h => hi ((mem_fixedOrbitSet j i).1 h)
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, one_mem _⟩
    · exact ⟨fixedOrbitElement_mem_fixedOrbitWeyl j, fixedOrbitElement_mem j⟩

theorem smul_longest
    {w₀ : WeylGroup t.tag}
    (h : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (v : Fin t.tag.rank → ℤ) : w₀ • v = -v := by
  have hneg : ReversesSigns t.negOne := fun α _ hpos => by
    rw [negOne_smul, height_neg]
    omega
  rw [(reversesSigns_of_forall_length_le h).eq hneg, negOne_smul]

theorem longest_mem_relWeylRee
    {w₀ : WeylGroup t.tag}
    (h : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    w₀ ∈ t.relWeylRee := by
  have h' : ∀ w, (coxeterSystem t.tag).length w ≤
      (coxeterSystem t.tag).length (t.weylPerm w₀) := fun w => by
    rw [length_weylPerm]
    exact h w
  exact (reversesSigns_of_forall_length_le h').eq (reversesSigns_of_forall_length_le h)

@[expose] def altWord : Fin F4.fixedOrbitCount → ℕ → List (Fin F4.fixedOrbitCount)
  | _, 0 => []
  | j, n + 1 => j :: altWord j.rev n

theorem length_altWord (j : Fin F4.fixedOrbitCount) (n : ℕ) : (altWord j n).length = n := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => rw [altWord, List.length_cons, ih]

theorem eq_rev_of_ne : ∀ a b : Fin F4.fixedOrbitCount, a ≠ b → b = a.rev := by
  decide

theorem eq_altWord : ∀ ω : List (Fin F4.fixedOrbitCount), ω.IsChain (· ≠ ·) →
    ∀ j, ω.head? = some j → ω = altWord j ω.length
  | [], _, _, h => absurd h (by simp)
  | [a], _, j, h => by
    rw [List.head?_cons, Option.some.injEq] at h
    subst h
    rfl
  | a :: b :: ω, hc, j, h => by
    rw [List.head?_cons, Option.some.injEq] at h
    subst h
    rw [List.isChain_cons_cons] at hc
    have h1 := eq_altWord (b :: ω) hc.2 b rfl
    have hb := eq_rev_of_ne a b hc.1
    calc a :: b :: ω = a :: altWord b (b :: ω).length := by rw [← h1]
      _ = altWord a (a :: b :: ω).length := by rw [hb]; rfl

theorem altWord_mem_table : ∀ j : Fin F4.fixedOrbitCount, ∀ n < 9,
    ∃ k : Fin F4.fixedWeylOrder, F4.fixedRelWord k = altWord j n ∨
      (j.val = 1 ∧ n = 8 ∧ F4.fixedRelWord k = altWord j.rev n) := by
  decide

theorem wordImages_altWord_eight (j : Fin F4.fixedOrbitCount) :
    wordImages F4.tag ((altWord j 8).flatMap F4.fixedOrbitWord) =
      wordImages F4.tag ((altWord j.rev 8).flatMap F4.fixedOrbitWord) := by
  revert j
  decide +kernel

theorem wordImages_altWord_eight_sixteen :
    wordImages F4.tag ((altWord ⟨0, by decide⟩ 8).flatMap F4.fixedOrbitWord) ≠
        wordImages F4.tag [] ∧
      wordImages F4.tag ((altWord ⟨0, by decide⟩ 16).flatMap F4.fixedOrbitWord) =
        wordImages F4.tag [] := by
  decide +kernel

theorem exists_fixedRelElt_altWord
    (j : Fin F4.fixedOrbitCount) {n : ℕ} (hn : n ≤ 8) :
    ∃ k, F4.fixedRelElt k = ((altWord j n).map F4.fixedOrbitElement).prod ∧
      (F4.fixedRelWord k).length = n := by
  obtain ⟨k, hk | ⟨-, rfl, hk⟩⟩ := altWord_mem_table j n (by omega)
  · exact ⟨k, by rw [fixedRelElt, hk], by rw [hk, length_altWord]⟩
  · refine ⟨k, simpleImages_injective ?_, by rw [hk, length_altWord]⟩
    rw [fixedRelElt, hk, list_prod_map_fixedOrbitElement, list_prod_map_fixedOrbitElement,
      simpleImages_wordProd, simpleImages_wordProd, wordImages_altWord_eight, Fin.rev_rev]

theorem fixedRelLength_alternating
    {ω : List (Fin F4.fixedOrbitCount)} (hω : ω.IsChain (· ≠ ·))
    (hlen : ω.length ≤ 8) :
    F4.fixedRelLength ((ω.map F4.fixedOrbitElement).prod) = ω.length := by
  rcases ω with _ | ⟨j, ω'⟩
  · exact le_antisymm (fixedRelLength_le rfl) (Nat.zero_le _)
  · obtain ⟨k, hk, hklen⟩ := exists_fixedRelElt_altWord j hlen
    rw [← eq_altWord _ hω j rfl] at hk
    rw [← hk, fixedRelLength_fixedRelElt, hklen]

theorem pow_F4_fixedOrbitElement_mul
    (n : ℕ) :
    (F4.fixedOrbitElement ⟨0, by decide⟩ * F4.fixedOrbitElement ⟨1, by decide⟩) ^ n =
      ((altWord ⟨0, by decide⟩ (2 * n)).map F4.fixedOrbitElement).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, altWord, altWord, Fin.rev_rev,
      List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← mul_assoc]
    rfl

theorem orderOf_F4_fixedOrbitElement_mul :
    orderOf (F4.fixedOrbitElement ⟨0, by decide⟩ * F4.fixedOrbitElement ⟨1, by decide⟩) = 8 := by
  have key : ∀ n, (F4.fixedOrbitElement ⟨0, by decide⟩ * F4.fixedOrbitElement ⟨1, by decide⟩) ^ n
      = 1 ↔ wordImages F4.tag ((altWord ⟨0, by decide⟩ (2 * n)).flatMap F4.fixedOrbitWord) =
        wordImages F4.tag [] := fun n => by
    rw [pow_F4_fixedOrbitElement_mul, list_prod_map_fixedOrbitElement, ← simpleImages_wordProd,
      ← simpleImages_wordProd, CoxeterSystem.wordProd_nil]
    exact simpleImages_injective.eq_iff.symm
  refine orderOf_eq_prime_pow (p := 2) (n := 2) ?_ ?_
  · rw [key]
    exact wordImages_altWord_eight_sixteen.1
  · rw [key]
    exact wordImages_altWord_eight_sixteen.2

theorem ree_fixed_Weyl_structure :
    (∀ t : ReeTag, t.relWeylRee = Subgroup.closure (Set.range t.fixedOrbitElement)) ∧
    (∀ (t : ReeTag) (j : Fin t.fixedOrbitCount), orderOf (t.fixedOrbitElement j) = 2) ∧
    Nat.card G2.relWeylRee = 2 ∧
    Nat.card F4.relWeylRee = 16 ∧
    orderOf (F4.fixedOrbitElement (0 : Fin 2) * F4.fixedOrbitElement (1 : Fin 2)) = 8 ∧
    (∀ ω : List (Fin F4.fixedOrbitCount), ω.IsChain (· ≠ ·) → ω.length ≤ 8 →
      F4.fixedRelLength ((ω.map F4.fixedOrbitElement).prod) = ω.length) ∧
    (∀ (t : ReeTag) (j : Fin t.fixedOrbitCount),
      (t.fixedOrbitWeyl j : Set (WeylGroup t.tag)) ∩ t.relWeylRee =
        {1, t.fixedOrbitElement j}) ∧
    (∀ (t : ReeTag) (j : Fin t.fixedOrbitCount),
      (coxeterSystem t.tag).length (t.fixedOrbitElement j) = (t.fixedOrbitRoots j).ncard) ∧
    (∀ (t : ReeTag) (j : Fin t.fixedOrbitCount),
      (t.fixedOrbitElement j • ·) '' t.fixedOrbitRoots j = Neg.neg '' t.fixedOrbitRoots j) ∧
    (∀ (t : ReeTag) (j : Fin t.fixedOrbitCount),
      Set.BijOn (t.fixedOrbitElement j • ·) (t.fixedOrbitComplementRoots j)
        (t.fixedOrbitComplementRoots j)) ∧
    (G2.fixedOrbitRoots (0 : Fin 1)).ncard = 6 ∧
    (F4.fixedOrbitRoots (0 : Fin 2)).ncard = 2 ∧
    (F4.fixedOrbitRoots (1 : Fin 2)).ncard = 4 ∧
    (∀ t : ReeTag, ∀ w ∈ t.relWeylRee, ∀ j : Fin t.fixedOrbitCount,
      (∀ α ∈ t.fixedOrbitRoots j, 0 < height (w • α)) ∨
        ∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0) ∧
    (∀ t : ReeTag, ∀ w ∈ t.relWeylRee, ∀ j : Fin t.fixedOrbitCount,
      (∀ α ∈ t.fixedOrbitRoots j, 0 < height (w • α)) →
        t.fixedRelLength (w * t.fixedOrbitElement j) = t.fixedRelLength w + 1 ∧
        (coxeterSystem t.tag).length (w * t.fixedOrbitElement j) =
          (coxeterSystem t.tag).length w + (t.fixedOrbitRoots j).ncard) ∧
    (∀ t : ReeTag, ∀ w ∈ t.relWeylRee, ∀ j : Fin t.fixedOrbitCount,
      (∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0) →
        t.fixedRelLength (w * t.fixedOrbitElement j) + 1 = t.fixedRelLength w ∧
        (coxeterSystem t.tag).length (w * t.fixedOrbitElement j) +
          (t.fixedOrbitRoots j).ncard = (coxeterSystem t.tag).length w) ∧
    (∀ t : ReeTag, ∀ w ∈ t.relWeylRee, ∀ j : Fin t.fixedOrbitCount,
      (∀ α ∈ t.fixedOrbitRoots j, 0 < height (w⁻¹ • α)) →
        t.fixedRelLength (t.fixedOrbitElement j * w) = t.fixedRelLength w + 1 ∧
        (coxeterSystem t.tag).length (t.fixedOrbitElement j * w) =
          (coxeterSystem t.tag).length w + (t.fixedOrbitRoots j).ncard) ∧
    (∀ t : ReeTag, ∀ w ∈ t.relWeylRee, ∀ j : Fin t.fixedOrbitCount,
      (∀ α ∈ t.fixedOrbitRoots j, height (w⁻¹ • α) < 0) →
        t.fixedRelLength (t.fixedOrbitElement j * w) + 1 = t.fixedRelLength w ∧
        (coxeterSystem t.tag).length (t.fixedOrbitElement j * w) +
          (t.fixedOrbitRoots j).ncard = (coxeterSystem t.tag).length w) ∧
    (∀ t : ReeTag, ∀ w ∈ t.relWeylRee, w ≠ 1 →
      ∃ j : Fin t.fixedOrbitCount, ∀ α ∈ t.fixedOrbitRoots j, height (w • α) < 0) ∧
    (∀ t : ReeTag, ∃ w₀ : WeylGroup t.tag,
      ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) ∧
    ∀ (t : ReeTag) (w₀ : WeylGroup t.tag),
      (∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) →
        (∀ v : Fin t.tag.rank → ℤ, w₀ • v = -v) ∧ w₀ ∈ t.relWeylRee :=
  ⟨fun _ => relWeylRee_eq_closure, fun _ => orderOf_fixedOrbitElement,
    card_relWeylRee, card_relWeylRee, orderOf_F4_fixedOrbitElement_mul,
    fun _ hω hlen => fixedRelLength_alternating hω hlen,
    fun _ => fixedOrbitWeyl_inter_relWeylRee, fun _ => length_fixedOrbitElement,
    fun _ => image_fixedOrbitRoots, fun _ => bijOn_fixedOrbitComplementRoots,
    ncard_fixedOrbitRoots _, ncard_fixedOrbitRoots _, ncard_fixedOrbitRoots _,
    fun _ _ hw j => fixedOrbitRoots_sign hw j,
    fun _ _ hw _ hpos => lengths_mul_fixedOrbitElement_of_pos hw hpos,
    fun _ _ hw _ hneg => lengths_mul_fixedOrbitElement_of_neg hw hneg,
    fun _ _ hw _ hpos => lengths_fixedOrbitElement_mul_of_pos hw hpos,
    fun _ _ hw _ hneg => lengths_fixedOrbitElement_mul_of_neg hw hneg,
    fun _ _ hw h1 => exists_fixedOrbitRoots_neg hw h1,
    fun _ => Finite.exists_max _, fun _ _ h => ⟨smul_longest h, longest_mem_relWeylRee h⟩⟩

end ReeTag

end CFSG.LieType.Ree
