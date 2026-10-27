module

public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LieType.Chevalley.LongestElement
public import CFSG.LieType.Chevalley.SimplyLacedCommutation

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

open CFSG.LieType.Chevalley Matrix

variable (t : TwistTag)

@[expose] def diagramOrbit (α : Fin t.tag.rank → ℤ) : Finset (Fin t.tag.rank → ℤ) :=
  (Finset.range t.order).image fun k => permLattice (t.perm ^ k) α

@[expose] def diagramRootOrbits : Set (Finset (Fin t.tag.rank → ℤ)) :=
  {O | ∃ α, IsRoot t.tag α ∧ t.diagramOrbit α = O}

theorem order_pos : 0 < t.order := by
  cases t <;> decide

theorem mem_diagramOrbit {α β : Fin t.tag.rank → ℤ} :
    β ∈ t.diagramOrbit α ↔ ∃ g ∈ Subgroup.zpowers t.perm, permLattice g α = β := by
  rw [diagramOrbit, Finset.mem_image]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨t.perm ^ k, Subgroup.npow_mem_zpowers _ _, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rw [← (isOfFinOrder_of_finite t.perm).mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff] at hg
    obtain ⟨k, rfl⟩ := hg
    exact ⟨k % t.order, Finset.mem_range.2 (Nat.mod_lt _ t.order_pos),
      by rw [← pow_eq_pow_mod k t.perm_pow_order]⟩

theorem self_mem_diagramOrbit (α : Fin t.tag.rank → ℤ) : α ∈ t.diagramOrbit α :=
  Finset.mem_image.2 ⟨0, Finset.mem_range.2 t.order_pos, rfl⟩

theorem cartan_perm_pow (k : ℕ) (i j : Fin t.tag.rank) :
    t.tag.cartan ((t.perm ^ k) i) ((t.perm ^ k) j) = t.tag.cartan i j := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, t.cartan_perm, ih]

theorem isRoot_of_mem_diagramOrbit {α β : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α)
    (hβ : β ∈ t.diagramOrbit α) : IsRoot t.tag β := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hβ
  exact hα.permLattice (t.cartan_perm_pow k)

theorem height_of_mem_diagramOrbit
    {α β : Fin t.tag.rank → ℤ} (hβ : β ∈ t.diagramOrbit α) :
    height β = height α := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hβ
  exact height_permLattice _ _

theorem permLattice_pow_smul
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) (k : ℕ)
    (v : Fin t.tag.rank → ℤ) :
    permLattice (t.perm ^ k) (w • v) = w • permLattice (t.perm ^ k) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change permLattice (t.perm * t.perm ^ k) (w • v) = w • permLattice (t.perm * t.perm ^ k) v
    change permLattice t.perm (permLattice (t.perm ^ k) (w • v)) =
      w • permLattice t.perm (permLattice (t.perm ^ k) v)
    rw [ih, (mem_relWeylTwist_iff_smul t).1 hw]

theorem diagramOrbit_smul
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (α : Fin t.tag.rank → ℤ) : t.diagramOrbit (w • α) = (t.diagramOrbit α).image (w • ·) := by
  rw [diagramOrbit, diagramOrbit, Finset.image_image]
  exact Finset.image_congr fun k _ => t.permLattice_pow_smul hw k α

theorem diagramOrbit_single (i : Fin t.tag.rank) :
    t.diagramOrbit (Pi.single i 1) =
      (t.orbit (t.orbitIndex i)).image fun j => (Pi.single j 1 : Fin t.tag.rank → ℤ) := by
  rw [t.orbit_orbitIndex, Finset.image_image, diagramOrbit]
  exact Finset.image_congr fun k _ => permLattice_single _ _

theorem diagramOrbit_smul_single
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (i : Fin t.tag.rank) :
    t.diagramOrbit (w • Pi.single i 1) =
      (t.orbit (t.orbitIndex i)).image fun j => w • (Pi.single j 1 : Fin t.tag.rank → ℤ) := by
  rw [t.diagramOrbit_smul hw, t.diagramOrbit_single, Finset.image_image]
  rfl

theorem eq_single_of_height_orbitReflection_smul_neg
    {c : Fin t.foldedTag.rank}
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) (hpos : 0 < height β)
    (hneg : height (t.orbitReflection c • β) < 0) : ∃ j ∈ t.orbit c, β = Pi.single j 1 := by
  have key : ∀ k < t.tag.rootCertificate.roots.length, ∀ c : Fin t.foldedTag.rank,
      0 < height (t.tag.rootCertificate.root k) ∧
        height ((t.orbitWord c).foldr (reflect t.tag) (t.tag.rootCertificate.root k)) < 0 →
      ∃ j ∈ t.orbit c, t.tag.rootCertificate.root k = Pi.single j 1 := by
    cases t <;> decide +kernel
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hβ
  rw [orbitReflection_smul] at hneg
  exact key k hk c ⟨hpos, hneg⟩

theorem exists_smul_single_of_list_prod
    {l : List (WeylGroup t.tag)}
    (hl : ∀ x ∈ l, x ∈ Set.range t.orbitReflection) {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β)
    (hpos : 0 < height β) (hneg : height (l.prod • β) < 0) :
    ∃ v ∈ relWeylTwist t, ∃ i, β = v • Pi.single i 1 := by
  induction l with
  | nil =>
    rw [List.prod_nil, one_smul] at hneg
    omega
  | cons x l ih =>
    rw [List.prod_cons, mul_smul] at hneg
    have hl' : ∀ y ∈ l, y ∈ Set.range t.orbitReflection :=
      fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hprod : l.prod ∈ relWeylTwist t := Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨c, rfl⟩ := hl' y hy
      exact t.orbitReflection_mem c
    rcases IsRoot.height_pos_or_neg (IsRoot.smul hβ l.prod) with hγ | hγ
    · obtain ⟨c, rfl⟩ := hl x List.mem_cons_self
      obtain ⟨j, -, hj⟩ :=
        t.eq_single_of_height_orbitReflection_smul_neg (IsRoot.smul hβ l.prod) hγ hneg
      exact ⟨l.prod⁻¹, inv_mem hprod, j, by rw [← hj, inv_smul_smul]⟩
    · exact ih hl' hγ

theorem exists_reversesSigns_mem_relWeylTwist
    : ∃ w₀ ∈ relWeylTwist t, ReversesSigns w₀ := by
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have h₀ := reversesSigns_of_forall_length_le hmax
  have h₁ : ReversesSigns (weylTwist t w₀) := reversesSigns_of_forall_length_le fun u => by
    rw [length_weylTwist]
    exact hmax u
  exact ⟨w₀, (mem_relWeylTwist t).2 (h₁.eq h₀), h₀⟩

theorem exists_smul_single_of_pos
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β)
    (hpos : 0 < height β) : ∃ v ∈ relWeylTwist t, ∃ i, β = v • Pi.single i 1 := by
  obtain ⟨w₀, hw₀, h₀⟩ := t.exists_reversesSigns_mem_relWeylTwist
  rw [relWeylTwist_eq_closure, ← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hw₀
  obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hw₀
  refine t.exists_smul_single_of_list_prod (fun x hx => ?_) hβ hpos (h₀ β hβ hpos)
  rcases hl x hx with h | h
  · exact h
  · obtain ⟨c, hc⟩ := Set.mem_inv.1 h
    exact ⟨c, by rw [← t.orbitReflection_inv, hc, inv_inv]⟩

theorem exists_smul_single
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    ∃ v ∈ relWeylTwist t, ∃ i, β = v • Pi.single i 1 := by
  rcases IsRoot.height_pos_or_neg hβ with h | h
  · exact t.exists_smul_single_of_pos hβ h
  · obtain ⟨v, hv, i, hi⟩ :=
      t.exists_smul_single_of_pos (IsRoot.neg hβ) (by rw [height_neg]; omega)
    refine ⟨v * t.orbitReflection (t.orbitIndex i), mul_mem hv (t.orbitReflection_mem _), i, ?_⟩
    rw [mul_smul, t.orbitReflection_smul_single (t.mem_orbit_orbitIndex i), smul_neg, ← hi,
      neg_neg]

theorem exists_diagramOrbit_eq
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    ∃ w ∈ relWeylTwist t, ∃ a, t.diagramOrbit α =
      (t.orbit a).image fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ) := by
  obtain ⟨w, hw, i, rfl⟩ := t.exists_smul_single hα
  exact ⟨w, hw, t.orbitIndex i, t.diagramOrbit_smul_single hw i⟩

theorem single_one_injective :
    Function.Injective fun i : Fin t.tag.rank => (Pi.single i 1 : Fin t.tag.rank → ℤ) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [hij] at this

theorem injective_smul_single
    (w : WeylGroup t.tag) :
    Function.Injective fun i : Fin t.tag.rank => w • (Pi.single i 1 : Fin t.tag.rank → ℤ) :=
  (MulAction.injective w).comp t.single_one_injective

theorem card_image_smul_single
    (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank) :
    ((t.orbit a).image fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)).card =
      (t.orbit a).card :=
  Finset.card_image_of_injective _ (t.injective_smul_single w)

theorem card_orbit (a : Fin t.foldedTag.rank) :
    (t.orbit a).card = 1 ∨ (t.orbit a).card = t.order := by
  revert a
  cases t <;> decide

theorem symmetrizedCartan_tag : t.tag.symmetrizedCartan = t.tag.cartan := by
  cases t <;> exact one_mul _

theorem rootForm_smul_single_eq_zero
    (w : WeylGroup t.tag) {a : Fin t.foldedTag.rank}
    {i j : Fin t.tag.rank} (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) :
    (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) ⬝ᵥ
      (t.tag.symmetrizedCartan *ᵥ (w • (Pi.single j 1 : Fin t.tag.rank → ℤ))) = 0 := by
  rw [rootForm_smul, single_dotProduct, one_mul, mulVec_single_one, t.symmetrizedCartan_tag]
  exact t.cartan_eq_zero_of_mem_orbit hi hj hij

theorem sum_image_smul_single
    (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank) :
    ∑ β ∈ (t.orbit a).image (fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)), β =
      w • t.orbitSum a := by
  rw [Finset.sum_image fun i _ j _ h => t.injective_smul_single w h, orbitSum, Finset.smul_sum]

theorem sum_diagramOrbit_smul
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (α : Fin t.tag.rank → ℤ) :
    ∑ β ∈ t.diagramOrbit (w • α), β = w • ∑ β ∈ t.diagramOrbit α, β := by
  rw [t.diagramOrbit_smul hw, Finset.sum_image fun _ _ _ _ h => MulAction.injective w h,
    Finset.smul_sum]

theorem exists_foldMap_eq_sum
    {O : Finset (Fin t.tag.rank → ℤ)} (hO : O ∈ t.diagramRootOrbits) :
    ∃ u, IsRoot t.foldedTag u ∧ t.foldMap u = ∑ β ∈ O, β := by
  obtain ⟨α, hα, rfl⟩ := hO
  obtain ⟨w, hw, a, h⟩ := t.exists_diagramOrbit_eq hα
  refine ⟨foldedWeylEquiv t ⟨w, hw⟩ • Pi.single a 1,
    isRoot_iff_exists_smul_single.2 ⟨_, a, rfl⟩, ?_⟩
  rw [h, t.sum_image_smul_single, ← smul_foldMap_foldedWeylEquiv, t.foldMap_single]

theorem eq_single_of_sum_diagramOrbit_eq {γ : Fin t.tag.rank → ℤ}
    (hγ : IsRoot t.tag γ) {b : Fin t.foldedTag.rank}
    (h : ∑ β ∈ t.diagramOrbit γ, β = t.orbitSum b) :
    ∃ j ∈ t.orbit b, γ = Pi.single j 1 := by
  have key : ∀ k < t.tag.rootCertificate.roots.length, ∀ b : Fin t.foldedTag.rank,
      ∑ β ∈ t.diagramOrbit (t.tag.rootCertificate.root k), β = t.orbitSum b →
      ∃ j ∈ t.orbit b, t.tag.rootCertificate.root k = Pi.single j 1 := by
    cases t <;> decide +kernel
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hγ
  exact key k hk b h

theorem eq_of_sum_eq
    {O₁ O₂ : Finset (Fin t.tag.rank → ℤ)} (h₁ : O₁ ∈ t.diagramRootOrbits)
    (h₂ : O₂ ∈ t.diagramRootOrbits) (h : ∑ β ∈ O₁, β = ∑ β ∈ O₂, β) : O₁ = O₂ := by
  obtain ⟨α₁, hα₁, rfl⟩ := h₁
  obtain ⟨α₂, hα₂, rfl⟩ := h₂
  obtain ⟨w, hw, j, rfl⟩ := t.exists_smul_single hα₂
  have hsum : ∑ β ∈ t.diagramOrbit (w⁻¹ • α₁), β = t.orbitSum (t.orbitIndex j) := by
    rw [t.sum_diagramOrbit_smul (inv_mem hw), h, t.diagramOrbit_smul_single hw,
      t.sum_image_smul_single, inv_smul_smul]
  obtain ⟨j', hj', hj'eq⟩ := t.eq_single_of_sum_diagramOrbit_eq (IsRoot.smul hα₁ w⁻¹) hsum
  have hα : α₁ = w • Pi.single j' 1 := by rw [← hj'eq, smul_inv_smul]
  rw [hα, t.diagramOrbit_smul_single hw, t.diagramOrbit_smul_single hw,
    (t.mem_orbit_iff).1 hj']

@[expose] def diagramOrbitRoot
    (O : t.diagramRootOrbits) : {u // IsRoot t.foldedTag u} :=
  ⟨(t.exists_foldMap_eq_sum O.2).choose, (t.exists_foldMap_eq_sum O.2).choose_spec.1⟩

theorem foldMap_diagramOrbitRoot
    (O : t.diagramRootOrbits) :
    t.foldMap (t.diagramOrbitRoot O) = ∑ β ∈ (O : Finset (Fin t.tag.rank → ℤ)), β :=
  (t.exists_foldMap_eq_sum O.2).choose_spec.2

theorem diagramOrbitRoot_injective :
    Function.Injective t.diagramOrbitRoot := by
  intro O₁ O₂ h
  refine Subtype.ext (t.eq_of_sum_eq O₁.2 O₂.2 ?_)
  rw [← t.foldMap_diagramOrbitRoot, ← t.foldMap_diagramOrbitRoot, h]

theorem diagramOrbitRoot_surjective :
    Function.Surjective t.diagramOrbitRoot := by
  rintro ⟨u, hu⟩
  obtain ⟨u', a, rfl⟩ := isRoot_iff_exists_smul_single.1 hu
  obtain ⟨i, hi⟩ := t.exists_orbitIndex_eq a
  set w := (foldedWeylEquiv t).symm u'
  have hO : t.diagramOrbit ((w : WeylGroup t.tag) • Pi.single i 1) ∈ t.diagramRootOrbits :=
    ⟨_, IsRoot.smul (isRoot_single _ i) _, rfl⟩
  refine ⟨⟨_, hO⟩, Subtype.ext (t.foldMap_injective ?_)⟩
  change t.foldMap (t.diagramOrbitRoot ⟨_, hO⟩) = t.foldMap (u' • Pi.single a 1)
  rw [t.foldMap_diagramOrbitRoot]
  change ∑ β ∈ t.diagramOrbit ((w : WeylGroup t.tag) • Pi.single i 1), β = _
  rw [t.diagramOrbit_smul_single w.2 i, t.sum_image_smul_single, hi, ← t.foldMap_single,
    smul_foldMap_foldedWeylEquiv, MulEquiv.apply_symm_apply]

theorem diagramOrbitRoot_bijective :
    Function.Bijective t.diagramOrbitRoot :=
  ⟨t.diagramOrbitRoot_injective, t.diagramOrbitRoot_surjective⟩

@[expose] def diagramOrbitRootEquiv :
    t.diagramRootOrbits ≃ {u // IsRoot t.foldedTag u} :=
  Equiv.ofBijective _ t.diagramOrbitRoot_bijective

theorem height_diagramOrbitRoot_pos_iff
    (O : t.diagramRootOrbits) {β : Fin t.tag.rank → ℤ}
    (hβ : β ∈ (O : Finset (Fin t.tag.rank → ℤ))) :
    0 < height (t.diagramOrbitRoot O : Fin t.foldedTag.rank → ℤ) ↔ 0 < height β := by
  obtain ⟨O, hO⟩ := O
  have hO' := hO
  obtain ⟨α, hα, rfl⟩ := hO'
  set u := (t.diagramOrbitRoot ⟨_, hO⟩ : Fin t.foldedTag.rank → ℤ)
  have hu : IsRoot t.foldedTag u := (t.diagramOrbitRoot ⟨_, hO⟩).2
  have hθ : t.foldMap u = ∑ γ ∈ t.diagramOrbit α, γ := t.foldMap_diagramOrbitRoot ⟨_, hO⟩
  have hcoord : ∀ i, u (t.orbitIndex i) = ∑ γ ∈ t.diagramOrbit α, γ i := fun i => by
    rw [← Finset.sum_apply, ← hθ, t.foldMap_apply_apply]
  have hheight : ∀ γ ∈ t.diagramOrbit α, height γ = height β := fun γ hγ =>
    (t.height_of_mem_diagramOrbit hγ).trans (t.height_of_mem_diagramOrbit hβ).symm
  rcases IsRoot.height_pos_or_neg (t.isRoot_of_mem_diagramOrbit hα hβ) with h | h
  · refine iff_of_true ((IsRoot.height_pos_iff hu).2 fun a => ?_) h
    obtain ⟨i, rfl⟩ := t.exists_orbitIndex_eq a
    rw [hcoord]
    exact Finset.sum_nonneg fun γ hγ =>
      (IsRoot.height_pos_iff (t.isRoot_of_mem_diagramOrbit hα hγ)).1 (hheight γ hγ ▸ h) _
  · refine iff_of_false (fun hpos => ?_) (by omega)
    have hneg : height u < 0 := (IsRoot.height_neg_iff hu).2 fun a => by
      obtain ⟨i, rfl⟩ := t.exists_orbitIndex_eq a
      rw [hcoord]
      exact Finset.sum_nonpos fun γ hγ =>
        (IsRoot.height_neg_iff (t.isRoot_of_mem_diagramOrbit hα hγ)).1 (hheight γ hγ ▸ h) _
    omega

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Matrix

theorem diagram_root_orbit_reduction
    (t : TwistTag) :
    (∀ α, IsRoot t.tag α → ∃ w ∈ relWeylTwist t, ∃ a,
      t.diagramOrbit α = (t.orbit a).image (fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) ∧
      (t.diagramOrbit α).card = (t.orbit a).card ∧
      ((t.orbit a).card = 1 ∨ (t.orbit a).card = t.order)) ∧
    (∀ α, IsRoot t.tag α → ∀ β ∈ t.diagramOrbit α, (0 < height β ↔ 0 < height α)) ∧
    (∀ α, IsRoot t.tag α → ∀ β ∈ t.diagramOrbit α, ∀ γ ∈ t.diagramOrbit α, β ≠ γ →
      β ⬝ᵥ (t.tag.symmetrizedCartan *ᵥ γ) = 0) ∧
    ∃ f : t.diagramRootOrbits ≃ {u // IsRoot t.foldedTag u},
      (∀ O : t.diagramRootOrbits, t.foldMap (f O) = ∑ β ∈ (O : Finset (Fin t.tag.rank → ℤ)), β) ∧
      ∀ O : t.diagramRootOrbits, ∀ β ∈ (O : Finset (Fin t.tag.rank → ℤ)),
        (0 < height (f O : Fin t.foldedTag.rank → ℤ) ↔ 0 < height β) := by
  refine ⟨fun α hα => ?_, fun α _ β hβ => by rw [t.height_of_mem_diagramOrbit hβ],
    fun α hα β hβ γ hγ hne => ?_, ⟨t.diagramOrbitRootEquiv, t.foldMap_diagramOrbitRoot,
      fun O β hβ => t.height_diagramOrbitRoot_pos_iff O hβ⟩⟩
  · obtain ⟨w, hw, a, h⟩ := t.exists_diagramOrbit_eq hα
    exact ⟨w, hw, a, h, by rw [h, t.card_image_smul_single], t.card_orbit a⟩
  · obtain ⟨w, hw, a, h⟩ := t.exists_diagramOrbit_eq hα
    rw [h, Finset.mem_image] at hβ hγ
    obtain ⟨i, hi, rfl⟩ := hβ
    obtain ⟨j, hj, rfl⟩ := hγ
    exact t.rootForm_smul_single_eq_zero w hi hj fun hij => hne (by rw [hij])

end CFSG.LieType.Chevalley
