module

public import CFSG.LieType.Chevalley.FoldedWeylData
public import CFSG.LieType.Chevalley.WeylExchange

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

open CFSG.LieType.Chevalley

variable (t : TwistTag)

theorem orbitIndex_perm (i : Fin t.tag.rank) : t.orbitIndex (t.perm i) = t.orbitIndex i := by
  revert i
  cases t <;> decide

theorem orbitIndex_eq_iff {i j : Fin t.tag.rank} :
    t.orbitIndex j = t.orbitIndex i ↔ j = i ∨ j = t.perm i ∨ j = t.perm (t.perm i) := by
  revert i j
  cases t <;> decide

theorem cartan_eq_zero_of_mem_orbit {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) : t.tag.cartan i j = 0 := by
  have key : ∀ a, ∀ p ∈ t.orbit a ×ˢ t.orbit a, p.1 ≠ p.2 → t.tag.cartan p.1 p.2 = 0 := by
    cases t <;> decide
  exact key a (i, j) (Finset.mem_product.2 ⟨hi, hj⟩) hij

theorem exists_orbitIndex_eq (a : Fin t.foldedTag.rank) : ∃ i, t.orbitIndex i = a := by
  revert a
  cases t <;> decide

theorem cartan_eq_zero_of_mem_orbitWord {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbitWord a) (hj : j ∈ t.orbitWord a) (hij : i ≠ j) : t.tag.cartan i j = 0 :=
  t.cartan_eq_zero_of_mem_orbit ((t.mem_orbitWord).1 hi) ((t.mem_orbitWord).1 hj) hij

theorem foldMap_injective : Function.Injective t.foldMap := by
  intro u u' h
  funext a
  obtain ⟨i, rfl⟩ := t.exists_orbitIndex_eq a
  have := congrFun h i
  rwa [t.foldMap_apply_apply, t.foldMap_apply_apply] at this

theorem foldMap_mem_fixedLattice
    (u : Fin t.foldedTag.rank → ℤ) : t.foldMap u ∈ t.fixedLattice := by
  rw [t.mem_fixedLattice_iff_forall]
  intro i
  rw [t.foldMap_apply_apply, t.foldMap_apply_apply, t.orbitIndex_perm]

theorem orbitSum_mem_fixedLattice
    (a : Fin t.foldedTag.rank) : t.orbitSum a ∈ t.fixedLattice :=
  t.foldMap_single a ▸ t.foldMap_mem_fixedLattice _

theorem exists_foldMap_eq
    {v : Fin t.tag.rank → ℤ} (hv : v ∈ t.fixedLattice) :
    ∃ u, t.foldMap u = v := by
  choose rep hrep using t.exists_orbitIndex_eq
  have h := (t.mem_fixedLattice_iff_forall).1 hv
  refine ⟨fun a => v (rep a), funext fun i => ?_⟩
  rw [t.foldMap_apply_apply]
  rcases (t.orbitIndex_eq_iff).1 (hrep (t.orbitIndex i)) with h1 | h1 | h1
  · rw [h1]
  · rw [h1, h]
  · rw [h1, h, h]

theorem range_foldMap :
    LinearMap.range t.foldMap = t.fixedLattice := by
  ext v
  exact ⟨fun ⟨u, hu⟩ => hu ▸ t.foldMap_mem_fixedLattice u, t.exists_foldMap_eq⟩

@[expose] def foldLatticeEquiv :
    (Fin t.foldedTag.rank → ℤ) ≃ₗ[ℤ] t.fixedLattice :=
  (LinearEquiv.ofInjective t.foldMap t.foldMap_injective).trans
    (LinearEquiv.ofEq _ _ t.range_foldMap)

@[simp] theorem coe_foldLatticeEquiv
    (u : Fin t.foldedTag.rank → ℤ) :
    (t.foldLatticeEquiv u : Fin t.tag.rank → ℤ) = t.foldMap u :=
  rfl

theorem orbitReflection_smul
    (a : Fin t.foldedTag.rank) (v : Fin t.tag.rank → ℤ) :
    t.orbitReflection a • v = (t.orbitWord a).foldr (reflect t.tag) v :=
  wordProd_smul _ v

theorem orbitReflection_smul_single
    {a : Fin t.foldedTag.rank} {i : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) :
    t.orbitReflection a • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single i 1 := by
  rw [orbitReflection_smul]
  revert a i
  cases t <;> decide +kernel

theorem orbitReflection_mul_self
    (a : Fin t.foldedTag.rank) :
    t.orbitReflection a * t.orbitReflection a = 1 := by
  refine ext_single fun k => ?_
  rw [mul_smul, one_smul, orbitReflection_smul, orbitReflection_smul]
  revert a k
  cases t <;> decide +kernel

theorem orbitReflection_inv
    (a : Fin t.foldedTag.rank) :
    (t.orbitReflection a)⁻¹ = t.orbitReflection a :=
  inv_eq_of_mul_eq_one_right (t.orbitReflection_mul_self a)

theorem orbitReflection_ne_one
    (a : Fin t.foldedTag.rank) : t.orbitReflection a ≠ 1 := by
  intro h
  obtain ⟨i, hi⟩ := t.exists_orbitIndex_eq a
  have h' := congrFun (t.orbitReflection_smul_single ((t.mem_orbit_iff).2 hi)) i
  rw [h, one_smul] at h'
  simp at h'

theorem orbitReflection_mem
    (a : Fin t.foldedTag.rank) : t.orbitReflection a ∈ relWeylTwist t := by
  rw [mem_relWeylTwist, orbitReflection, weylTwist_wordProd]
  refine ext_single fun k => ?_
  rw [wordProd_smul, wordProd_smul]
  revert a k
  cases t <;> decide +kernel

theorem orbitReflection_smul_orbitSum
    (a b : Fin t.foldedTag.rank) :
    t.orbitReflection a • t.orbitSum b =
      t.foldMap (simple t.foldedTag a • (Pi.single b 1 : Fin t.foldedTag.rank → ℤ)) := by
  rw [orbitReflection_smul, simple_smul, orbitSum_eq]
  funext i
  rw [foldMap_apply_apply]
  revert a b i
  cases t <;> decide +kernel

theorem orbitReflection_smul_foldMap
    (a : Fin t.foldedTag.rank) (v : Fin t.foldedTag.rank → ℤ) :
    t.orbitReflection a • t.foldMap v = t.foldMap (simple t.foldedTag a • v) := by
  have h : (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan t.tag)
      (t.orbitReflection a)).comp t.foldMap = t.foldMap.comp
        (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan t.foldedTag)
          (simple t.foldedTag a)) := by
    refine LinearMap.pi_ext fun b x => ?_
    have hx : (Pi.single b x : Fin t.foldedTag.rank → ℤ) = x • Pi.single b 1 := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [hx, map_smul, map_smul, LinearMap.comp_apply, LinearMap.comp_apply, foldMap_single,
      ← smul_def, ← smul_def, orbitReflection_smul_orbitSum]
  exact LinearMap.congr_fun h v

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem length_mul_wordProd_add_length
    {τ : Tag} {w : WeylGroup τ} {ω : List (Fin τ.rank)}
    (hω : ω.Nodup) (horth : ∀ i ∈ ω, ∀ j ∈ ω, i ≠ j → τ.cartan i j = 0)
    (hneg : ∀ i ∈ ω, height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0) :
    (coxeterSystem τ).length (w * (coxeterSystem τ).wordProd ω) + ω.length =
      (coxeterSystem τ).length w := by
  induction ω generalizing w with
  | nil => simp
  | cons j ω ih =>
    rw [List.nodup_cons] at hω
    have hd : (coxeterSystem τ).IsRightDescent w j :=
      (smul_single_mem_negRoots_iff w j).1
        ⟨IsRoot.smul (isRoot_single τ j) w, hneg j List.mem_cons_self⟩
    rw [isRightDescent_iff_length] at hd
    have hneg' : ∀ i ∈ ω, height ((w * simple τ j) • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 := by
      intro i hi
      have hji : j ≠ i := fun h => hω.1 (h ▸ hi)
      rw [mul_smul, simple_smul, reflect_single,
        horth j List.mem_cons_self i (List.mem_cons_of_mem _ hi) hji, zero_smul, sub_zero]
      exact hneg i (List.mem_cons_of_mem _ hi)
    have h : (coxeterSystem τ).length (w * (coxeterSystem τ).simple j *
        (coxeterSystem τ).wordProd ω) + ω.length = (coxeterSystem τ).length (w * simple τ j) :=
      ih hω.2 (fun i hi k hk => horth i (List.mem_cons_of_mem _ hi) k (List.mem_cons_of_mem _ hk))
        hneg'
    rw [CoxeterSystem.wordProd_cons, ← mul_assoc, List.length_cons]
    omega

theorem length_mul_wordProd_of_pos
    {τ : Tag} {w : WeylGroup τ} {ω : List (Fin τ.rank)}
    (hω : ω.Nodup) (horth : ∀ i ∈ ω, ∀ j ∈ ω, i ≠ j → τ.cartan i j = 0)
    (hpos : ∀ i ∈ ω, 0 < height (w • (Pi.single i 1 : Fin τ.rank → ℤ))) :
    (coxeterSystem τ).length (w * (coxeterSystem τ).wordProd ω) =
      (coxeterSystem τ).length w + ω.length := by
  induction ω generalizing w with
  | nil => simp
  | cons j ω ih =>
    rw [List.nodup_cons] at hω
    have hd : ¬ (coxeterSystem τ).IsRightDescent w j := fun hd =>
      ((mem_posRoots_iff_not_mem_negRoots (IsRoot.smul (isRoot_single τ j) w)).1
        ⟨IsRoot.smul (isRoot_single τ j) w, hpos j List.mem_cons_self⟩)
        ((smul_single_mem_negRoots_iff w j).2 hd)
    rw [not_isRightDescent_iff_length] at hd
    have hpos' : ∀ i ∈ ω, 0 < height ((w * simple τ j) • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
      intro i hi
      have hji : j ≠ i := fun h => hω.1 (h ▸ hi)
      rw [mul_smul, simple_smul, reflect_single,
        horth j List.mem_cons_self i (List.mem_cons_of_mem _ hi) hji, zero_smul, sub_zero]
      exact hpos i (List.mem_cons_of_mem _ hi)
    have h : (coxeterSystem τ).length (w * (coxeterSystem τ).simple j *
        (coxeterSystem τ).wordProd ω) = (coxeterSystem τ).length (w * simple τ j) + ω.length :=
      ih hω.2 (fun i hi k hk => horth i (List.mem_cons_of_mem _ hi) k (List.mem_cons_of_mem _ hk))
        hpos'
    rw [CoxeterSystem.wordProd_cons, ← mul_assoc, List.length_cons, h]
    change (coxeterSystem τ).length (w * simple τ j) + ω.length = _
    omega

variable (t : TwistTag)

theorem smul_single_perm
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) (i : Fin t.tag.rank) :
    w • (Pi.single (t.perm i) 1 : Fin t.tag.rank → ℤ) =
      permLattice t.perm (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) := by
  rw [← permLattice_single, (mem_relWeylTwist_iff_smul t).1 hw]

theorem height_smul_single_of_orbitIndex_eq
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {i j : Fin t.tag.rank} (h : t.orbitIndex j = t.orbitIndex i) :
    height (w • (Pi.single j 1 : Fin t.tag.rank → ℤ)) =
      height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) := by
  rcases (t.orbitIndex_eq_iff).1 h with rfl | rfl | rfl
  · rfl
  · rw [smul_single_perm t hw, height_permLattice]
  · rw [smul_single_perm t hw, height_permLattice, smul_single_perm t hw, height_permLattice]

theorem length_mul_orbitReflection_add_card
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {i : Fin t.tag.rank} (hi : height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    (coxeterSystem t.tag).length (w * t.orbitReflection (t.orbitIndex i)) +
      (t.orbit (t.orbitIndex i)).card = (coxeterSystem t.tag).length w := by
  rw [← t.length_orbitWord]
  refine length_mul_wordProd_add_length (t.nodup_orbitWord _)
    (fun _ hk _ hl => t.cartan_eq_zero_of_mem_orbitWord hk hl) fun j hj => ?_
  rw [height_smul_single_of_orbitIndex_eq t hw ((t.mem_orbit_iff).1 ((t.mem_orbitWord).1 hj))]
  exact hi

theorem relWeylTwist_eq_closure :
    relWeylTwist t = Subgroup.closure (Set.range t.orbitReflection) := by
  refine le_antisymm (fun w hw => ?_) ((Subgroup.closure_le _).2 ?_)
  · suffices h : ∀ n, ∀ w ∈ relWeylTwist t, (coxeterSystem t.tag).length w = n →
        w ∈ Subgroup.closure (Set.range t.orbitReflection) from h _ w hw rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw hn
      by_cases h1 : w = 1
      · rw [h1]
        exact one_mem _
      obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one h1
      have hlen := length_mul_orbitReflection_add_card t hw hi
      have hcard : 0 < (t.orbit (t.orbitIndex i)).card :=
        Finset.card_pos.2 ⟨i, t.mem_orbit_orbitIndex i⟩
      have hw' := ih _ (by omega) _ (mul_mem hw (t.orbitReflection_mem (t.orbitIndex i))) rfl
      rw [← mul_one w, ← t.orbitReflection_mul_self (t.orbitIndex i), ← mul_assoc]
      exact mul_mem hw' (Subgroup.subset_closure ⟨_, rfl⟩)
  · rintro _ ⟨a, rfl⟩
    exact t.orbitReflection_mem a

theorem eq_one_of_forall_smul_fixedLattice
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (hfix : ∀ v ∈ t.fixedLattice, w • v = v) : w = 1 := by
  by_contra h1
  obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one h1
  have hle : (w • t.orbitSum (t.orbitIndex i)) i ≤ 0 := by
    rw [TwistTag.orbitSum, Finset.smul_sum, Finset.sum_apply]
    refine Finset.sum_nonpos fun j hj => ?_
    have hj' := height_smul_single_of_orbitIndex_eq t hw ((t.mem_orbit_iff).1 hj)
    exact (IsRoot.height_neg_iff (IsRoot.smul (isRoot_single _ j) w)).1 (hj' ▸ hi) i
  rw [hfix _ (t.orbitSum_mem_fixedLattice _), t.orbitSum_apply,
    ite_eq_left (t.mem_orbit_orbitIndex i)] at hle
  omega

theorem exists_smul_foldMap_eq
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    ∃ u : WeylGroup t.foldedTag, ∀ v, w • t.foldMap v = t.foldMap (u • v) := by
  rw [relWeylTwist_eq_closure] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨simple t.foldedTag a, t.orbitReflection_smul_foldMap a⟩
  | one => exact ⟨1, fun v => by rw [one_smul, one_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨u', hu'⟩ := hy
    exact ⟨u * u', fun v => by rw [mul_smul, hu', hu, mul_smul]⟩
  | inv x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨u⁻¹, fun v => ?_⟩
    have h := hu (u⁻¹ • v)
    rw [smul_inv_smul] at h
    rw [← h, inv_smul_smul]

theorem eq_of_forall_smul_foldMap
    {w : WeylGroup t.tag} {u u' : WeylGroup t.foldedTag}
    (hu : ∀ v, w • t.foldMap v = t.foldMap (u • v))
    (hu' : ∀ v, w • t.foldMap v = t.foldMap (u' • v)) : u = u' :=
  FaithfulSMul.eq_of_smul_eq_smul (α := Fin t.foldedTag.rank → ℤ) fun v =>
    t.foldMap_injective ((hu v).symm.trans (hu' v))

@[expose] def foldedWeylHom :
    relWeylTwist t →* WeylGroup t.foldedTag where
  toFun w := (exists_smul_foldMap_eq t w.2).choose
  map_one' := eq_of_forall_smul_foldMap t (exists_smul_foldMap_eq t (one_mem _)).choose_spec
    fun v => by rw [one_smul, one_smul]
  map_mul' w w' := eq_of_forall_smul_foldMap t (exists_smul_foldMap_eq t (w * w').2).choose_spec
    fun v => by
      rw [Subgroup.coe_mul, mul_smul, (exists_smul_foldMap_eq t w'.2).choose_spec,
        (exists_smul_foldMap_eq t w.2).choose_spec, mul_smul]

theorem smul_foldMap
    (w : relWeylTwist t) (v : Fin t.foldedTag.rank → ℤ) :
    (w : WeylGroup t.tag) • t.foldMap v = t.foldMap (foldedWeylHom t w • v) :=
  (exists_smul_foldMap_eq t w.2).choose_spec v

theorem foldedWeylHom_eq
    {w : relWeylTwist t} {u : WeylGroup t.foldedTag}
    (hu : ∀ v, (w : WeylGroup t.tag) • t.foldMap v = t.foldMap (u • v)) : foldedWeylHom t w = u :=
  eq_of_forall_smul_foldMap t (smul_foldMap t w) hu

theorem foldedWeylHom_orbitReflection
    (a : Fin t.foldedTag.rank) :
    foldedWeylHom t ⟨t.orbitReflection a, t.orbitReflection_mem a⟩ = simple t.foldedTag a :=
  foldedWeylHom_eq t (t.orbitReflection_smul_foldMap a)

theorem foldedWeylHom_injective :
    Function.Injective (foldedWeylHom t) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  refine Subtype.ext (eq_one_of_forall_smul_fixedLattice t w.2 fun v hv => ?_)
  obtain ⟨u, rfl⟩ := t.exists_foldMap_eq hv
  rw [smul_foldMap, hw, one_smul]

theorem foldedWeylHom_surjective :
    Function.Surjective (foldedWeylHom t) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← (coxeterSystem t.foldedTag).subgroup_closure_range_simple, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨_, foldedWeylHom_orbitReflection t a⟩

@[expose] def foldedWeylEquiv :
    relWeylTwist t ≃* WeylGroup t.foldedTag :=
  MulEquiv.ofBijective (foldedWeylHom t) ⟨foldedWeylHom_injective t, foldedWeylHom_surjective t⟩

@[simp] theorem foldedWeylEquiv_apply
    (w : relWeylTwist t) :
    foldedWeylEquiv t w = foldedWeylHom t w :=
  rfl

theorem smul_foldMap_foldedWeylEquiv
    (w : relWeylTwist t) (v : Fin t.foldedTag.rank → ℤ) :
    (w : WeylGroup t.tag) • t.foldMap v = t.foldMap (foldedWeylEquiv t w • v) :=
  smul_foldMap t w v

theorem foldedWeylEquiv_orbitReflection
    (a : Fin t.foldedTag.rank) :
    foldedWeylEquiv t ⟨t.orbitReflection a, t.orbitReflection_mem a⟩ = simple t.foldedTag a :=
  foldedWeylHom_orbitReflection t a

theorem fixed_Weyl_folded_identification
    (t : TwistTag) :
    (∃ e : (Fin t.foldedTag.rank → ℤ) ≃ₗ[ℤ] t.fixedLattice,
      ∀ u, (e u : Fin t.tag.rank → ℤ) = t.foldMap u) ∧
    (∀ a, t.orbitReflection a ∈ relWeylTwist t ∧ t.orbitReflection a ≠ 1 ∧
      t.orbitReflection a * t.orbitReflection a = 1) ∧
    relWeylTwist t = Subgroup.closure (Set.range t.orbitReflection) ∧
    (∃ φ : relWeylTwist t ≃* WeylGroup t.foldedTag,
      (∀ (w : relWeylTwist t) (u : Fin t.foldedTag.rank → ℤ),
        (w : WeylGroup t.tag) • t.foldMap u = t.foldMap (φ w • u)) ∧
      ∀ a (h : t.orbitReflection a ∈ relWeylTwist t),
        φ ⟨t.orbitReflection a, h⟩ = simple t.foldedTag a) ∧
    (∀ a (u : Fin t.foldedTag.rank → ℤ),
      t.orbitReflection a • t.foldMap u = t.foldMap (simple t.foldedTag a • u)) ∧
    ∀ w ∈ relWeylTwist t, (∀ v ∈ t.fixedLattice, w • v = v) → w = 1 :=
  ⟨⟨t.foldLatticeEquiv, t.coe_foldLatticeEquiv⟩,
    fun a => ⟨t.orbitReflection_mem a, t.orbitReflection_ne_one a, t.orbitReflection_mul_self a⟩,
    relWeylTwist_eq_closure t,
    ⟨foldedWeylEquiv t, smul_foldMap_foldedWeylEquiv t,
      fun a _ => foldedWeylEquiv_orbitReflection t a⟩,
    t.orbitReflection_smul_foldMap,
    fun _ hw hfix => eq_one_of_forall_smul_fixedLattice t hw hfix⟩

end CFSG.LieType.Chevalley
