module

public import CFSG.LieType.Chevalley.GraphFixedSchreier
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
public import CFSG.LieType.Chevalley.RootPairCommonField

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem list_prod_map_eq_of_ne_one {ι M : Type*} [Monoid M] {l : List ι} (hl : l.Nodup)
    {a : ι} (ha : a ∈ l) {g : ι → M} (hg : ∀ c, c ≠ a → g c = 1) : (l.map g).prod = g a := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hc, hl'⟩ := List.nodup_cons.1 hl
    by_cases hca : c = a
    · subst hca
      rw [List.prod_eq_one fun x hx => ?_, mul_one]
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hg y fun h => hc (h ▸ hy)
    · rw [hg c hca, one_mul]
      exact ih hl' ((List.mem_cons.1 ha).resolve_left (Ne.symm hca))

theorem ringHom_pow_apply_eq_of_apply_eq {K : Type*} [Semiring K] {σ : K →+* K} {c : K}
    (hc : σ c = c) (n : ℕ) : (σ ^ n) c = c := by
  rw [RingHom.coe_pow]
  exact Function.iterate_fixed hc n

theorem natCard_comap_rightHom {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (H : Subgroup G) :
    Nat.card (H.comap (SemidirectProduct.rightHom : N ⋊[φ] G →* G)) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => (x.1.left, ⟨x.1.right, x.2⟩)
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem cartanChar_zpow {τ : Tag} {K : Type} [Field K] (u : Kˣ) (e : Fin τ.rank → ℤ)
    (l : Fin τ.rank) : cartanChar (fun j => u ^ e j) l = u ^ (∑ j, e j * τ.cartan j l) := by
  rw [cartanChar, ← prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm

theorem eq_of_foldedEdges {t : TwistTag} {β : Type*} (g : Fin t.foldedTag.rank → β)
    (hedge : ∀ a b, ∑ j, (if t.orbitIndex j = a then (1 : ℤ) else 0) *
      t.tag.cartan j (t.orbitMin b) = -1 → g a = g b) (a b : Fin t.foldedTag.rank) :
    g a = g b := by
  cases t
  · have e01 := hedge ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    have e21 := hedge ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
    have e23 := hedge ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
    have h : ∀ c, g c = g ⟨1, by decide⟩ := by
      intro c
      fin_cases c
      exacts [e01, rfl, e21, e23.symm.trans e21]
    exact (h a).trans (h b).symm
  · have e10 := hedge ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)
    have h : ∀ c, g c = g ⟨0, by decide⟩ := by
      intro c
      fin_cases c
      exacts [rfl, e10]
    exact (h a).trans (h b).symm

@[expose] def baseOrbit : (t : TwistTag) → Fin t.foldedTag.rank
  | .E6 => ⟨2, by decide⟩
  | .D4 => ⟨1, by decide⟩

theorem card_orbit_baseOrbit (t : TwistTag) : (t.orbit (baseOrbit t)).card = 1 := by
  cases t <;> decide

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem mem_orbitField_of_fixed {c : K} (hc : σ c = c) (a : Fin t.foldedTag.rank) :
    c ∈ orbitField t K σ a :=
  mem_orbitField.2 (ringHom_pow_apply_eq_of_apply_eq hc _)

variable (t K σ) in
@[expose] def fixedOrbitX
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    graphFixedRootGroup t K σ :=
  ⟨orbitX t K σ a c, graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
    (orbitX_mem_graphFixedPosUnipotent t σ a c)⟩

variable (t K σ) in
@[expose] def fixedOrbitY
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    graphFixedRootGroup t K σ :=
  ⟨orbitY t K σ a c, graphFixedNegUnipotent_le_graphFixedRootGroup t K σ
    (orbitY_mem_graphFixedNegUnipotent t σ a c)⟩

variable (t K σ) in
@[expose] def fixedOrbitH
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    graphFixedRootGroup t K σ :=
  ⟨orbitH t K σ a u, orbitH_mem_graphFixedRootGroup t σ a u⟩

theorem orbitRankOneHomFixed_sl2Upper
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    orbitRankOneHomFixed t K σ a (sl2Upper _ c) = fixedOrbitX t K σ a c :=
  Subtype.ext (orbitRankOneHom_uSL a c)

theorem orbitRankOneHomFixed_sl2Lower
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    orbitRankOneHomFixed t K σ a (sl2Lower _ c) = fixedOrbitY t K σ a c :=
  Subtype.ext (orbitRankOneHom_vSL a c)

theorem orbitRankOneHomFixed_sl2Diag
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    orbitRankOneHomFixed t K σ a (sl2Diag _ u) = fixedOrbitH t K σ a u :=
  Subtype.ext (orbitRankOneHom_HSL a u)

theorem fixedOrbitX_injective
    (a : Fin t.foldedTag.rank) :
    Function.Injective (fixedOrbitX t K σ a) := by
  intro c d h
  apply sl2Upper_injective (orbitRankOneHomFixed_ker (a := a))
  change orbitRankOneHomFixed t K σ a (sl2Upper _ c) = orbitRankOneHomFixed t K σ a (sl2Upper _ d)
  rw [orbitRankOneHomFixed_sl2Upper, orbitRankOneHomFixed_sl2Upper, h]

variable (t K σ) in
@[expose] def graphFixedPairAut
    : Subgroup (MulAut (graphFixedRootGroup t K σ)) :=
  ⨅ a, pairAutSubgroup ((orbitXSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ))
    ((orbitYSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ))

theorem mem_graphFixedPairAut
    {α : MulAut (graphFixedRootGroup t K σ)} :
    α ∈ graphFixedPairAut t K σ ↔ ∀ a, α ∈ pairAutSubgroup
      (sl2RootX (orbitRankOneHomFixed t K σ a)) (sl2RootY (orbitRankOneHomFixed t K σ a)) := by
  rw [graphFixedPairAut, Subgroup.mem_iInf]
  simp only [sl2RootX_orbitRankOneHomFixed, sl2RootY_orbitRankOneHomFixed]

theorem exists_orbit_params
    [Finite K] {α : MulAut (graphFixedRootGroup t K σ)}
    (hα : α ∈ graphFixedPairAut t K σ) (a : Fin t.foldedTag.rank) :
    ∃ (b : (orbitField t K σ a)ˣ) (β : orbitField t K σ a ≃+* orbitField t K σ a),
      (∀ c, α (fixedOrbitX t K σ a c) = fixedOrbitX t K σ a (b * β c)) ∧
      (∀ c, α (fixedOrbitY t K σ a c) =
        fixedOrbitY t K σ a (((b⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) * β c)) ∧
      ∀ u, α (fixedOrbitH t K σ a u) = fixedOrbitH t K σ a (Units.map β.toMonoidHom u) := by
  have hα' := mem_graphFixedPairAut.1 hα a
  choose f hf using exists_sl2Upper_param hα'
  choose g hg using exists_sl2Lower_param hα'
  obtain ⟨b, β, hfb, hgb, hh⟩ := exists_semilinear_params orbitRankOneHomFixed_ker hα' hf hg
  refine ⟨b, β, fun c => ?_, fun c => ?_, fun u => ?_⟩
  · rw [← orbitRankOneHomFixed_sl2Upper, hf, hfb, orbitRankOneHomFixed_sl2Upper]
  · rw [← orbitRankOneHomFixed_sl2Lower, hg, hgb, orbitRankOneHomFixed_sl2Lower]
  · rw [← orbitRankOneHomFixed_sl2Diag, hh, orbitRankOneHomFixed_sl2Diag]

theorem orbit_params_unique
    {α : MulAut (graphFixedRootGroup t K σ)} {a : Fin t.foldedTag.rank}
    {b b' : (orbitField t K σ a)ˣ} {β β' : orbitField t K σ a ≃+* orbitField t K σ a}
    (h : ∀ c, α (fixedOrbitX t K σ a c) = fixedOrbitX t K σ a (b * β c))
    (h' : ∀ c, α (fixedOrbitX t K σ a c) = fixedOrbitX t K σ a (b' * β' c)) :
    b = b' ∧ β = β' := by
  have e : ∀ c, (b : orbitField t K σ a) * β c = b' * β' c := fun c =>
    fixedOrbitX_injective a ((h c).symm.trans (h' c))
  have hb : b = b' := Units.ext (by simpa using e 1)
  refine ⟨hb, RingEquiv.ext fun c => ?_⟩
  have := e c
  rw [hb] at this
  exact mul_left_cancel₀ b'.ne_zero this

variable (t K σ) in
abbrev OrbitParamGroup (a : Fin t.foldedTag.rank) :=
  (orbitField t K σ a)ˣ ⋊[unitsRingAut (orbitField t K σ a)] RingAut (orbitField t K σ a)

variable (t K σ) in
@[expose] def orbitParamsFun
    [Finite K] (a : Fin t.foldedTag.rank) (α : graphFixedPairAut t K σ) :
    OrbitParamGroup t K σ a :=
  ⟨(exists_orbit_params α.2 a).choose, (exists_orbit_params α.2 a).choose_spec.choose⟩

theorem orbitParamsFun_spec
    [Finite K] (a : Fin t.foldedTag.rank) (α : graphFixedPairAut t K σ) :
    (∀ c, (α : MulAut (graphFixedRootGroup t K σ)) (fixedOrbitX t K σ a c) =
      fixedOrbitX t K σ a ((orbitParamsFun t K σ a α).left * (orbitParamsFun t K σ a α).right c)) ∧
    (∀ c, (α : MulAut (graphFixedRootGroup t K σ)) (fixedOrbitY t K σ a c) =
      fixedOrbitY t K σ a ((((orbitParamsFun t K σ a α).left⁻¹ : (orbitField t K σ a)ˣ) :
        orbitField t K σ a) * (orbitParamsFun t K σ a α).right c)) ∧
    ∀ u, (α : MulAut (graphFixedRootGroup t K σ)) (fixedOrbitH t K σ a u) =
      fixedOrbitH t K σ a (Units.map (orbitParamsFun t K σ a α).right.toMonoidHom u) :=
  (exists_orbit_params α.2 a).choose_spec.choose_spec

theorem orbitParamsFun_eq
    [Finite K] {a : Fin t.foldedTag.rank} {α : graphFixedPairAut t K σ}
    {b : (orbitField t K σ a)ˣ} {β : RingAut (orbitField t K σ a)}
    (h : ∀ c, (α : MulAut (graphFixedRootGroup t K σ)) (fixedOrbitX t K σ a c) =
      fixedOrbitX t K σ a (b * β c)) :
    orbitParamsFun t K σ a α = ⟨b, β⟩ := by
  obtain ⟨hb, hβ⟩ := orbit_params_unique (orbitParamsFun_spec a α).1 h
  exact SemidirectProduct.ext hb hβ

variable (t K σ) in
@[expose] def orbitParams
    [Finite K] (a : Fin t.foldedTag.rank) :
    graphFixedPairAut t K σ →* OrbitParamGroup t K σ a where
  toFun := orbitParamsFun t K σ a
  map_one' := orbitParamsFun_eq fun c => by
    rw [Units.val_one, one_mul]
    rfl
  map_mul' α γ := by
    refine (orbitParamsFun_eq fun c => ?_).trans rfl
    rw [Subgroup.coe_mul, MulAut.mul_apply, (orbitParamsFun_spec a γ).1,
      (orbitParamsFun_spec a α).1, map_mul, ← mul_assoc]
    rfl

theorem orbitParams_spec
    [Finite K] (a : Fin t.foldedTag.rank) (α : graphFixedPairAut t K σ) :
    (∀ c, (α : MulAut (graphFixedRootGroup t K σ)) (fixedOrbitX t K σ a c) =
      fixedOrbitX t K σ a ((orbitParams t K σ a α).left * (orbitParams t K σ a α).right c)) ∧
    (∀ c, (α : MulAut (graphFixedRootGroup t K σ)) (fixedOrbitY t K σ a c) =
      fixedOrbitY t K σ a ((((orbitParams t K σ a α).left⁻¹ : (orbitField t K σ a)ˣ) :
        orbitField t K σ a) * (orbitParams t K σ a α).right c)) ∧
    ∀ u, (α : MulAut (graphFixedRootGroup t K σ)) (fixedOrbitH t K σ a u) =
      fixedOrbitH t K σ a (Units.map (orbitParams t K σ a α).right.toMonoidHom u) :=
  orbitParamsFun_spec a α

theorem list_prod_orbitH_mulSingle
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    ((List.finRange t.foldedTag.rank).map fun c => (orbitH t K σ c
      (Pi.mulSingle (M := fun c => (orbitField t K σ c)ˣ) a u c) : ModGL t.tag K)).prod =
      orbitH t K σ a u := by
  rw [list_prod_map_eq_of_ne_one (List.nodup_finRange _) (List.mem_finRange a),
    Pi.mulSingle_eq_same]
  intro c hc
  rw [Pi.mulSingle_eq_of_ne hc]
  have h1 : orbitH t K σ c 1 = 1 := mul_inv_cancel _
  rw [h1]
  rfl

theorem compatDiag_mulSingle {a : Fin t.foldedTag.rank} {u : (orbitField t K σ a)ˣ}
    (hu : σ ((u : orbitField t K σ a) : K) = u) :
    compatDiag t σ (Pi.mulSingle a u) =
      fun j => orbitFieldUnit t σ u ^ (if t.orbitIndex j = a then (1 : ℤ) else 0) := by
  funext j
  obtain ⟨k, hk, hi⟩ := t.exists_eq_perm_pow_orbitMin (t.mem_orbit_orbitIndex j)
  rw [← hi, compatDiag_pow _ _ hk]
  have hj : t.orbitIndex ((t.perm ^ k) (t.orbitMin (t.orbitIndex j))) = t.orbitIndex j :=
    (t.mem_orbit_iff).1 (t.perm_pow_mem_orbit (t.orbitMin_mem _) k)
  rw [hj]
  refine Units.ext ?_
  by_cases h : t.orbitIndex j = a
  · subst h
    simp only [Pi.mulSingle_eq_same, ↓reduceIte, zpow_one, Units.coe_map, coe_orbitFieldUnit]
    exact ringHom_pow_apply_eq_of_apply_eq hu k
  · simp only [Pi.mulSingle_eq_of_ne h, h, ↓reduceIte, zpow_zero, Units.val_one]
    simp [orbitFieldUnit]

theorem fixedOrbitH_conj_fixedOrbitX
    {a : Fin t.foldedTag.rank} {u : (orbitField t K σ a)ˣ}
    (hu : σ ((u : orbitField t K σ a) : K) = u) (b : Fin t.foldedTag.rank) :
    ∃ w : (orbitField t K σ b)ˣ, ((w : orbitField t K σ b) : K) =
        ((u : orbitField t K σ a) : K) ^ (∑ j, (if t.orbitIndex j = a then (1 : ℤ) else 0) *
          t.tag.cartan j (t.orbitMin b)) ∧
      ∀ c, fixedOrbitH t K σ a u * fixedOrbitX t K σ b c * (fixedOrbitH t K σ a u)⁻¹ =
        fixedOrbitX t K σ b (w * c) := by
  obtain ⟨v, -, hv, hX, -⟩ := exists_list_prod_orbitH_conj (Pi.mulSingle a u)
  rw [list_prod_orbitH_mulSingle] at hX
  refine ⟨v b, ?_, fun c => Subtype.ext (hX b c)⟩
  have h := congrArg Units.val (hv b)
  rw [compatDiag_mulSingle hu, cartanChar_zpow, Units.val_zpow_eq_zpow_val, coe_orbitFieldUnit,
    coe_orbitFieldUnit] at h
  exact h

theorem ringEquiv_apply_fixed {q : ℕ} (hσ : ∀ c, σ c = c ^ q) {a : Fin t.foldedTag.rank}
    (β : orbitField t K σ a ≃+* orbitField t K σ a) {c : orbitField t K σ a}
    (hc : σ (c : K) = c) : σ (β c : K) = β c := by
  have hcq : c ^ q = c := Subtype.ext (by rw [SubmonoidClass.coe_pow, ← hσ, hc])
  rw [hσ, ← SubmonoidClass.coe_pow, ← map_pow, hcq]

theorem orbitParams_right_eq_of_edge
    [Finite K] {q : ℕ} (hσ : ∀ c, σ c = c ^ q)
    (α : graphFixedPairAut t K σ) {a b : Fin t.foldedTag.rank}
    (hab : ∑ j, (if t.orbitIndex j = a then (1 : ℤ) else 0) * t.tag.cartan j (t.orbitMin b) = -1)
    {c : K} (hca : c ∈ orbitField t K σ a) (hcb : c ∈ orbitField t K σ b) (hc : σ c = c) :
    ((orbitParams t K σ a α).right ⟨c, hca⟩ : K) =
      ((orbitParams t K σ b α).right ⟨c, hcb⟩ : K) := by
  by_cases h0 : c = 0
  · subst h0
    have ha0 : (⟨0, hca⟩ : orbitField t K σ a) = 0 := rfl
    have hb0 : (⟨0, hcb⟩ : orbitField t K σ b) = 0 := rfl
    rw [ha0, hb0, map_zero, map_zero, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
  have hca0 : (⟨c, hca⟩ : orbitField t K σ a) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hcb0 : (⟨c, hcb⟩ : orbitField t K σ b) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  obtain ⟨hxb, -, -⟩ := orbitParams_spec b α
  obtain ⟨-, -, hha⟩ := orbitParams_spec a α
  obtain ⟨w, hw, hconj⟩ := fixedOrbitH_conj_fixedOrbitX (u := Units.mk0 _ hca0) hc b
  have hfix := ringEquiv_apply_fixed hσ (orbitParams t K σ a α).right
    (c := (Units.mk0 _ hca0 : orbitField t K σ a)) hc
  obtain ⟨w', hw', hconj'⟩ := fixedOrbitH_conj_fixedOrbitX
    (u := Units.map (orbitParams t K σ a α).right.toMonoidHom (Units.mk0 _ hca0)) hfix b
  rw [hab, zpow_neg, zpow_one] at hw hw'
  have e := congrArg (α : MulAut (graphFixedRootGroup t K σ)) (hconj 1)
  rw [map_mul, map_mul, map_inv, hha, hxb, hxb, map_one, mul_one, hconj', mul_one] at e
  have e' := fixedOrbitX_injective b e
  have e'' : (w' : orbitField t K σ b) = (orbitParams t K σ b α).right w := by
    rw [mul_comm] at e'
    exact mul_left_cancel₀ (orbitParams t K σ b α).left.ne_zero e'
  have hwc : (w : orbitField t K σ b) = (⟨c, hcb⟩ : orbitField t K σ b)⁻¹ :=
    Subtype.ext (by rw [hw, Units.val_mk0]; rfl)
  rw [hwc, map_inv₀] at e''
  have e3 := congrArg (fun x : orbitField t K σ b => (x : K)) e''
  rw [hw', Units.coe_map, Units.val_mk0] at e3
  exact inv_injective (e3.trans (by rfl))

theorem orbitParams_right_eq_base
    [Finite K] {q : ℕ} (hσ : ∀ c, σ c = c ^ q)
    (α : graphFixedPairAut t K σ) (a : Fin t.foldedTag.rank) {c : K}
    (hca : c ∈ orbitField t K σ a) (hc0 : c ∈ orbitField t K σ (baseOrbit t)) :
    ((orbitParams t K σ a α).right ⟨c, hca⟩ : K) =
      ((orbitParams t K σ (baseOrbit t) α).right ⟨c, hc0⟩ : K) := by
  have hc : σ c = c := (mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit t)).1 hc0
  exact eq_of_foldedEdges
    (fun a' => ((orbitParams t K σ a' α).right ⟨c, mem_orbitField_of_fixed hc a'⟩ : K))
    (fun a' b' hab => orbitParams_right_eq_of_edge hσ α hab _ _ hc) a (baseOrbit t)

theorem eq_one_of_fixedOrbit
    {α : MulAut (graphFixedRootGroup t K σ)}
    (hσ : Function.Surjective σ)
    (hx : ∀ a c, α (fixedOrbitX t K σ a c) = fixedOrbitX t K σ a c)
    (hy : ∀ a c, α (fixedOrbitY t K σ a c) = fixedOrbitY t K σ a c) : α = 1 := by
  refine eq_one_of_forall_apply_eq (iSup_range_orbitRankOneHomFixed hσ) fun a g hg => ?_
  rw [range_eq_sl2RootX_sup_sl2RootY] at hg
  have hle : sl2RootX (orbitRankOneHomFixed t K σ a) ⊔ sl2RootY (orbitRankOneHomFixed t K σ a) ≤
      α.toMonoidHom.eqLocus (MonoidHom.id _) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      show α (orbitRankOneHomFixed t K σ a (sl2Upper _ c)) =
        orbitRankOneHomFixed t K σ a (sl2Upper _ c)
      rw [orbitRankOneHomFixed_sl2Upper]
      exact hx a c
    · rintro _ ⟨c, rfl⟩
      show α (orbitRankOneHomFixed t K σ a (sl2Lower _ c)) =
        orbitRankOneHomFixed t K σ a (sl2Lower _ c)
      rw [orbitRankOneHomFixed_sl2Lower]
      exact hy a c
  exact hle hg

variable (t K σ) in
@[expose] def orbitFieldBaseFix (a : Fin t.foldedTag.rank) :
    Subgroup (RingAut (orbitField t K σ a)) where
  carrier := {β | ∀ c : orbitField t K σ a, σ (c : K) = c → β c = c}
  mul_mem' {β γ} hβ hγ c hc := by
    change β (γ c) = c
    rw [hγ c hc, hβ c hc]
  one_mem' _ _ := rfl
  inv_mem' {β} hβ c hc := by
    change β.symm c = c
    rw [RingEquiv.symm_apply_eq, hβ c hc]

theorem natCard_orbitFieldBaseFix [Finite K] {q : ℕ} (hq : 1 < q)
    (hcard : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card)
    (a : Fin t.foldedTag.rank) :
    Nat.card (orbitFieldBaseFix t K σ a) = (t.orbit a).card := by
  have hk : orbitField t K σ (baseOrbit t) ≤ orbitField t K σ a := fun c hc =>
    mem_orbitField_of_fixed ((mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit t)).1 hc) a
  let : Algebra (orbitField t K σ (baseOrbit t)) (orbitField t K σ a) :=
    (Subfield.inclusion hk).toAlgebra
  have hfixk : ∀ x : orbitField t K σ (baseOrbit t), σ (x : K) = x := fun x =>
    (mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit t)).1 x.2
  let e : orbitFieldBaseFix t K σ a ≃ Gal(orbitField t K σ a / orbitField t K σ (baseOrbit t)) :=
    { toFun := fun β => AlgEquiv.ofRingEquiv (f := β.1) fun x => β.2 _ (hfixk x)
      invFun := fun g => ⟨g.toRingEquiv, fun c hc => g.commutes
        (⟨c, (mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit t)).2 hc⟩ :
          orbitField t K σ (baseOrbit t))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank]
  have h := Module.natCard_eq_pow_finrank (K := orbitField t K σ (baseOrbit t))
    (V := orbitField t K σ a)
  rw [hcard, hcard, card_orbit_baseOrbit, pow_one] at h
  exact (Nat.pow_right_injective hq h).symm

theorem natCard_ker_orbitParams_dvd
    [Finite K] {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q)
    (hσs : Function.Surjective σ)
    (hcard : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card) :
    Nat.card (SemidirectProduct.rightHom.comp (orbitParams t K σ (baseOrbit t))).ker ∣
      ∏ a, (t.orbit a).card * (Nat.card (orbitField t K σ a) - 1) := by
  have hmem : ∀ (α : (SemidirectProduct.rightHom.comp (orbitParams t K σ (baseOrbit t))).ker) a,
      (orbitParams t K σ a α.1).right ∈ orbitFieldBaseFix t K σ a := by
    intro α a c hc
    have h1 : (orbitParams t K σ (baseOrbit t) α.1).right = 1 := α.2
    have hc0 : (c : K) ∈ orbitField t K σ (baseOrbit t) :=
      (mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit t)).2 hc
    refine Subtype.ext ((orbitParams_right_eq_base hσ α.1 a c.2 hc0).trans ?_)
    rw [h1]
    rfl
  let Θ : (SemidirectProduct.rightHom.comp (orbitParams t K σ (baseOrbit t))).ker →*
      ∀ a, ((orbitFieldBaseFix t K σ a).comap
        (SemidirectProduct.rightHom : OrbitParamGroup t K σ a →* _)) :=
    MonoidHom.pi fun a => ((orbitParams t K σ a).comp
      (SemidirectProduct.rightHom.comp (orbitParams t K σ (baseOrbit t))).ker.subtype).codRestrict
        _ fun α => hmem α a
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have h1 : ∀ a, orbitParams t K σ a α.1 = 1 := fun a =>
      congrArg Subtype.val (congrFun hα a)
    have hα1 : ((α.1 : graphFixedPairAut t K σ) : MulAut (graphFixedRootGroup t K σ)) = 1 :=
      eq_one_of_fixedOrbit hσs (fun a c => by
        rw [(orbitParams_spec a α.1).1, h1 a, SemidirectProduct.one_left,
          SemidirectProduct.one_right, Units.val_one, one_mul]
        rfl) (fun a c => by
        rw [(orbitParams_spec a α.1).2.1, h1 a, SemidirectProduct.one_left,
          SemidirectProduct.one_right, inv_one, Units.val_one, one_mul]
        rfl)
    exact Subtype.ext (Subtype.ext hα1)
  have h := Subgroup.card_dvd_of_injective Θ hinj
  rw [Nat.card_pi] at h
  refine h.trans (dvd_of_eq (Finset.prod_congr rfl fun a _ => ?_))
  rw [natCard_comap_rightHom, Nat.card_units, natCard_orbitFieldBaseFix hq hcard a, mul_comm]

theorem diagram_fixed_simple_pairs_common_base_field_parameter
    (t : TwistTag) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    (∀ α ∈ graphFixedPairAut t K σ.toRingHom, ∀ a, ∃! p : (orbitField t K σ.toRingHom a)ˣ ×
        (orbitField t K σ.toRingHom a ≃+* orbitField t K σ.toRingHom a),
      (∀ c, α (fixedOrbitX t K σ.toRingHom a c) =
        fixedOrbitX t K σ.toRingHom a (p.1 * p.2 c)) ∧
      (∀ c, α (fixedOrbitY t K σ.toRingHom a c) = fixedOrbitY t K σ.toRingHom a
        (((p.1⁻¹ : (orbitField t K σ.toRingHom a)ˣ) : orbitField t K σ.toRingHom a) * p.2 c)) ∧
      ∀ u, α (fixedOrbitH t K σ.toRingHom a u) =
        fixedOrbitH t K σ.toRingHom a (Units.map p.2.toMonoidHom u)) ∧
    ∃ k : Subfield K, (k : Set K) = {c | σ c = c} ∧ (∀ a, k ≤ orbitField t K σ.toRingHom a) ∧
      ∃ δ : graphFixedPairAut t K σ.toRingHom →* RingAut k,
        (∀ (α : graphFixedPairAut t K σ.toRingHom) a
          (p : (orbitField t K σ.toRingHom a)ˣ ×
            (orbitField t K σ.toRingHom a ≃+* orbitField t K σ.toRingHom a)),
          (∀ c, (α : MulAut (graphFixedRootGroup t K σ.toRingHom))
            (fixedOrbitX t K σ.toRingHom a c) = fixedOrbitX t K σ.toRingHom a (p.1 * p.2 c)) →
          ∀ c (hc : c ∈ k) (hca : c ∈ orbitField t K σ.toRingHom a),
            (p.2 ⟨c, hca⟩ : K) = (δ α ⟨c, hc⟩ : K)) ∧
        IsCyclic δ.range ∧
        Nat.card δ.ker ∣
          ∏ a, (t.orbit a).card * (Nat.card (orbitField t K σ.toRingHom a) - 1) := by
  have hq : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))
  obtain ⟨σ', hσ', -, hcard, -, -⟩ := finite_graph_field_parameter_fields t hℓ hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  subst hσσ'
  have hσq : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  refine ⟨fun α hα a => ?_, orbitField t K σ.toRingHom (baseOrbit t), ?_, fun a c hc =>
    mem_orbitField_of_fixed ((mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit t)).1 hc) a,
    SemidirectProduct.rightHom.comp (orbitParams t K σ.toRingHom (baseOrbit t)), ?_, ?_, ?_⟩
  ·
    obtain ⟨b, β, hx, hy, hh⟩ := exists_orbit_params hα a
    exact ⟨(b, β), ⟨hx, hy, hh⟩, fun p hp => by
      obtain ⟨h1, h2⟩ := orbit_params_unique hp.1 hx
      exact Prod.ext h1 h2⟩
  · ext c
    exact mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit t)
  ·
    intro α a p hp c hc hca
    have hpa := orbitParamsFun_eq (b := p.1) (β := p.2) hp
    have e : p.2 = (orbitParams t K σ.toRingHom a α).right := by
      change p.2 = (orbitParamsFun t K σ.toRingHom a α).right
      rw [hpa]
    rw [e]
    exact orbitParams_right_eq_base hσq α a hca hc
  ·
    have : IsCyclic (RingAut (orbitField t K σ.toRingHom (baseOrbit t))) := ringAut_isCyclic
    infer_instance
  · exact natCard_ker_orbitParams_dvd hq hσq σ.surjective hcard

end CFSG.LieType.Chevalley
