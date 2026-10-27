module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPolar

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)

variable {r : ℕ} {K : Type*} [Field K]

section Points

theorem exists_eq_span_of_points (L : Points (quadPlus r K)) :
    ∃ v : Fin r ⊕ Fin r → K, v ≠ 0 ∧ L.val = K ∙ v := by
  have hL0 : L.val ≠ ⊥ := fun h => by
    have h1 := L.2.1
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  refine ⟨v, hv0, (Submodule.eq_of_le_of_finrank_eq
    ((span_singleton_le_iff_mem _ _).2 hv) ?_).symm⟩
  rw [finrank_span_singleton hv0, L.2.1]

@[expose] noncomputable def spanPoint {v : Fin r ⊕ Fin r → K} (hv0 : v ≠ 0)
    (hv : quadPlus r K v = 0) : Points (quadPlus r K) :=
  ⟨K ∙ v, finrank_span_singleton hv0, fun x hx => by
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hx
    rw [map_smul_eq_sq, hv, mul_zero]⟩

theorem polarOrtho_span_singleton {a b : Fin r ⊕ Fin r → K} :
    PolarOrtho (quadPlus r K) (K ∙ a) (K ∙ b) ↔ polar (quadPlus r K) a b = 0 := by
  refine ⟨fun h => h a (mem_span_singleton_self a) b (mem_span_singleton_self b),
    fun h x hx y hy => ?_⟩
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hx
  obtain ⟨d, rfl⟩ := mem_span_singleton.1 hy
  rw [polar_smul_left_eq, polar_smul_right_eq, h, mul_zero, mul_zero]

end Points

section Scale

variable (r K) in
@[expose] def ySpan : Submodule K (Fin r ⊕ Fin r → K) :=
  coordSpan K (Set.range Sum.inr)

theorem mem_ySpan_iff {v : Fin r ⊕ Fin r → K} : v ∈ ySpan r K ↔ ∀ i, v (Sum.inl i) = 0 := by
  rw [ySpan, mem_coordSpan_iff]
  refine ⟨fun h i => h _ (by simp), fun h x hx => ?_⟩
  rcases x with i | i
  · exact h i
  · exact absurd ⟨i, rfl⟩ hx

theorem mem_flag_top_iff {v : Fin r ⊕ Fin r → K} :
    v ∈ flag r K r ↔ ∀ i, v (Sum.inr i) = 0 := by
  rw [flag_eq_coordSpan, mem_coordSpan_iff]
  refine ⟨fun h i => h _ (by simp), fun h x hx => ?_⟩
  rcases x with i | i
  · exact absurd ⟨i, i.isLt, rfl⟩ hx
  · exact h i

variable (r K) in
@[expose] def splitScale (c : K) : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) where
  toFun v x := Sum.elim (fun _ => (1 : K)) (fun _ => c) x * v x
  map_add' v w := funext fun x => by simp [mul_add]
  map_smul' a v := funext fun x => by simp [mul_left_comm]

@[simp] theorem splitScale_inl (c : K) (v : Fin r ⊕ Fin r → K) (i : Fin r) :
    splitScale r K c v (Sum.inl i) = v (Sum.inl i) := by
  simp [splitScale]

@[simp] theorem splitScale_inr (c : K) (v : Fin r ⊕ Fin r → K) (i : Fin r) :
    splitScale r K c v (Sum.inr i) = c * v (Sum.inr i) := by
  simp [splitScale]

theorem quadPlus_splitScale (c : K) (v : Fin r ⊕ Fin r → K) :
    quadPlus r K (splitScale r K c v) = c * quadPlus r K v := by
  rw [quadPlus_apply, quadPlus_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [splitScale_inl, splitScale_inr]
  ring

theorem polar_quadPlus_eq_dotProduct (v w : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) v w =
      (fun i => v (Sum.inl i)) ⬝ᵥ (fun i => w (Sum.inr i)) +
        (fun i => w (Sum.inl i)) ⬝ᵥ (fun i => v (Sum.inr i)) := by
  rw [polar_quadPlus, Finset.sum_add_distrib]
  rfl

end Scale

theorem exists_smul_eq_of_dotProduct_iff {y y' : Fin r → K} (hy : y ≠ 0)
    (h : ∀ u : Fin r → K, u ⬝ᵥ y = 0 ↔ u ⬝ᵥ y' = 0) : ∃ l : K, l ≠ 0 ∧ y' = l • y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
  have hi' : y i ≠ 0 := hi
  have key : ∀ j, y' j = y' i / y i * y j := by
    intro j
    have hu := (h ((y i) • Pi.single j 1 - (y j) • Pi.single i 1)).1 (by
      rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct]
      simp only [smul_eq_mul]
      ring)
    rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct]
      at hu
    simp only [smul_eq_mul, one_mul] at hu
    rw [div_mul_eq_mul_div, eq_div_iff hi']
    linear_combination hu
  refine ⟨y' i / y i, fun h0 => hi' ?_, funext fun j => by rw [key j, Pi.smul_apply, smul_eq_mul]⟩
  have hy'0 : y' = 0 := funext fun j => by rw [key j, h0, zero_mul, Pi.zero_apply]
  have := (h (Pi.single i 1)).2 (by rw [hy'0, dotProduct_zero])
  rwa [single_dotProduct, one_mul] at this

section Mixed

variable (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
  (hφ : ∀ L M : Points (quadPlus r K),
    PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val)
  (hX : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r → φ L = L)
  (hY : ∀ L : Points (quadPlus r K), L.val ≤ ySpan r K → φ L = L)
include hφ hX hY

omit hφ hX hY in
theorem polar_inl_left (u : Fin r → K) (v : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) v (Sum.elim u 0) = u ⬝ᵥ (fun i => v (Sum.inr i)) := by
  rw [polar_quadPlus_eq_dotProduct]
  simp [dotProduct]

omit hφ hX hY in
theorem polar_inr_left (u : Fin r → K) (v : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) v (Sum.elim 0 u) = (fun i => v (Sum.inl i)) ⬝ᵥ u := by
  rw [polar_quadPlus_eq_dotProduct]
  simp [dotProduct]

theorem exists_eq_span_splitScale {v : Fin r ⊕ Fin r → K} (hv0 : v ≠ 0)
    (hv : quadPlus r K v = 0) (hx : ∃ i, v (Sum.inl i) ≠ 0) (hy : ∃ i, v (Sum.inr i) ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ (φ (spanPoint hv0 hv)).val = K ∙ splitScale r K s v := by
  obtain ⟨w, hw0, hw⟩ := exists_eq_span_of_points (φ (spanPoint hv0 hv))
  have hyw : ∀ u : Fin r → K, u ⬝ᵥ (fun i => v (Sum.inr i)) = 0 ↔
      u ⬝ᵥ (fun i => w (Sum.inr i)) = 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    have hu0 : (Sum.elim u 0 : Fin r ⊕ Fin r → K) ≠ 0 := fun h => hu (funext fun i => by
      simpa using congrFun h (Sum.inl i))
    have huQ : quadPlus r K (Sum.elim u 0) = 0 := by simp [quadPlus_apply]
    have hfix := hX (spanPoint hu0 huQ) ((span_singleton_le_iff_mem _ _).2
      (mem_flag_top_iff.2 fun i => rfl))
    have h := hφ (spanPoint hv0 hv) (spanPoint hu0 huQ)
    rw [hfix, hw] at h
    change PolarOrtho _ (K ∙ v) (K ∙ _) ↔ PolarOrtho _ (K ∙ w) (K ∙ _) at h
    rw [polarOrtho_span_singleton, polarOrtho_span_singleton, polar_inl_left,
      polar_inl_left] at h
    exact h
  have hxw : ∀ u : Fin r → K, (fun i => v (Sum.inl i)) ⬝ᵥ u = 0 ↔
      (fun i => w (Sum.inl i)) ⬝ᵥ u = 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    have hu0 : (Sum.elim 0 u : Fin r ⊕ Fin r → K) ≠ 0 := fun h => hu (funext fun i => by
      simpa using congrFun h (Sum.inr i))
    have huQ : quadPlus r K (Sum.elim 0 u) = 0 := by simp [quadPlus_apply]
    have hfix := hY (spanPoint hu0 huQ) ((span_singleton_le_iff_mem _ _).2
      (mem_ySpan_iff.2 fun i => rfl))
    have h := hφ (spanPoint hv0 hv) (spanPoint hu0 huQ)
    rw [hfix, hw] at h
    change PolarOrtho _ (K ∙ v) (K ∙ _) ↔ PolarOrtho _ (K ∙ w) (K ∙ _) at h
    rw [polarOrtho_span_singleton, polarOrtho_span_singleton, polar_inr_left,
      polar_inr_left] at h
    exact h
  obtain ⟨l, hl, hly⟩ := exists_smul_eq_of_dotProduct_iff
    (fun h => by obtain ⟨i, hi⟩ := hy; exact hi (congrFun h i)) hyw
  obtain ⟨m, hm, hmx⟩ := exists_smul_eq_of_dotProduct_iff
    (y := fun i => v (Sum.inl i)) (y' := fun i => w (Sum.inl i))
    (fun h => by obtain ⟨i, hi⟩ := hx; exact hi (congrFun h i))
    (fun u => by rw [dotProduct_comm u, dotProduct_comm u]; exact hxw u)
  refine ⟨l / m, div_ne_zero hl hm, ?_⟩
  have hwe : w = m • splitScale r K (l / m) v := by
    funext x
    rcases x with i | i
    · have := congrFun hmx i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp [this]
    · have := congrFun hly i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp only [this, Pi.smul_apply, smul_eq_mul, splitScale_inr]
      field_simp
  rw [hw, hwe, span_singleton_smul_eq (IsUnit.mk0 _ hm)]

@[expose] def IsMixed (v : Fin r ⊕ Fin r → K) : Prop :=
  quadPlus r K v = 0 ∧ (∃ i, v (Sum.inl i) ≠ 0) ∧ ∃ i, v (Sum.inr i) ≠ 0

omit hφ hX hY in
theorem IsMixed.ne_zero {v : Fin r ⊕ Fin r → K} (hv : IsMixed v) : v ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := hv.2.1
  exact hi rfl

open Classical in
@[expose] noncomputable def rigScale (v : Fin r ⊕ Fin r → K) : K :=
  if h : IsMixed v then
    (exists_eq_span_splitScale φ hφ hX hY h.ne_zero h.1 h.2.1 h.2.2).choose
  else 1

theorem rigScale_spec {v : Fin r ⊕ Fin r → K} (h : IsMixed v) :
    rigScale φ hφ hX hY v ≠ 0 ∧
      (φ (spanPoint h.ne_zero h.1)).val = K ∙ splitScale r K (rigScale φ hφ hX hY v) v := by
  rw [rigScale, dite_eq_left h]
  exact (exists_eq_span_splitScale φ hφ hX hY h.ne_zero h.1 h.2.1 h.2.2).choose_spec

theorem rigScale_eq {v v' : Fin r ⊕ Fin r → K} (h : IsMixed v) (h' : IsMixed v')
    (horth : polar (quadPlus r K) v v' = 0)
    (hcross : (fun i => v (Sum.inl i)) ⬝ᵥ (fun i => v' (Sum.inr i)) ≠ 0) :
    rigScale φ hφ hX hY v = rigScale φ hφ hX hY v' := by
  obtain ⟨-, hs⟩ := rigScale_spec φ hφ hX hY h
  obtain ⟨-, hs'⟩ := rigScale_spec φ hφ hX hY h'
  have ho := (hφ (spanPoint h.ne_zero h.1) (spanPoint h'.ne_zero h'.1)).1
    (polarOrtho_span_singleton.2 horth)
  rw [hs, hs', polarOrtho_span_singleton, polar_quadPlus_eq_dotProduct] at ho
  rw [polar_quadPlus_eq_dotProduct] at horth
  set s := rigScale φ hφ hX hY v
  set s' := rigScale φ hφ hX hY v'
  have e1 : (fun i => splitScale r K s v (Sum.inl i)) ⬝ᵥ (fun i => splitScale r K s' v' (Sum.inr i))
      = s' * ((fun i => v (Sum.inl i)) ⬝ᵥ (fun i => v' (Sum.inr i))) := by
    simp only [splitScale_inl, splitScale_inr, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : (fun i => splitScale r K s' v' (Sum.inl i)) ⬝ᵥ (fun i => splitScale r K s v (Sum.inr i))
      = s * ((fun i => v' (Sum.inl i)) ⬝ᵥ (fun i => v (Sum.inr i))) := by
    simp only [splitScale_inl, splitScale_inr, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2] at ho
  have : (s' - s) * ((fun i => v (Sum.inl i)) ⬝ᵥ (fun i => v' (Sum.inr i))) = 0 := by
    linear_combination ho - s * horth
  rcases mul_eq_zero.1 this with h0 | h0
  · exact (sub_eq_zero.1 h0).symm
  · exact absurd h0 hcross

end Mixed

section Constancy

variable (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
  (hφ : ∀ L M : Points (quadPlus r K),
    PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val)
  (hX : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r → φ L = L)
  (hY : ∀ L : Points (quadPlus r K), L.val ≤ ySpan r K → φ L = L)

variable (r K) in
@[expose] def rigTestVec (i j : Fin r) (a : K) : Fin r ⊕ Fin r → K :=
  Pi.single (Sum.inl j) 1 + a • Pi.single (Sum.inr i) 1

@[simp] theorem rigTestVec_inl (i j : Fin r) (a : K) (k : Fin r) :
    rigTestVec r K i j a (Sum.inl k) = if k = j then 1 else 0 := by
  simp [rigTestVec, Pi.single_apply]

@[simp] theorem rigTestVec_inr (i j : Fin r) (a : K) (k : Fin r) :
    rigTestVec r K i j a (Sum.inr k) = if k = i then a else 0 := by
  simp [rigTestVec, Pi.single_apply]

theorem isMixed_rigTestVec {i j : Fin r} (hij : i ≠ j) {a : K} (ha : a ≠ 0) :
    IsMixed (rigTestVec r K i j a) := by
  refine ⟨?_, ⟨j, by simp⟩, ⟨i, by simpa using ha⟩⟩
  rw [quadPlus_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [rigTestVec_inl, rigTestVec_inr]
  by_cases hk : k = j
  · subst hk
    simp [hij.symm]
  · simp [hk]

theorem exists_inl_inr_ne {v : Fin r ⊕ Fin r → K} (h : IsMixed v) :
    ∃ i j, i ≠ j ∧ v (Sum.inl i) ≠ 0 ∧ v (Sum.inr j) ≠ 0 := by
  obtain ⟨hQ, ⟨i₀, hi₀⟩, ⟨j₀, hj₀⟩⟩ := h
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hji : j₀ = i₀ := by
    by_contra hne
    exact hj₀ (hcon i₀ j₀ (Ne.symm hne) hi₀)
  subst hji
  have hx : ∀ k, k ≠ j₀ → v (Sum.inl k) = 0 := fun k hk => by
    by_contra hk'
    exact hj₀ (hcon k j₀ hk hk')
  rw [quadPlus_apply, Finset.sum_eq_single j₀ (fun k _ hk => by rw [hx k hk, zero_mul])
    (by simp)] at hQ
  exact mul_ne_zero hi₀ hj₀ hQ

include hφ hX hY

theorem rigScale_eq_test {v : Fin r ⊕ Fin r → K} (h : IsMixed v) {i j : Fin r} (hij : i ≠ j)
    (hxi : v (Sum.inl i) ≠ 0) (hyj : v (Sum.inr j) ≠ 0) :
    rigScale φ hφ hX hY v =
      rigScale φ hφ hX hY (rigTestVec r K i j (-v (Sum.inr j) / v (Sum.inl i))) := by
  have ha : -v (Sum.inr j) / v (Sum.inl i) ≠ 0 := div_ne_zero (neg_ne_zero.2 hyj) hxi
  refine rigScale_eq φ hφ hX hY h (isMixed_rigTestVec hij ha) ?_ ?_
  · rw [polar_quadPlus_eq_dotProduct]
    simp only [rigTestVec_inl, rigTestVec_inr, dotProduct, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
    ring
  · simp only [rigTestVec_inr, dotProduct, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    field_simp
    exact neg_ne_zero.2 hyj

theorem rigScale_test_left {i i' j : Fin r} (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i' ≠ j) {a : K}
    (ha : a ≠ 0) :
    rigScale φ hφ hX hY (rigTestVec r K i j a) = rigScale φ hφ hX hY (rigTestVec r K i' j a) := by
  set v : Fin r ⊕ Fin r → K :=
    Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl i') 1 - a • Pi.single (Sum.inr j) 1 with hv
  have vi : v (Sum.inl i) = 1 := by simp [hv, h1]
  have vi' : v (Sum.inl i') = 1 := by simp [hv, h1.symm]
  have vj : v (Sum.inr j) = -a := by simp [hv]
  have hmix : IsMixed v := by
    refine ⟨?_, ⟨i, by rw [vi]; exact one_ne_zero⟩, ⟨j, by rw [vj]; exact neg_ne_zero.2 ha⟩⟩
    rw [quadPlus_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = j
    · subst hk
      simp [hv, h2.symm, h3.symm]
    · simp [hv, hk]
  have e1 := rigScale_eq_test φ hφ hX hY hmix h2 (by rw [vi]; exact one_ne_zero)
    (by rw [vj]; exact neg_ne_zero.2 ha)
  have e2 := rigScale_eq_test φ hφ hX hY hmix h3 (by rw [vi']; exact one_ne_zero)
    (by rw [vj]; exact neg_ne_zero.2 ha)
  rw [vi, vj, neg_neg, div_one] at e1
  rw [vi', vj, neg_neg, div_one] at e2
  rw [← e1, e2]

theorem rigScale_test_right {i j j' : Fin r} (h1 : j ≠ j') (h2 : i ≠ j) (h3 : i ≠ j') {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    rigScale φ hφ hX hY (rigTestVec r K i j a) = rigScale φ hφ hX hY (rigTestVec r K i j' b) := by
  set v : Fin r ⊕ Fin r → K :=
    Pi.single (Sum.inl i) 1 - a • Pi.single (Sum.inr j) 1 - b • Pi.single (Sum.inr j') 1
    with hv
  have vi : v (Sum.inl i) = 1 := by simp [hv]
  have vj : v (Sum.inr j) = -a := by simp [hv, h1]
  have vj' : v (Sum.inr j') = -b := by simp [hv, h1.symm]
  have hmix : IsMixed v := by
    refine ⟨?_, ⟨i, by rw [vi]; exact one_ne_zero⟩, ⟨j, by rw [vj]; exact neg_ne_zero.2 ha⟩⟩
    rw [quadPlus_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [hv, h2, h3]
    · simp [hv, hk]
  have e1 := rigScale_eq_test φ hφ hX hY hmix h2 (by rw [vi]; exact one_ne_zero)
    (by rw [vj]; exact neg_ne_zero.2 ha)
  have e2 := rigScale_eq_test φ hφ hX hY hmix h3 (by rw [vi]; exact one_ne_zero)
    (by rw [vj']; exact neg_ne_zero.2 hb)
  rw [vi, vj, neg_neg, div_one] at e1
  rw [vi, vj', neg_neg, div_one] at e2
  rw [← e1, e2]

omit hφ hX hY in
theorem exists_third_index (hr : 3 ≤ r) (i j : Fin r) : ∃ k : Fin r, k ≠ i ∧ k ≠ j := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have key : ∀ m : ℕ, m < r → m = i.val ∨ m = j.val := fun m hm => by
    by_cases hmi : (⟨m, hm⟩ : Fin r) = i
    · left
      rw [← hmi]
    · right
      rw [← h _ hmi]
  have := key 0 (by omega)
  have := key 1 (by omega)
  have := key 2 (by omega)
  omega

theorem rigScale_test_eq (hr : 3 ≤ r) {i j : Fin r} (hij : i ≠ j) {a : K} (ha : a ≠ 0) :
    rigScale φ hφ hX hY (rigTestVec r K i j a) =
      rigScale φ hφ hX hY (rigTestVec r K ⟨0, by omega⟩ ⟨1, by omega⟩ 1) := by
  set S : Fin r → Fin r → K := fun i j => rigScale φ hφ hX hY (rigTestVec r K i j 1) with hS
  have hconst : ∀ i j : Fin r, i ≠ j → ∀ a : K, a ≠ 0 →
      rigScale φ hφ hX hY (rigTestVec r K i j a) = S i j := by
    intro i j hij a ha
    obtain ⟨j', hj'i, hj'j⟩ := exists_third_index hr i j
    rw [rigScale_test_right φ hφ hX hY (Ne.symm hj'j) hij (Ne.symm hj'i) ha one_ne_zero, hS]
    exact (rigScale_test_right φ hφ hX hY (Ne.symm hj'j) hij (Ne.symm hj'i) one_ne_zero
      one_ne_zero).symm
  have hR1 : ∀ i i' j : Fin r, i ≠ i' → i ≠ j → i' ≠ j → S i j = S i' j := fun i i' j h1 h2 h3 =>
    rigScale_test_left φ hφ hX hY h1 h2 h3 one_ne_zero
  have hR2 : ∀ i j j' : Fin r, j ≠ j' → i ≠ j → i ≠ j' → S i j = S i j' := fun i j j' h1 h2 h3 =>
    rigScale_test_right φ hφ hX hY h1 h2 h3 one_ne_zero one_ne_zero
  rw [hconst i j hij a ha]
  set p : Fin r := ⟨0, by omega⟩ with hp
  set q : Fin r := ⟨1, by omega⟩ with hq
  set m : Fin r := ⟨2, by omega⟩ with hm
  have hpq : p ≠ q := Fin.ne_of_val_ne (by simp [hp, hq])
  have hpm : p ≠ m := Fin.ne_of_val_ne (by simp [hp, hm])
  have hqm : q ≠ m := Fin.ne_of_val_ne (by simp [hq, hm])
  change S i j = S p q
  by_cases hiq : i = q
  · subst hiq
    by_cases hjm : j = m
    · subst hjm
      rw [hR2 q m p (Ne.symm hpm) hqm (Ne.symm hpq), hR1 q m p hqm (Ne.symm hpq) (Ne.symm hpm),
        hR2 m p q hpq (Ne.symm hpm) (Ne.symm hqm), hR1 m p q (Ne.symm hpm) (Ne.symm hqm) hpq]
    · rw [hR1 q m j hqm hij (Ne.symm hjm), hR2 m j q (fun h => hij h.symm) (Ne.symm hjm)
        (Ne.symm hqm), hR1 m p q (Ne.symm hpm) (Ne.symm hqm) hpq]
  ·
    have h1 : S i j = S i q := by
      by_cases hjq : j = q
      · rw [hjq]
      · exact hR2 i j q hjq hij hiq
    rw [h1]
    by_cases hip : i = p
    · rw [hip]
    · exact hR1 i p q hip hiq hpq

end Constancy


theorem orthogonal_geometry_split_point_rigidity {K : Type*} [Field K] {r : ℕ} (hr : 3 ≤ r)
    (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
    (hφ : ∀ L M : Points (quadPlus r K),
      PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val)
    (hX : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r → φ L = L)
    (hY : ∀ L : Points (quadPlus r K), L.val ≤ ySpan r K → φ L = L) :
    ∃ c : K, c ≠ 0 ∧
      (∀ (v : Fin r ⊕ Fin r → K) (hv0 : v ≠ 0) (hv : quadPlus r K v = 0),
        (φ (spanPoint hv0 hv)).val = K ∙ splitScale r K c v) ∧
      (∀ L : Points (quadPlus r K), (φ L).val = L.val.map (splitScale r K c)) ∧
      ∀ v : Fin r ⊕ Fin r → K, quadPlus r K (splitScale r K c v) = c * quadPlus r K v := by
  have hp1 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by simp)
  set c := rigScale φ hφ hX hY (rigTestVec r K ⟨0, by omega⟩ ⟨1, by omega⟩ 1) with hc
  have hc0 : c ≠ 0 := (rigScale_spec φ hφ hX hY (isMixed_rigTestVec hp1 one_ne_zero)).1
  have hmixed : ∀ v, IsMixed v → rigScale φ hφ hX hY v = c := by
    intro v h
    obtain ⟨i, j, hij, hxi, hyj⟩ := exists_inl_inr_ne h
    rw [rigScale_eq_test φ hφ hX hY h hij hxi hyj, rigScale_test_eq φ hφ hX hY hr hij
      (div_ne_zero (neg_ne_zero.2 hyj) hxi)]
  have hall : ∀ (v : Fin r ⊕ Fin r → K) (hv0 : v ≠ 0) (hv : quadPlus r K v = 0),
      (φ (spanPoint hv0 hv)).val = K ∙ splitScale r K c v := by
    intro v hv0 hv
    by_cases hm : IsMixed v
    · rw [← hmixed v hm]
      exact (rigScale_spec φ hφ hX hY hm).2
    · simp only [IsMixed, hv, true_and, not_and_or, not_exists, not_not] at hm
      rcases hm with hx | hy
      ·
        have hfix := hY (spanPoint hv0 hv) ((span_singleton_le_iff_mem _ _).2
          (mem_ySpan_iff.2 hx))
        rw [hfix]
        have hD : splitScale r K c v = c • v := funext fun x => by
          rcases x with i | i
          · simp [hx i]
          · simp
        rw [hD, span_singleton_smul_eq (IsUnit.mk0 _ hc0)]
        rfl
      ·
        have hfix := hX (spanPoint hv0 hv) ((span_singleton_le_iff_mem _ _).2
          (mem_flag_top_iff.2 hy))
        rw [hfix]
        have hD : splitScale r K c v = v := funext fun x => by
          rcases x with i | i
          · simp
          · simp [hy i]
        rw [hD]
        rfl
  refine ⟨c, hc0, hall, fun L => ?_, quadPlus_splitScale c⟩
  obtain ⟨v, hv0, hL⟩ := exists_eq_span_of_points L
  have hv : quadPlus r K v = 0 := L.2.2 v (by rw [hL]; exact mem_span_singleton_self v)
  have hLeq : L = spanPoint hv0 hv := Subtype.ext hL
  rw [hLeq, hall v hv0 hv]
  change _ = (K ∙ v).map _
  rw [Submodule.map_span, Set.image_singleton]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
