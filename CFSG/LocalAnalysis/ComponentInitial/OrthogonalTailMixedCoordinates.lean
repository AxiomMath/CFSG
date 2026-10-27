module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailLinearRigidity

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
  (Points pointMk pointMk_submodule exists_eq_pointMk)

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

section HPoints

variable {q : QuadraticForm K A}

variable (q) in
@[expose] noncomputable def hPoint (L : Points (quadPlus r K)) : Points (quadTail r q) :=
  ⟨L.val.map (LinearMap.inl K (Fin r ⊕ Fin r → K) A), by
    rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
      (LinearMap.inl K (Fin r ⊕ Fin r → K) A) LinearMap.inl_injective L.val)]
    exact L.2.1, by
    rintro _ ⟨u, hu, rfl⟩
    rw [LinearMap.inl_apply, quadTail_apply, L.2.2 u hu, QuadraticMap.map_zero, add_zero]⟩

theorem hPoint_val (L : Points (quadPlus r K)) :
    (hPoint q L).val = L.val.map (LinearMap.inl K (Fin r ⊕ Fin r → K) A) :=
  rfl

theorem eq_map_inl_map_fst {M : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hM : ∀ x ∈ M, x.2 = 0) :
    M = (M.map (LinearMap.fst K (Fin r ⊕ Fin r → K) A)).map
      (LinearMap.inl K (Fin r ⊕ Fin r → K) A) := by
  ext x
  constructor
  · intro hx
    refine ⟨x.1, ⟨x, hx, rfl⟩, ?_⟩
    rw [LinearMap.inl_apply]
    exact Prod.ext rfl (hM x hx).symm
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have : (LinearMap.inl K (Fin r ⊕ Fin r → K) A) ((LinearMap.fst K _ A) y) = y :=
      Prod.ext rfl (hM y hy).symm
    rw [this]
    exact hy

@[expose] noncomputable def splitPart (M : Points (quadTail r q)) (hM : ∀ x ∈ M.val, x.2 = 0) :
    Points (quadPlus r K) :=
  ⟨M.val.map (LinearMap.fst K (Fin r ⊕ Fin r → K) A), by
    have h1 : finrank K ((M.val.map (LinearMap.fst K (Fin r ⊕ Fin r → K) A)).map
        (LinearMap.inl K (Fin r ⊕ Fin r → K) A)) =
          finrank K (M.val.map (LinearMap.fst K (Fin r ⊕ Fin r → K) A)) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
        (LinearMap.inl K (Fin r ⊕ Fin r → K) A) LinearMap.inl_injective _)).symm
    rw [← h1, ← eq_map_inl_map_fst hM]
    exact M.2.1, by
    rintro _ ⟨y, hy, rfl⟩
    have h := M.2.2 y hy
    rw [quadTail_apply, hM y hy, QuadraticMap.map_zero, add_zero] at h
    exact h⟩

theorem splitPart_val (M : Points (quadTail r q)) (hM : ∀ x ∈ M.val, x.2 = 0) :
    (splitPart M hM).val = M.val.map (LinearMap.fst K (Fin r ⊕ Fin r → K) A) :=
  rfl

theorem hPoint_splitPart (M : Points (quadTail r q)) (hM : ∀ x ∈ M.val, x.2 = 0) :
    hPoint q (splitPart M hM) = M :=
  Subtype.ext (eq_map_inl_map_fst hM).symm

theorem splitPart_hPoint (L : Points (quadPlus r K)) (h : ∀ x ∈ (hPoint q L).val, x.2 = 0) :
    splitPart (hPoint q L) h = L := by
  refine Subtype.ext ?_
  change (L.val.map (LinearMap.inl K _ A)).map (LinearMap.fst K _ A) = L.val
  rw [← Submodule.map_comp, LinearMap.fst_comp_inl, Submodule.map_id]

theorem snd_eq_zero_of_mem_hPoint {L : Points (quadPlus r K)} {x : (Fin r ⊕ Fin r → K) × A}
    (hx : x ∈ (hPoint q L).val) : x.2 = 0 := by
  obtain ⟨u, -, rfl⟩ := hx
  rfl

theorem polarOrtho_hPoint (L M : Points (quadPlus r K)) :
    PolarOrtho (quadTail r q) (hPoint q L).val (hPoint q M).val ↔
      PolarOrtho (quadPlus r K) L.val M.val := by
  constructor
  · intro h u hu v hv
    have := h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rwa [LinearMap.inl_apply, LinearMap.inl_apply, polar_quadTail, polar_zero_left,
      add_zero] at this
  · rintro h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [LinearMap.inl_apply, LinearMap.inl_apply, polar_quadTail, polar_zero_left, add_zero]
    exact h u hu v hv

theorem hPoint_spanPoint {u : Fin r ⊕ Fin r → K} (hu0 : u ≠ 0) (hu : quadPlus r K u = 0) :
    (hPoint q (spanPoint hu0 hu)).val = K ∙ ((u, 0) : (Fin r ⊕ Fin r → K) × A) := by
  rw [hPoint_val]
  change (K ∙ u).map _ = _
  rw [Submodule.map_span, Set.image_singleton, LinearMap.inl_apply]

end HPoints

theorem eq_zero_of_dotProduct_right_iff {y y' : Fin r → K} (hy : y = 0)
    (h : ∀ t : Fin r → K, t ⬝ᵥ y = 0 ↔ t ⬝ᵥ y' = 0) : y' = 0 :=
  funext fun i => by
    have := (h (Pi.single i 1)).1 (by rw [hy, dotProduct_zero])
    rwa [single_dotProduct, one_mul] at this

theorem eq_zero_of_dotProduct_left_iff {x x' : Fin r → K} (hx : x = 0)
    (h : ∀ t : Fin r → K, x ⬝ᵥ t = 0 ↔ x' ⬝ᵥ t = 0) : x' = 0 :=
  eq_zero_of_dotProduct_right_iff hx fun t => by
    rw [dotProduct_comm t, dotProduct_comm t]
    exact h t

theorem exists_smul_eq_of_dotProduct_left_iff {x x' : Fin r → K} (hx : x ≠ 0)
    (h : ∀ t : Fin r → K, x ⬝ᵥ t = 0 ↔ x' ⬝ᵥ t = 0) : ∃ l : K, l ≠ 0 ∧ x' = l • x :=
  exists_smul_eq_of_dotProduct_iff hx fun t => by
    rw [dotProduct_comm t, dotProduct_comm t]
    exact h t

section Shape

variable {q q' : QuadraticForm K A}
  (φ : Points (quadTail r q) ≃ Points (quadTail r q'))
  (hφ : ∀ L M : Points (quadTail r q),
    PolarOrtho (quadTail r q) L.val M.val ↔ PolarOrtho (quadTail r q') (φ L).val (φ M).val)
  (hX : ∀ L : Points (quadTail r q), L.val ≤ (flag r K r).prod ⊥ → (φ L).val = L.val)
  (hY : ∀ L : Points (quadTail r q), L.val ≤ (ySpan r K).prod ⊥ → (φ L).val = L.val)
include hφ hX hY

theorem dotProduct_iff_of_image {v : (Fin r ⊕ Fin r → K) × A} (hv0 : v ≠ 0)
    (hv : quadTail r q v = 0) {w : (Fin r ⊕ Fin r → K) × A}
    (hw : (φ (pointMk v hv0 hv)).val = K ∙ w) :
    (∀ t : Fin r → K, t ⬝ᵥ (fun i => v.1 (.inr i)) = 0 ↔ t ⬝ᵥ (fun i => w.1 (.inr i)) = 0) ∧
    ∀ t : Fin r → K, (fun i => v.1 (.inl i)) ⬝ᵥ t = 0 ↔ (fun i => w.1 (.inl i)) ⬝ᵥ t = 0 := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases ht : t = 0
    · simp [ht]
    have hu0 : ((Sum.elim t 0 : Fin r ⊕ Fin r → K), (0 : A)) ≠ 0 := fun h => ht (funext fun i => by
      simpa using congrFun (congrArg Prod.fst h) (Sum.inl i))
    have huQ : quadTail r q ((Sum.elim t 0 : Fin r ⊕ Fin r → K), (0 : A)) = 0 := by
      simp [quadTail_apply, quadPlus_apply]
    have hle : (pointMk (Q := quadTail r q) _ hu0 huQ).val ≤ (flag r K r).prod ⊥ := by
      rw [pointMk_submodule, span_singleton_le_iff_mem, Submodule.mem_prod]
      exact ⟨mem_flag_top_iff.2 fun i => rfl, Submodule.zero_mem _⟩
    have h := hφ (pointMk v hv0 hv) (pointMk _ hu0 huQ)
    rw [hX _ hle, hw, pointMk_submodule, pointMk_submodule, polarOrtho_span_singleton_iff_polar,
      polarOrtho_span_singleton_iff_polar, polar_quadTail, polar_quadTail] at h
    dsimp only at h
    simp only [polar_zero_right, add_zero, polar_inl_left] at h
    exact h
  · by_cases ht : t = 0
    · simp [ht]
    have hu0 : ((Sum.elim 0 t : Fin r ⊕ Fin r → K), (0 : A)) ≠ 0 := fun h => ht (funext fun i => by
      simpa using congrFun (congrArg Prod.fst h) (Sum.inr i))
    have huQ : quadTail r q ((Sum.elim 0 t : Fin r ⊕ Fin r → K), (0 : A)) = 0 := by
      simp [quadTail_apply, quadPlus_apply]
    have hle : (pointMk (Q := quadTail r q) _ hu0 huQ).val ≤ (ySpan r K).prod ⊥ := by
      rw [pointMk_submodule, span_singleton_le_iff_mem, Submodule.mem_prod]
      exact ⟨mem_ySpan_iff.2 fun i => rfl, Submodule.zero_mem _⟩
    have h := hY _ hle
    have h' := hφ (pointMk v hv0 hv) (pointMk _ hu0 huQ)
    rw [h, hw, pointMk_submodule, pointMk_submodule, polarOrtho_span_singleton_iff_polar,
      polarOrtho_span_singleton_iff_polar, polar_quadTail, polar_quadTail] at h'
    dsimp only at h'
    simp only [polar_zero_right, add_zero, polar_inr_left] at h'
    exact h'

theorem snd_eq_zero_of_image (hani' : q'.Anisotropic) {v : (Fin r ⊕ Fin r → K) × A}
    (hv0 : v ≠ 0) (hv : quadTail r q v = 0) (hva : v.2 = 0) {w : (Fin r ⊕ Fin r → K) × A}
    (hw : (φ (pointMk v hv0 hv)).val = K ∙ w) : w.2 = 0 := by
  obtain ⟨h1, h2⟩ := dotProduct_iff_of_image φ hφ hX hY hv0 hv hw
  have hwQ : quadTail r q' w = 0 :=
    (φ (pointMk v hv0 hv)).2.2 w (by rw [hw]; exact mem_span_singleton_self w)
  have hxy : (fun i => v.1 (.inl i)) ⬝ᵥ (fun i => v.1 (.inr i)) = 0 := by
    rw [quadTail_apply, hva, QuadraticMap.map_zero, add_zero, quadPlus_apply] at hv
    exact hv
  have hxy' : (fun i => w.1 (.inl i)) ⬝ᵥ (fun i => w.1 (.inr i)) = 0 := by
    by_cases hy : (fun i => v.1 (.inr i)) = 0
    · rw [eq_zero_of_dotProduct_right_iff hy h1, dotProduct_zero]
    by_cases hx : (fun i => v.1 (.inl i)) = 0
    · rw [eq_zero_of_dotProduct_left_iff hx h2, zero_dotProduct]
    obtain ⟨l, -, hly⟩ := exists_smul_eq_of_dotProduct_iff hy h1
    obtain ⟨m, -, hmx⟩ := exists_smul_eq_of_dotProduct_left_iff hx h2
    rw [hly, hmx, smul_dotProduct, dotProduct_smul, hxy, smul_zero, smul_zero]
  rw [quadTail_apply, quadPlus_apply] at hwQ
  have hq : q' w.2 = 0 := by
    have : ∑ i, w.1 (.inl i) * w.1 (.inr i) = 0 := hxy'
    rw [this, zero_add] at hwQ
    exact hwQ
  exact hani' _ hq

theorem snd_eq_zero_of_mem_image_hPoint (hani' : q'.Anisotropic) (L : Points (quadPlus r K)) :
    ∀ x ∈ (φ (hPoint q L)).val, x.2 = 0 := by
  obtain ⟨u, hu0, hL⟩ := exists_eq_span_of_points L
  have hu : quadPlus r K u = 0 := L.2.2 u (by rw [hL]; exact mem_span_singleton_self u)
  have hv0 : ((u, 0) : (Fin r ⊕ Fin r → K) × A) ≠ 0 := fun h => hu0 (congrArg Prod.fst h)
  have hv : quadTail r q ((u, 0) : (Fin r ⊕ Fin r → K) × A) = 0 := by
    rw [quadTail_apply, hu, QuadraticMap.map_zero, add_zero]
  have hLeq : hPoint q L = pointMk _ hv0 hv := Subtype.ext (by
    rw [hPoint_val, pointMk_submodule, hL, Submodule.map_span, Set.image_singleton,
      LinearMap.inl_apply])
  obtain ⟨w, hw0, hwQ, hwe⟩ := exists_eq_pointMk (φ (pointMk _ hv0 hv))
  have hw : (φ (pointMk _ hv0 hv)).val = K ∙ w := by rw [hwe, pointMk_submodule]
  have hw2 := snd_eq_zero_of_image φ hφ hX hY hani' hv0 hv rfl hw
  rw [hLeq, hw]
  intro x hx
  obtain ⟨t, rfl⟩ := mem_span_singleton.1 hx
  rw [Prod.smul_snd, hw2, smul_zero]

end Shape

section HEquiv

variable {q₁ q₂ : QuadraticForm K A}
  (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))

theorem symm_fix_of_fix {S : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hS : ∀ x ∈ S, quadTail r q₁ x = 0)
    (hfix : ∀ L : Points (quadTail r q₁), L.val ≤ S → (φ L).val = L.val)
    (L : Points (quadTail r q₂)) (hL : L.val ≤ S) : (φ.symm L).val = L.val := by
  set L' : Points (quadTail r q₁) := ⟨L.val, L.2.1, fun x hx => hS x (hL hx)⟩
  have h : φ L' = L := Subtype.ext (hfix L' hL)
  rw [← h, Equiv.symm_apply_apply]
  exact (hfix L' hL).symm

theorem polarOrtho_symm_iff
    (hφ : ∀ L M : Points (quadTail r q₁),
      PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val)
    (L M : Points (quadTail r q₂)) :
    PolarOrtho (quadTail r q₂) L.val M.val ↔
      PolarOrtho (quadTail r q₁) (φ.symm L).val (φ.symm M).val := by
  rw [hφ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem quadTail_eq_zero_of_mem_xSpan {x : (Fin r ⊕ Fin r → K) × A}
    (hx : x ∈ (flag r K r).prod (⊥ : Submodule K A)) : quadTail r q₁ x = 0 := by
  obtain ⟨h1, h2⟩ := Submodule.mem_prod.1 hx
  rw [quadTail_apply, quadPlus_eq_zero_of_mem_flag h1, (Submodule.mem_bot K).1 h2,
    QuadraticMap.map_zero, add_zero]

theorem quadTail_eq_zero_of_mem_ySpan {x : (Fin r ⊕ Fin r → K) × A}
    (hx : x ∈ (ySpan r K).prod (⊥ : Submodule K A)) : quadTail r q₁ x = 0 := by
  obtain ⟨h1, h2⟩ := Submodule.mem_prod.1 hx
  rw [quadTail_apply, (Submodule.mem_bot K).1 h2, QuadraticMap.map_zero, add_zero,
    quadPlus_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [mem_ySpan_iff.1 h1 i, zero_mul]

variable (hani₁ : q₁.Anisotropic) (hani₂ : q₂.Anisotropic)
  (hφ : ∀ L M : Points (quadTail r q₁),
    PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val)
  (hX : ∀ L : Points (quadTail r q₁), L.val ≤ (flag r K r).prod ⊥ → (φ L).val = L.val)
  (hY : ∀ L : Points (quadTail r q₁), L.val ≤ (ySpan r K).prod ⊥ → (φ L).val = L.val)

@[expose] noncomputable def hEquiv : Points (quadPlus r K) ≃ Points (quadPlus r K) where
  toFun L := splitPart (φ (hPoint q₁ L)) (snd_eq_zero_of_mem_image_hPoint φ hφ hX hY hani₂ L)
  invFun L := splitPart (φ.symm (hPoint q₂ L)) (snd_eq_zero_of_mem_image_hPoint φ.symm
    (polarOrtho_symm_iff φ hφ) (symm_fix_of_fix φ (fun _ hx => quadTail_eq_zero_of_mem_xSpan hx) hX)
    (symm_fix_of_fix φ (fun _ hx => quadTail_eq_zero_of_mem_ySpan hx) hY) hani₁ L)
  left_inv L := by
    refine Subtype.ext ?_
    dsimp only
    rw [splitPart_val, hPoint_splitPart, Equiv.symm_apply_apply, hPoint_val,
      ← Submodule.map_comp, LinearMap.fst_comp_inl, Submodule.map_id]
  right_inv L := by
    refine Subtype.ext ?_
    dsimp only
    rw [splitPart_val, hPoint_splitPart, Equiv.apply_symm_apply, hPoint_val,
      ← Submodule.map_comp, LinearMap.fst_comp_inl, Submodule.map_id]

theorem hPoint_hEquiv (L : Points (quadPlus r K)) :
    hPoint q₂ (hEquiv φ hani₁ hani₂ hφ hX hY L) = φ (hPoint q₁ L) :=
  hPoint_splitPart _ (snd_eq_zero_of_mem_image_hPoint φ hφ hX hY hani₂ L)

theorem polarOrtho_hEquiv (L M : Points (quadPlus r K)) :
    PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K)
      (hEquiv φ hani₁ hani₂ hφ hX hY L).val (hEquiv φ hani₁ hani₂ hφ hX hY M).val := by
  rw [← polarOrtho_hPoint (q := q₁), hφ, ← hPoint_hEquiv φ hani₁ hani₂ hφ hX hY,
    ← hPoint_hEquiv φ hani₁ hani₂ hφ hX hY, polarOrtho_hPoint]

theorem hEquiv_fix_x (L : Points (quadPlus r K)) (hL : L.val ≤ flag r K r) :
    hEquiv φ hani₁ hani₂ hφ hX hY L = L := by
  have hle : (hPoint q₁ L).val ≤ (flag r K r).prod ⊥ := by
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.mem_prod.2 ⟨hL hu, Submodule.zero_mem _⟩
  refine Subtype.ext ?_
  rw [hEquiv, Equiv.coe_fn_mk, splitPart_val, hX _ hle, hPoint_val, ← Submodule.map_comp,
    LinearMap.fst_comp_inl, Submodule.map_id]

theorem hEquiv_fix_y (L : Points (quadPlus r K)) (hL : L.val ≤ ySpan r K) :
    hEquiv φ hani₁ hani₂ hφ hX hY L = L := by
  have hle : (hPoint q₁ L).val ≤ (ySpan r K).prod ⊥ := by
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.mem_prod.2 ⟨hL hu, Submodule.zero_mem _⟩
  refine Subtype.ext ?_
  rw [hEquiv, Equiv.coe_fn_mk, splitPart_val, hY _ hle, hPoint_val, ← Submodule.map_comp,
    LinearMap.fst_comp_inl, Submodule.map_id]

end HEquiv

theorem splitScale_ne_zero {c : K} (hc : c ≠ 0) {u : Fin r ⊕ Fin r → K} (hu : u ≠ 0) :
    splitScale r K c u ≠ 0 := fun h => hu (funext fun x => by
  rcases x with i | i
  · simpa using congrFun h (Sum.inl i)
  · have := congrFun h (Sum.inr i)
    rw [splitScale_inr, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left hc)

theorem orthogonal_geometry_tail_mixed_coordinates {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] {r : ℕ} (hr : 3 ≤ r) {q₁ q₂ : QuadraticForm K A}
    (hani₁ : q₁.Anisotropic) (hani₂ : q₂.Anisotropic)
    (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))
    (hφ : ∀ L M : Points (quadTail r q₁),
      PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val)
    (hX : ∀ L : Points (quadTail r q₁), L.val ≤ (flag r K r).prod ⊥ → (φ L).val = L.val)
    (hY : ∀ L : Points (quadTail r q₁), L.val ≤ (ySpan r K).prod ⊥ → (φ L).val = L.val) :
    ∃ c : K, c ≠ 0 ∧ ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0),
      (∃! b : A, (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val =
        K ∙ (splitScale r K c v.1, b)) ∧
      ∀ b : A, (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val =
          K ∙ (splitScale r K c v.1, b) → q₂ b = c * q₁ v.2 ∧ (v.2 = 0 → b = 0) := by
  obtain ⟨c, hc, hall, -, -⟩ := orthogonal_geometry_split_point_rigidity hr
    (hEquiv φ hani₁ hani₂ hφ hX hY) (polarOrtho_hEquiv φ hani₁ hani₂ hφ hX hY)
    (hEquiv_fix_x φ hani₁ hani₂ hφ hX hY) (hEquiv_fix_y φ hani₁ hani₂ hφ hX hY)
  have hH : ∀ (u : Fin r ⊕ Fin r → K) (hu0 : u ≠ 0) (hu : quadPlus r K u = 0)
      (hv0 : ((u, 0) : (Fin r ⊕ Fin r → K) × A) ≠ 0) (hv : quadTail r q₁ (u, 0) = 0),
      (φ (pointMk _ hv0 hv)).val =
        K ∙ ((splitScale r K c u, 0) : (Fin r ⊕ Fin r → K) × A) := by
    intro u hu0 hu hv0 hv
    have hpt : pointMk (Q := quadTail r q₁) _ hv0 hv = hPoint q₁ (spanPoint hu0 hu) :=
      Subtype.ext (by rw [pointMk_submodule, hPoint_spanPoint])
    rw [hpt, ← hPoint_hEquiv φ hani₁ hani₂ hφ hX hY, hPoint_val, hall u hu0 hu,
      Submodule.map_span, Set.image_singleton, LinearMap.inl_apply]
  have hex : ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0),
      ∃ b : A, (φ (pointMk _ hv0 hv)).val = K ∙ (splitScale r K c v.1, b) := by
    rintro ⟨u, a⟩ hv0 hv
    by_cases ha : a = 0
    · subst ha
      have hu0 : u ≠ 0 := fun h => hv0 (by rw [h]; rfl)
      have hu : quadPlus r K u = 0 := by
        rw [quadTail_apply, QuadraticMap.map_zero, add_zero] at hv
        exact hv
      exact ⟨0, hH u hu0 hu hv0 hv⟩
    have hxy : (fun i => u (Sum.inl i)) ⬝ᵥ (fun i => u (Sum.inr i)) = -q₁ a := by
      rw [quadTail_apply, quadPlus_apply] at hv
      change (∑ i, u (Sum.inl i) * u (Sum.inr i)) = _
      linear_combination hv
    have hqa : q₁ a ≠ 0 := fun h => ha (hani₁ a h)
    have hx : (fun i => u (Sum.inl i)) ≠ 0 := fun h => hqa (by
      rw [h, zero_dotProduct] at hxy
      linear_combination hxy)
    have hy : (fun i => u (Sum.inr i)) ≠ 0 := fun h => hqa (by
      rw [h, dotProduct_zero] at hxy
      linear_combination hxy)
    obtain ⟨w, hw0, hwQ, hwe⟩ := exists_eq_pointMk (φ (pointMk _ hv0 hv))
    have hw : (φ (pointMk _ hv0 hv)).val = K ∙ w := by rw [hwe, pointMk_submodule]
    obtain ⟨h1, h2⟩ := dotProduct_iff_of_image φ hφ hX hY hv0 hv hw
    obtain ⟨l, hl, hly⟩ := exists_smul_eq_of_dotProduct_iff hy h1
    obtain ⟨m, hm, hmx⟩ := exists_smul_eq_of_dotProduct_left_iff hx h2
    set s := l / m with hs
    have hw' : (φ (pointMk _ hv0 hv)).val = K ∙ (splitScale r K s u, m⁻¹ • w.2) := by
      have hwe' : w = m • ((splitScale r K s u, m⁻¹ • w.2) : (Fin r ⊕ Fin r → K) × A) := by
        refine Prod.ext (funext fun x => ?_) ?_
        · rcases x with i | i
          · have := congrFun hmx i
            simp only [Pi.smul_apply, smul_eq_mul] at this
            simp [this]
          · have := congrFun hly i
            simp only [Pi.smul_apply, smul_eq_mul] at this
            simp only [this, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, splitScale_inr, hs]
            field_simp
        · simp [smul_smul, mul_inv_cancel₀ hm]
      rw [hw]
      conv_lhs => rw [hwe']
      rw [span_singleton_smul_eq (IsUnit.mk0 _ hm)]
    have hscal : ∀ (T : Fin r ⊕ Fin r → K) (hT0 : T ≠ 0) (hT : quadPlus r K T = 0),
        polar (quadPlus r K) u T = 0 →
        (fun i => u (Sum.inl i)) ⬝ᵥ (fun i => T (Sum.inr i)) ≠ 0 → s = c := by
      intro T hT0 hT horth hcross
      have hTv0 : ((T, 0) : (Fin r ⊕ Fin r → K) × A) ≠ 0 := fun h => hT0 (congrArg Prod.fst h)
      have hTv : quadTail r q₁ ((T, 0) : (Fin r ⊕ Fin r → K) × A) = 0 := by
        rw [quadTail_apply, hT, QuadraticMap.map_zero, add_zero]
      have horth' : polar (quadTail r q₁) (u, a) (T, 0) = 0 := by
        rw [polar_quadTail]
        dsimp only
        rw [horth, polar_zero_right, add_zero]
      have h := (hφ (pointMk _ hv0 hv) (pointMk _ hTv0 hTv)).1 (by
        rw [pointMk_submodule, pointMk_submodule]
        exact polarOrtho_span_singleton_iff_polar.2 horth')
      rw [hw', hH T hT0 hT hTv0 hTv, polarOrtho_span_singleton_iff_polar, polar_quadTail] at h
      dsimp only at h
      rw [polar_zero_right, add_zero, polar_quadPlus_eq_dotProduct] at h
      rw [polar_quadPlus_eq_dotProduct] at horth
      have e1 : (fun i => splitScale r K s u (Sum.inl i)) ⬝ᵥ
          (fun i => splitScale r K c T (Sum.inr i)) =
            c * ((fun i => u (Sum.inl i)) ⬝ᵥ (fun i => T (Sum.inr i))) := by
        simp only [splitScale_inl, splitScale_inr, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : (fun i => splitScale r K c T (Sum.inl i)) ⬝ᵥ
          (fun i => splitScale r K s u (Sum.inr i)) =
            s * ((fun i => T (Sum.inl i)) ⬝ᵥ (fun i => u (Sum.inr i))) := by
        simp only [splitScale_inl, splitScale_inr, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, e2] at h
      have : (c - s) * ((fun i => u (Sum.inl i)) ⬝ᵥ (fun i => T (Sum.inr i))) = 0 := by
        linear_combination h - s * horth
      rcases mul_eq_zero.1 this with h0 | h0
      · exact (sub_eq_zero.1 h0).symm
      · exact absurd h0 hcross
    have hsc : s = c := by
      by_cases hij : ∃ i j : Fin r, i ≠ j ∧ u (Sum.inl i) ≠ 0 ∧ u (Sum.inr j) ≠ 0
      · obtain ⟨i, j, hij, hxi, hyj⟩ := hij
        have ht : -u (Sum.inr j) / u (Sum.inl i) ≠ 0 := div_ne_zero (neg_ne_zero.2 hyj) hxi
        have hmix := isMixed_rigTestVec (K := K) hij ht
        refine hscal _ hmix.ne_zero hmix.1 ?_ ?_
        · rw [polar_quadPlus_eq_dotProduct]
          simp only [rigTestVec_inl, rigTestVec_inr, dotProduct, mul_ite, mul_zero, ite_mul,
            zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          field_simp
          ring
        · simp only [rigTestVec_inr, dotProduct, mul_ite, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true]
          field_simp
          exact neg_ne_zero.2 hyj
      · simp only [not_exists, not_and, not_not] at hij
        obtain ⟨i, hxi⟩ := Function.ne_iff.1 hx
        have hxi' : u (Sum.inl i) ≠ 0 := hxi
        have hyj0 : ∀ j, j ≠ i → u (Sum.inr j) = 0 := fun j hj => hij i j (Ne.symm hj) hxi'
        have hyi : u (Sum.inr i) ≠ 0 := fun h0 => hy (funext fun j => by
          by_cases hj : j = i
          · rw [hj]
            exact h0
          · exact hyj0 j hj)
        have hxk0 : ∀ k, k ≠ i → u (Sum.inl k) = 0 := fun k hk => by
          by_contra hxk
          exact hyi (hij k i hk hxk)
        obtain ⟨j, hji, -⟩ := exists_third_index hr i i
        set t := -u (Sum.inr i) / u (Sum.inl i) with ht
        have ht0 : t ≠ 0 := div_ne_zero (neg_ne_zero.2 hyi) hxi'
        set f : Fin r → K := Pi.single i 1 + Pi.single j 1 with hf
        set g : Fin r → K := t • (Pi.single i 1 - Pi.single j 1) with hg
        have hfg : f ⬝ᵥ g = 0 := by
          rw [hf, hg, dotProduct_smul, add_dotProduct, dotProduct_sub, dotProduct_sub,
            single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
          simp [hji, Ne.symm hji]
        have hW0 : (Sum.elim f g : Fin r ⊕ Fin r → K) ≠ 0 := fun h0 => by
          have := congrFun h0 (Sum.inl i)
          simp [hf, Ne.symm hji] at this
        have hW : quadPlus r K (Sum.elim f g) = 0 := by
          rw [quadPlus_apply]
          exact hfg
        have hxg : (fun k => u (Sum.inl k)) ⬝ᵥ g = t * u (Sum.inl i) := by
          rw [hg, dotProduct_smul, dotProduct_sub, dotProduct_single, dotProduct_single,
            hxk0 j hji, smul_eq_mul]
          ring
        refine hscal _ hW0 hW ?_ ?_
        · rw [polar_quadPlus_eq_dotProduct]
          change (fun k => u (Sum.inl k)) ⬝ᵥ g + f ⬝ᵥ (fun k => u (Sum.inr k)) = 0
          rw [hxg, hf, add_dotProduct, single_dotProduct, single_dotProduct, hyj0 j hji, ht]
          field_simp
          ring
        · change (fun k => u (Sum.inl k)) ⬝ᵥ g ≠ 0
          rw [hxg]
          exact mul_ne_zero ht0 hxi'
    exact ⟨m⁻¹ • w.2, by rw [hw', hsc]⟩
  have hnorm : ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0)
      (b : A), (φ (pointMk _ hv0 hv)).val = K ∙ (splitScale r K c v.1, b) →
        q₂ b = c * q₁ v.2 := by
    intro v hv0 hv b hb
    have hQ := (φ (pointMk _ hv0 hv)).2.2 (splitScale r K c v.1, b)
      (by rw [hb]; exact mem_span_singleton_self _)
    rw [quadTail_apply, quadPlus_splitScale] at hQ
    rw [quadTail_apply] at hv
    linear_combination hQ - c * hv
  refine ⟨c, hc, fun v hv0 hv => ⟨?_, fun b hb => ⟨hnorm v hv0 hv b hb, fun hva =>
    hani₂ b (by rw [hnorm v hv0 hv b hb, hva, QuadraticMap.map_zero, mul_zero])⟩⟩⟩
  obtain ⟨b, hb⟩ := hex v hv0 hv
  refine ⟨b, hb, fun b' hb' => ?_⟩
  have hv1 : v.1 ≠ 0 := fun h => by
    have hq : q₁ v.2 = 0 := by
      rw [quadTail_apply, h, QuadraticMap.map_zero, zero_add] at hv
      exact hv
    exact hv0 (Prod.ext h (hani₁ _ hq))
  have hmem : ((splitScale r K c v.1, b') : (Fin r ⊕ Fin r → K) × A) ∈
      K ∙ ((splitScale r K c v.1, b) : (Fin r ⊕ Fin r → K) × A) := by
    rw [← hb, hb']
    exact mem_span_singleton_self _
  obtain ⟨μ, hμ⟩ := mem_span_singleton.1 hmem
  have h1 : (μ - 1) • splitScale r K c v.1 = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact congrArg Prod.fst hμ
  have hμ1 : μ = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right (splitScale_ne_zero hc hv1))
  have h2 := congrArg Prod.snd hμ
  rw [hμ1] at h2
  simpa using h2.symm

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
