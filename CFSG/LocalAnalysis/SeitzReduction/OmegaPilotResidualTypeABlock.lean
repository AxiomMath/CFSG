module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeARep

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply)
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

variable {K : Type} [Field K] {n ℓ m : ℕ}

section Coord

@[expose] def blockShift (h : ℓ + m = n) (a : Fin m) : Fin n :=
  ⟨ℓ + a.val, by have := a.isLt; omega⟩

theorem blockShift_val (h : ℓ + m = n) (a : Fin m) : (blockShift h a).val = ℓ + a.val :=
  rfl

theorem blockShift_injective (h : ℓ + m = n) : Function.Injective (blockShift h) := by
  intro a b hab
  have := congrArg Fin.val hab
  rw [blockShift_val, blockShift_val] at this
  exact Fin.ext (by omega)

theorem exists_blockShift_eq (h : ℓ + m = n) {i : Fin n} (hi : ℓ ≤ i.val) :
    ∃ a, blockShift h a = i :=
  ⟨⟨i.val - ℓ, by have := i.isLt; omega⟩, Fin.ext (by simp only [blockShift_val]; omega)⟩

@[expose] noncomputable def blockCoord (h : ℓ + m = n) (x : Fin (2 * m)) : Fin (2 * n) :=
  plusIndexEquiv n (Sum.map (blockShift h) (blockShift h) ((plusIndexEquiv m).symm x))

theorem blockCoord_inl (h : ℓ + m = n) (a : Fin m) :
    blockCoord h (plusIndexEquiv m (.inl a)) = plusIndexEquiv n (.inl (blockShift h a)) := by
  simp [blockCoord]

theorem blockCoord_inr (h : ℓ + m = n) (a : Fin m) :
    blockCoord h (plusIndexEquiv m (.inr a)) = plusIndexEquiv n (.inr (blockShift h a)) := by
  simp [blockCoord]

theorem blockCoord_injective (h : ℓ + m = n) : Function.Injective (blockCoord h) := by
  intro x y hxy
  have h1 := (plusIndexEquiv n).injective hxy
  have h2 := (Sum.map_injective.mpr ⟨blockShift_injective h, blockShift_injective h⟩) h1
  exact (plusIndexEquiv m).symm.injective h2

theorem mem_range_blockCoord_iff (h : ℓ + m = n) (c : Fin (2 * n)) :
    c ∈ Set.range (blockCoord h) ↔
      ∃ i : Fin n, ℓ ≤ i.val ∧ (c = plusIndexEquiv n (.inl i) ∨ c = plusIndexEquiv n (.inr i)) := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨s, rfl⟩ := (plusIndexEquiv m).surjective x
    rcases s with a | a
    · exact ⟨blockShift h a, Nat.le_add_right ℓ a.val, Or.inl (blockCoord_inl h a)⟩
    · exact ⟨blockShift h a, Nat.le_add_right ℓ a.val, Or.inr (blockCoord_inr h a)⟩
  · rintro ⟨i, hi, hc | hc⟩
    · obtain ⟨a, rfl⟩ := exists_blockShift_eq h hi
      exact ⟨plusIndexEquiv m (.inl a), (blockCoord_inl h a).trans hc.symm⟩
    · obtain ⟨a, rfl⟩ := exists_blockShift_eq h hi
      exact ⟨plusIndexEquiv m (.inr a), (blockCoord_inr h a).trans hc.symm⟩

theorem inl_not_mem_range_blockCoord (h : ℓ + m = n) {i : Fin n} (hi : i.val < ℓ) :
    plusIndexEquiv n (.inl i) ∉ Set.range (blockCoord h) := by
  rw [mem_range_blockCoord_iff]
  rintro ⟨j, hj, hc | hc⟩
  · have := Sum.inl_injective ((plusIndexEquiv n).injective hc)
    subst this
    omega
  · exact Sum.inl_ne_inr ((plusIndexEquiv n).injective hc)

theorem inr_not_mem_range_blockCoord (h : ℓ + m = n) {i : Fin n} (hi : i.val < ℓ) :
    plusIndexEquiv n (.inr i) ∉ Set.range (blockCoord h) := by
  rw [mem_range_blockCoord_iff]
  rintro ⟨j, hj, hc | hc⟩
  · exact Sum.inr_ne_inl ((plusIndexEquiv n).injective hc)
  · have := Sum.inr_injective ((plusIndexEquiv n).injective hc)
    subst this
    omega

omit [Field K] in
theorem add_comp_blockCoord [Add K] (h : ℓ + m = n) (v w : Fin (2 * n) → K) :
    (v + w) ∘ blockCoord h = v ∘ blockCoord h + w ∘ blockCoord h :=
  rfl

omit [Field K] in
theorem sub_comp_blockCoord [Sub K] (h : ℓ + m = n) (v w : Fin (2 * n) → K) :
    (v - w) ∘ blockCoord h = v ∘ blockCoord h - w ∘ blockCoord h :=
  rfl

theorem extend_blockCoord_comp (h : ℓ + m = n) (w : Fin (2 * m) → K) :
    Function.extend (blockCoord h) w 0 ∘ blockCoord h = w :=
  Function.extend_comp (blockCoord_injective h) w 0

theorem extend_blockCoord_mem_lowPerp (h : ℓ + m = n) (w : Fin (2 * m) → K) :
    Function.extend (blockCoord h) w 0 ∈ lowPerp K n ℓ := fun _ hi =>
  Function.extend_apply' _ _ _ (inr_not_mem_range_blockCoord h hi)

theorem comp_blockCoord_eq_zero_of_mem_lowSpan (h : ℓ + m = n) {v : Fin (2 * n) → K}
    (hv : v ∈ lowSpan K n ℓ) : v ∘ blockCoord h = 0 := by
  funext x
  obtain ⟨s, rfl⟩ := (plusIndexEquiv m).surjective x
  rcases s with a | a
  · rw [Function.comp_apply, blockCoord_inl, Pi.zero_apply]
    exact (hv _).2 (Nat.le_add_right ℓ a.val)
  · rw [Function.comp_apply, blockCoord_inr, Pi.zero_apply]
    exact (hv _).1

theorem mem_lowSpan_of_mem_lowPerp (h : ℓ + m = n) {v : Fin (2 * n) → K}
    (hv : v ∈ lowPerp K n ℓ) (hb : v ∘ blockCoord h = 0) : v ∈ lowSpan K n ℓ := by
  intro i
  by_cases hi : i.val < ℓ
  · exact ⟨hv i hi, fun h' => absurd h' (by omega)⟩
  · obtain ⟨a, rfl⟩ := exists_blockShift_eq h (not_lt.mp hi)
    refine ⟨?_, fun _ => ?_⟩
    · have := congrFun hb (plusIndexEquiv m (.inr a))
      rwa [Function.comp_apply, blockCoord_inr, Pi.zero_apply] at this
    · have := congrFun hb (plusIndexEquiv m (.inl a))
      rwa [Function.comp_apply, blockCoord_inl, Pi.zero_apply] at this

theorem sub_extend_mem_lowSpan (h : ℓ + m = n) {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ) :
    v - Function.extend (blockCoord h) (v ∘ blockCoord h) 0 ∈ lowSpan K n ℓ := by
  refine mem_lowSpan_of_mem_lowPerp h
    (Submodule.sub_mem _ hv (extend_blockCoord_mem_lowPerp h _)) ?_
  rw [sub_comp_blockCoord, extend_blockCoord_comp, sub_self]

theorem coordinateQuadPlus_eq_add (h : ℓ + m = n) (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K v = (∑ i : Fin n, if i.val < ℓ then
      v (plusIndexEquiv n (.inl i)) * v (plusIndexEquiv n (.inr i)) else 0) +
      coordinateQuadPlus m K (v ∘ blockCoord h) := by
  have key : ∑ a : Fin m, (v ∘ blockCoord h) (plusIndexEquiv m (.inl a)) *
      (v ∘ blockCoord h) (plusIndexEquiv m (.inr a)) =
      ∑ i : Fin n, if i.val < ℓ then 0 else
        v (plusIndexEquiv n (.inl i)) * v (plusIndexEquiv n (.inr i)) := by
    refine Fintype.sum_of_injective (blockShift h) (blockShift_injective h) _ _
      (fun i hi => ?_) (fun a => ?_)
    · rw [ite_eq_left]
      by_contra hlt
      exact hi (exists_blockShift_eq h (not_lt.mp hlt))
    · simp only [Function.comp_apply, blockCoord_inl, blockCoord_inr]
      split_ifs with hlt
      · exact absurd hlt (not_lt.mpr (Nat.le_add_right ℓ a.val))
      · rfl
  rw [coordinateQuadPlus_apply n K v, coordinateQuadPlus_apply m K (v ∘ blockCoord h), key,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem coordinateQuadPlus_of_mem_lowPerp (h : ℓ + m = n) {v : Fin (2 * n) → K}
    (hv : v ∈ lowPerp K n ℓ) :
    coordinateQuadPlus n K v = coordinateQuadPlus m K (v ∘ blockCoord h) := by
  rw [coordinateQuadPlus_eq_add h, Finset.sum_eq_zero, zero_add]
  intro i _
  split_ifs with hi
  · rw [hv i hi, mul_zero]
  · rfl

theorem coordinateQuadPlus_extend_blockCoord (h : ℓ + m = n) (w : Fin (2 * m) → K) :
    coordinateQuadPlus n K (Function.extend (blockCoord h) w 0) = coordinateQuadPlus m K w := by
  rw [coordinateQuadPlus_of_mem_lowPerp h (extend_blockCoord_mem_lowPerp h w),
    extend_blockCoord_comp]

omit [Field K] in
theorem ext_blockCoord (h : ℓ + m = n) {v w : Fin (2 * n) → K}
    (h1 : v ∘ blockCoord h = w ∘ blockCoord h)
    (h2 : ∀ c ∉ Set.range (blockCoord h), v c = w c) : v = w := by
  funext c
  by_cases hc : c ∈ Set.range (blockCoord h)
  · obtain ⟨x, rfl⟩ := hc
    exact congrFun h1 x
  · exact h2 c hc

end Coord

section Extend

@[expose] noncomputable def blockLin (h : ℓ + m = n)
    (g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) :
    (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) where
  toFun v := Function.extend (blockCoord h) (g (v ∘ blockCoord h)) v
  map_add' v w := by
    funext c
    by_cases hc : ∃ x, blockCoord h x = c
    · obtain ⟨x, rfl⟩ := hc
      simp only [Pi.add_apply, (blockCoord_injective h).extend_apply]
      rw [add_comp_blockCoord, map_add, Pi.add_apply]
    · simp only [Pi.add_apply, Function.extend_apply' _ _ _ hc]
  map_smul' c v := by
    funext d
    by_cases hd : ∃ x, blockCoord h x = d
    · obtain ⟨x, rfl⟩ := hd
      simp only [Pi.smul_apply, (blockCoord_injective h).extend_apply, RingHom.id_apply]
      rw [show (c • v) ∘ blockCoord h = c • (v ∘ blockCoord h) from rfl, map_smul, Pi.smul_apply]
    · simp only [Pi.smul_apply, Function.extend_apply' _ _ _ hd, RingHom.id_apply]

theorem blockLin_apply_blockCoord (h : ℓ + m = n) (g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K))
    (v : Fin (2 * n) → K) (x : Fin (2 * m)) :
    blockLin h g v (blockCoord h x) = g (v ∘ blockCoord h) x :=
  (blockCoord_injective h).extend_apply _ _ x

theorem blockLin_apply_of_not_mem (h : ℓ + m = n)
    (g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) (v : Fin (2 * n) → K) {c : Fin (2 * n)}
    (hc : c ∉ Set.range (blockCoord h)) : blockLin h g v c = v c :=
  Function.extend_apply' _ _ _ hc

theorem blockLin_comp_blockCoord (h : ℓ + m = n)
    (g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) (v : Fin (2 * n) → K) :
    blockLin h g v ∘ blockCoord h = g (v ∘ blockCoord h) :=
  funext fun x => blockLin_apply_blockCoord h g v x

theorem blockLin_comp (h : ℓ + m = n) (g g' : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) :
    blockLin h (g ∘ₗ g') = blockLin h g ∘ₗ blockLin h g' := by
  refine LinearMap.ext fun v => ext_blockCoord h ?_ fun c hc => ?_
  · simp only [LinearMap.comp_apply, blockLin_comp_blockCoord]
  · simp only [LinearMap.comp_apply, blockLin_apply_of_not_mem h _ _ hc]

theorem blockLin_id (h : ℓ + m = n) :
    blockLin h (LinearMap.id : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) = LinearMap.id := by
  refine LinearMap.ext fun v => ext_blockCoord h ?_ fun c hc => ?_
  · rw [blockLin_comp_blockCoord]
    rfl
  · rw [blockLin_apply_of_not_mem h _ _ hc]
    rfl

@[expose] noncomputable def blockExtend (h : ℓ + m = n) :
    ((Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) →*
      ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) where
  toFun g := LinearEquiv.ofLinearMap (blockLin h g) (blockLin h g.symm)
    (by rw [← blockLin_comp, LinearEquiv.comp_symm, blockLin_id])
    (by rw [← blockLin_comp, LinearEquiv.symm_comp, blockLin_id])
  map_one' := LinearEquiv.ext fun v => by
    change blockLin h LinearMap.id v = v
    rw [blockLin_id, LinearMap.id_apply]
  map_mul' g g' := LinearEquiv.ext fun v => by
    change blockLin h ((g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) ∘ₗ
      (g' : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K))) v = blockLin h g (blockLin h g' v)
    rw [blockLin_comp, LinearMap.comp_apply]

theorem blockExtend_apply_of_not_mem (h : ℓ + m = n)
    (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) (v : Fin (2 * n) → K) {c : Fin (2 * n)}
    (hc : c ∉ Set.range (blockCoord h)) : blockExtend h g v c = v c :=
  blockLin_apply_of_not_mem h (g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) v hc

theorem blockExtend_comp_blockCoord (h : ℓ + m = n)
    (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) (v : Fin (2 * n) → K) :
    blockExtend h g v ∘ blockCoord h = g (v ∘ blockCoord h) :=
  blockLin_comp_blockCoord h (g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) v

theorem blockExtend_apply_inl (h : ℓ + m = n) (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K))
    (v : Fin (2 * n) → K) {i : Fin n} (hi : i.val < ℓ) :
    blockExtend h g v (plusIndexEquiv n (.inl i)) = v (plusIndexEquiv n (.inl i)) :=
  blockExtend_apply_of_not_mem h g v (inl_not_mem_range_blockCoord h hi)

theorem blockExtend_apply_inr (h : ℓ + m = n) (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K))
    (v : Fin (2 * n) → K) {i : Fin n} (hi : i.val < ℓ) :
    blockExtend h g v (plusIndexEquiv n (.inr i)) = v (plusIndexEquiv n (.inr i)) :=
  blockExtend_apply_of_not_mem h g v (inr_not_mem_range_blockCoord h hi)

theorem blockExtend_apply_of_comp_eq_zero (h : ℓ + m = n)
    (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) {v : Fin (2 * n) → K}
    (hv : v ∘ blockCoord h = 0) : blockExtend h g v = v :=
  ext_blockCoord h (by rw [blockExtend_comp_blockCoord, hv, map_zero]) fun _ hc =>
    blockExtend_apply_of_not_mem h g v hc

theorem blockExtend_apply_of_mem_lowSpan (h : ℓ + m = n)
    (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) {v : Fin (2 * n) → K}
    (hv : v ∈ lowSpan K n ℓ) : blockExtend h g v = v :=
  blockExtend_apply_of_comp_eq_zero h g (comp_blockCoord_eq_zero_of_mem_lowSpan h hv)

theorem blockExtend_mem_orthogonalGroup (h : ℓ + m = n)
    {g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m K)) :
    blockExtend h g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [coordinateQuadPlus_eq_add h (blockExtend h g v), coordinateQuadPlus_eq_add h v,
    blockExtend_comp_blockCoord, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [blockExtend_apply_inl h g v hi, blockExtend_apply_inr h g v hi]
  · rfl

theorem map_orthDerived_blockExtend_le (h : ℓ + m = n) :
    (orthDerived (coordinateQuadPlus m K)).map (blockExtend h) ≤
      orthDerived (coordinateQuadPlus n K) := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m K)).map (blockExtend h) ≤
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) := by
    rintro _ ⟨g, hg, rfl⟩
    exact blockExtend_mem_orthogonalGroup h hg
  rw [orthDerived, Subgroup.map_commutator]
  exact Subgroup.commutator_mono hle hle

end Extend

section Part

@[expose] noncomputable def blockPart (h : ℓ + m = n)
    (g : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) :
    (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K) :=
  LinearMap.funLeft K K (blockCoord h) ∘ₗ g ∘ₗ Function.ExtendByZero.linearMap K (blockCoord h)

theorem blockPart_apply (h : ℓ + m = n) (g : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K))
    (w : Fin (2 * m) → K) :
    blockPart h g w = (g (Function.extend (blockCoord h) w 0)) ∘ blockCoord h :=
  rfl

theorem comp_blockCoord_of_mem_lowPerp (h : ℓ + m = n)
    {g : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)}
    (hg : ∀ v ∈ lowSpan K n ℓ, g v ∈ lowSpan K n ℓ) {v : Fin (2 * n) → K}
    (hv : v ∈ lowPerp K n ℓ) : g v ∘ blockCoord h = blockPart h g (v ∘ blockCoord h) := by
  have hu := hg _ (sub_extend_mem_lowSpan h hv)
  calc g v ∘ blockCoord h
      = g (v - Function.extend (blockCoord h) (v ∘ blockCoord h) 0) ∘ blockCoord h +
        g (Function.extend (blockCoord h) (v ∘ blockCoord h) 0) ∘ blockCoord h := by
        rw [← add_comp_blockCoord, ← map_add, sub_add_cancel]
    _ = blockPart h g (v ∘ blockCoord h) := by
        rw [comp_blockCoord_eq_zero_of_mem_lowSpan h hu, zero_add, blockPart_apply]

theorem blockPart_comp (h : ℓ + m = n) {g g' : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)}
    (hg : ∀ v ∈ lowSpan K n ℓ, g v ∈ lowSpan K n ℓ)
    (hg' : ∀ v ∈ lowPerp K n ℓ, g' v ∈ lowPerp K n ℓ) :
    blockPart h (g ∘ₗ g') = blockPart h g ∘ₗ blockPart h g' :=
  LinearMap.ext fun w =>
    comp_blockCoord_of_mem_lowPerp h hg (hg' _ (extend_blockCoord_mem_lowPerp h w))

theorem blockPart_id (h : ℓ + m = n) :
    blockPart h (LinearMap.id : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) = LinearMap.id :=
  LinearMap.ext fun w => extend_blockCoord_comp h w

theorem blockPart_blockExtend (h : ℓ + m = n) (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) :
    blockPart h (blockExtend h g : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) =
      (g : (Fin (2 * m) → K) →ₗ[K] (Fin (2 * m) → K)) := by
  refine LinearMap.ext fun w => ?_
  rw [blockPart_apply]
  simp only [LinearEquiv.coe_coe]
  rw [blockExtend_comp_blockCoord, extend_blockCoord_comp]

theorem coordinateQuadPlus_blockPart (h : ℓ + m = n)
    {g : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)}
    (hg : ∀ v, coordinateQuadPlus n K (g v) = coordinateQuadPlus n K v)
    (hgP : ∀ v ∈ lowPerp K n ℓ, g v ∈ lowPerp K n ℓ) (w : Fin (2 * m) → K) :
    coordinateQuadPlus m K (blockPart h g w) = coordinateQuadPlus m K w := by
  rw [blockPart_apply,
    ← coordinateQuadPlus_of_mem_lowPerp h (hgP _ (extend_blockCoord_mem_lowPerp h w)), hg,
    coordinateQuadPlus_extend_blockCoord]

theorem blockPart_eq_id_iff (h : ℓ + m = n) {g : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)}
    (hgW : ∀ v ∈ lowSpan K n ℓ, g v ∈ lowSpan K n ℓ)
    (hgP : ∀ v ∈ lowPerp K n ℓ, g v ∈ lowPerp K n ℓ) :
    blockPart h g = LinearMap.id ↔ ∀ v ∈ lowPerp K n ℓ, g v - v ∈ lowSpan K n ℓ := by
  constructor
  · intro hid v hv
    refine mem_lowSpan_of_mem_lowPerp h (Submodule.sub_mem _ (hgP v hv) hv) ?_
    rw [sub_comp_blockCoord, comp_blockCoord_of_mem_lowPerp h hgW hv, hid, LinearMap.id_apply,
      sub_self]
  · intro hW
    refine LinearMap.ext fun w => ?_
    have h0 := comp_blockCoord_eq_zero_of_mem_lowSpan h
      (hW _ (extend_blockCoord_mem_lowPerp h w))
    rw [sub_comp_blockCoord, sub_eq_zero, extend_blockCoord_comp] at h0
    rw [blockPart_apply, h0, LinearMap.id_apply]

end Part

section OrthOne

theorem coordinateQuadPlus_one_apply (v : Fin (2 * 1) → K) :
    coordinateQuadPlus 1 K v = v (plusIndexEquiv 1 (.inl 0)) * v (plusIndexEquiv 1 (.inr 0)) := by
  rw [coordinateQuadPlus_apply, Fin.sum_univ_one]

theorem eq_smul_single_add_smul_single_one (v : Fin (2 * 1) → K) :
    v = v (plusIndexEquiv 1 (.inl 0)) • Pi.single (plusIndexEquiv 1 (.inl 0)) (1 : K) +
      v (plusIndexEquiv 1 (.inr 0)) • Pi.single (plusIndexEquiv 1 (.inr 0)) (1 : K) := by
  refine ext_plus (fun i => ?_) fun i => ?_ <;> obtain rfl := Subsingleton.elim i 0 <;> simp

theorem orthOne_cases_aux {a b c d : K} (h1 : a * c = 0) (h2 : b * d = 0)
    (h3 : (a + b) * (c + d) = 1) :
    (c = 0 ∧ b = 0 ∧ a * d = 1) ∨ (a = 0 ∧ d = 0 ∧ b * c = 1) := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by linear_combination h3 - h2
    exact Or.inl ⟨rfl, by simpa [right_ne_zero_of_mul_eq_one had] using h2, had⟩
  · have ha : a = 0 := by simpa [hc] using h1
    subst ha
    have hbc : b * c = 1 := by linear_combination h3 - h2
    exact Or.inr ⟨rfl, by simpa [left_ne_zero_of_mul_eq_one hbc] using h2, hbc⟩

theorem orthOne_cases {g : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K)) :
    (g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inr 0)) = 0 ∧
      g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1) (plusIndexEquiv 1 (.inl 0)) = 0 ∧
      g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inl 0)) *
        g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1) (plusIndexEquiv 1 (.inr 0)) = 1) ∨
    (g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inl 0)) = 0 ∧
      g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1) (plusIndexEquiv 1 (.inr 0)) = 0 ∧
      g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1) (plusIndexEquiv 1 (.inl 0)) *
        g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inr 0)) = 1) := by
  have h1 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg
    (Pi.single (plusIndexEquiv 1 (.inl 0)) 1)
  have h2 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg
    (Pi.single (plusIndexEquiv 1 (.inr 0)) 1)
  have h3 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg
    (Pi.single (plusIndexEquiv 1 (.inl 0)) 1 + Pi.single (plusIndexEquiv 1 (.inr 0)) 1)
  simp only [coordinateQuadPlus_one_apply, map_add, Pi.add_apply, Pi.single_eq_same,
    single_inl_apply_inr, single_inr_apply_inl, mul_zero, add_zero, zero_add, mul_one] at h1 h2 h3
  exact orthOne_cases_aux h1 h2 h3

open Classical in
@[expose] noncomputable def orthOneType (g : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)) :
    ZMod 2 :=
  if g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inr 0)) = 0 then 0 else 1

theorem orthOneType_one : orthOneType (1 : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)) = 0 := by
  simp [orthOneType, LinearEquiv.coe_one]

theorem mul_single_inl_apply_inr_one (g g' : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)) :
    (g * g') (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inr 0)) =
      g' (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inl 0)) *
        g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inr 0)) +
      g' (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inr 0)) *
        g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1) (plusIndexEquiv 1 (.inr 0)) := by
  rw [LinearEquiv.mul_apply]
  conv_lhs => rw [eq_smul_single_add_smul_single_one (g' (Pi.single (plusIndexEquiv 1 (.inl 0)) 1))]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem orthOneType_mul {g g' : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K))
    (hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K)) :
    orthOneType (g * g') = orthOneType g + orthOneType g' := by
  unfold orthOneType
  rw [mul_single_inl_apply_inr_one]
  rcases orthOne_cases hg with ⟨hc, hb, had⟩ | ⟨ha, hd, hbc⟩ <;>
    rcases orthOne_cases hg' with ⟨hc', hb', had'⟩ | ⟨ha', hd', hbc'⟩
  · simp [hc, hc']
  · simp [hc, ha', right_ne_zero_of_mul_eq_one hbc', right_ne_zero_of_mul_eq_one had]
  · simp [hc', left_ne_zero_of_mul_eq_one had', right_ne_zero_of_mul_eq_one hbc]
  · simp [ha', hd, right_ne_zero_of_mul_eq_one hbc, right_ne_zero_of_mul_eq_one hbc']
    decide

theorem orthOneType_commutatorElement {g₁ g₂ : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)}
    (h₁ : g₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K))
    (h₂ : g₂ ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K)) :
    orthOneType ⁅g₁, g₂⁆ = 0 := by
  have e₁ := orthOneType_mul h₁ (inv_mem h₁)
  have e₂ := orthOneType_mul h₂ (inv_mem h₂)
  rw [mul_inv_cancel, orthOneType_one] at e₁ e₂
  rw [commutatorElement_def, orthOneType_mul (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂),
    orthOneType_mul (mul_mem h₁ h₂) (inv_mem h₁), orthOneType_mul h₁ h₂]
  linear_combination -e₁ - e₂

variable (K) in
@[expose] noncomputable def orthOneDiag :
    Subgroup ((Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K) ∧
    orthOneType g = 0}
  one_mem' := ⟨one_mem _, orthOneType_one⟩
  mul_mem' := fun {_ _} hg hg' => ⟨mul_mem hg.1 hg'.1, by
    rw [orthOneType_mul hg.1 hg'.1, hg.2, hg'.2, add_zero]⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, by
    have e := orthOneType_mul hg.1 (inv_mem hg.1)
    rw [mul_inv_cancel, orthOneType_one, hg.2, zero_add] at e
    exact e.symm⟩

theorem commutatorElement_mem_orthOneDiag {g₁ g₂ : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)}
    (h₁ : g₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K))
    (h₂ : g₂ ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K)) :
    ⁅g₁, g₂⁆ ∈ orthOneDiag K :=
  ⟨by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂),
    orthOneType_commutatorElement h₁ h₂⟩

theorem exists_diag_of_mem_orthOneDiag {g : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)}
    (hg : g ∈ orthOneDiag K) :
    ∃ a d : K, g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) =
        a • Pi.single (plusIndexEquiv 1 (.inl 0)) 1 ∧
      g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1) =
        d • Pi.single (plusIndexEquiv 1 (.inr 0)) 1 := by
  obtain ⟨hO, ht⟩ := hg
  have hc : g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inr 0)) = 0 := by
    by_contra hne
    unfold orthOneType at ht
    rw [ite_eq_right hne] at ht
    exact absurd ht (by decide)
  rcases orthOne_cases hO with ⟨-, hb, -⟩ | ⟨-, -, hbc⟩
  · refine ⟨g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1) (plusIndexEquiv 1 (.inl 0)),
      g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1) (plusIndexEquiv 1 (.inr 0)), ?_, ?_⟩
    · conv_lhs => rw [eq_smul_single_add_smul_single_one
        (g (Pi.single (plusIndexEquiv 1 (.inl 0)) 1))]
      rw [hc, zero_smul, add_zero]
    · conv_lhs => rw [eq_smul_single_add_smul_single_one
        (g (Pi.single (plusIndexEquiv 1 (.inr 0)) 1))]
      rw [hb, zero_smul, zero_add]
  · rw [hc, mul_zero] at hbc
    exact absurd hbc zero_ne_one

theorem commute_of_mem_orthOneDiag {g g' : (Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K)}
    (hg : g ∈ orthOneDiag K) (hg' : g' ∈ orthOneDiag K) : g * g' = g' * g := by
  obtain ⟨a, d, hE, hF⟩ := exists_diag_of_mem_orthOneDiag hg
  obtain ⟨a', d', hE', hF'⟩ := exists_diag_of_mem_orthOneDiag hg'
  refine Module.Basis.ext' (Pi.basisFun K (Fin (2 * 1))) fun c => ?_
  obtain ⟨s, rfl⟩ := (plusIndexEquiv 1).surjective c
  rw [Pi.basisFun_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rcases s with i | i <;> obtain rfl := Subsingleton.elim i 0
  · rw [hE', map_smul, hE, map_smul, hE', smul_smul, smul_smul, mul_comm a' a]
  · rw [hF', map_smul, hF, map_smul, hF', smul_smul, smul_smul, mul_comm d' d]

theorem eq_bot_of_commutator_eq_self_of_le_orthogonalGroup_one
    {H : Subgroup ((Fin (2 * 1) → K) ≃ₗ[K] (Fin (2 * 1) → K))}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 1 K))
    (hperf : ⁅H, H⁆ = H) : H = ⊥ := by
  have hD : H ≤ orthOneDiag K := by
    rw [← hperf]
    exact Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ =>
      commutatorElement_mem_orthOneDiag (hH h₁) (hH h₂)
  rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro g' hg'
  exact commute_of_mem_orthOneDiag (hD hg') (hD hg)

end OrthOne

end CFSG.SeitzReduction.OmegaPilot
