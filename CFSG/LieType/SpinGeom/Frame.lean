module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFix

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.ComponentClassification.CatalogueBOrthogonalPointData QuadraticMap
open scoped Matrix

section Vocabulary

variable (K : Type) [Field K]

@[expose] noncomputable def frameE (k : Fin 4) : Fin (2 * 4) → K :=
  AutOm.pvec k (decide (k ≠ 1))

@[expose] noncomputable def frameF (k : Fin 4) : Fin (2 * 4) → K :=
  AutOm.pvec k (!decide (k ≠ 1))

@[expose] noncomputable def coordX (v : Fin (2 * 4) → K) (k : Fin 4) : K :=
  polar (coordinateQuadPlus 4 K) v (frameF K k)

@[expose] noncomputable def coordY (v : Fin (2 * 4) → K) (k : Fin 4) : K :=
  polar (coordinateQuadPlus 4 K) v (frameE K k)

@[expose] noncomputable def frameVec (x₀ : K) (x y : Fin 3 → K) (y₀ : K) : Fin (2 * 4) → K :=
  x₀ • frameE K 0 + ∑ j : Fin 3, x j • frameE K j.succ + ∑ j : Fin 3, y j • frameF K j.succ +
    y₀ • frameF K 0

@[expose] def altMat (m : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, m 2, m 1; m 2, 0, m 0; m 1, m 0, 0]

@[expose] noncomputable def spinElt (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K)
    (v : Fin (2 * 4) → K) : Fin (2 * 4) → K :=
  frameVec K
    (coordX K v 0 + c ⬝ᵥ (g *ᵥ fun j => coordX K v j.succ) +
      m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ fun j => coordY K v j.succ) + coordY K v 0 * (c ⬝ᵥ m))
    ((g *ᵥ fun j => coordX K v j.succ) + coordY K v 0 • m)
    (((g.adjugate)ᵀ *ᵥ fun j => coordY K v j.succ) +
      altMat K m *ᵥ (g *ᵥ fun j => coordX K v j.succ) + coordY K v 0 • c)
    (coordY K v 0)

@[expose] noncomputable def elemMap (a b : Fin 4) (c : K) (v : Fin (2 * 4) → K) :
    Fin (2 * 4) → K :=
  v + (c * coordX K v b) • frameE K a + (c * coordY K v a) • frameF K b

@[expose] noncomputable def longMap (a b c d : Fin 4) (m : K) (v : Fin (2 * 4) → K) :
    Fin (2 * 4) → K :=
  v + (m * coordY K v b) • frameE K a + (m * coordY K v a) • frameE K b +
    (m * coordX K v d) • frameF K c + (m * coordX K v c) • frameF K d

end Vocabulary

section Frame

variable {K : Type} [Field K]

theorem polar_frameE_frameF (k l : Fin 4) :
    polar (coordinateQuadPlus 4 K) (frameE K k) (frameF K l) = if k = l then 1 else 0 := by
  unfold frameE frameF
  rw [AutOm.polar_pvec]
  by_cases h : k = l
  · subst h
    simp
  · simp [h]

theorem polar_frameF_frameE (k l : Fin 4) :
    polar (coordinateQuadPlus 4 K) (frameF K k) (frameE K l) = if k = l then 1 else 0 := by
  rw [polar_comm, polar_frameE_frameF, eq_comm]
  simp only [eq_comm]

theorem polar_frameE_frameE (k l : Fin 4) :
    polar (coordinateQuadPlus 4 K) (frameE K k) (frameE K l) = 0 := by
  unfold frameE
  rw [AutOm.polar_pvec]
  by_cases h : k = l
  · subst h
    simp
  · simp [h]

theorem polar_frameF_frameF (k l : Fin 4) :
    polar (coordinateQuadPlus 4 K) (frameF K k) (frameF K l) = 0 := by
  unfold frameF
  rw [AutOm.polar_pvec]
  by_cases h : k = l
  · subst h
    simp
  · simp [h]

theorem quad_pvec (k : Fin 4) (r : Bool) :
    coordinateQuadPlus 4 K (AutOm.pvec k r) = 0 := by
  change reindexQuadraticForm _ _ _ = 0
  rw [reindexQuadraticForm_map, CFSG.LieType.Universal.Spin.quadPlus_plusVec]

theorem quad_frameE (k : Fin 4) : coordinateQuadPlus 4 K (frameE K k) = 0 :=
  quad_pvec _ _

theorem quad_frameF (k : Fin 4) : coordinateQuadPlus 4 K (frameF K k) = 0 :=
  quad_pvec _ _

theorem pvec_eq_frame (k : Fin 4) (r : Bool) :
    (AutOm.pvec k r : Fin (2 * 4) → K) = frameE K k ∨ AutOm.pvec k r = frameF K k := by
  unfold frameE frameF
  cases r <;> cases h : decide (k ≠ 1) <;> simp

end Frame

section Coords

variable {K : Type} [Field K]

theorem coordX_add (v w : Fin (2 * 4) → K) (k : Fin 4) :
    coordX K (v + w) k = coordX K v k + coordX K w k :=
  polar_add_left _ _ _ _

theorem coordY_add (v w : Fin (2 * 4) → K) (k : Fin 4) :
    coordY K (v + w) k = coordY K v k + coordY K w k :=
  polar_add_left _ _ _ _

theorem coordX_smul (c : K) (v : Fin (2 * 4) → K) (k : Fin 4) :
    coordX K (c • v) k = c * coordX K v k := by
  rw [coordX, polar_smul_left, smul_eq_mul]
  rfl

theorem coordY_smul (c : K) (v : Fin (2 * 4) → K) (k : Fin 4) :
    coordY K (c • v) k = c * coordY K v k := by
  rw [coordY, polar_smul_left, smul_eq_mul]
  rfl

theorem coordX_zero (k : Fin 4) : coordX K (0 : Fin (2 * 4) → K) k = 0 :=
  polar_zero_left _ _

theorem coordY_zero (k : Fin 4) : coordY K (0 : Fin (2 * 4) → K) k = 0 :=
  polar_zero_left _ _

theorem coordX_sub (v w : Fin (2 * 4) → K) (k : Fin 4) :
    coordX K (v - w) k = coordX K v k - coordX K w k :=
  polar_sub_left _ _ _ _

theorem coordY_sub (v w : Fin (2 * 4) → K) (k : Fin 4) :
    coordY K (v - w) k = coordY K v k - coordY K w k :=
  polar_sub_left _ _ _ _

theorem coordX_sum {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * 4) → K) (k : Fin 4) :
    coordX K (∑ i ∈ s, f i) k = ∑ i ∈ s, coordX K (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordX_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, coordX_add, ih, Finset.sum_insert ha]

theorem coordY_sum {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * 4) → K) (k : Fin 4) :
    coordY K (∑ i ∈ s, f i) k = ∑ i ∈ s, coordY K (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordY_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, coordY_add, ih, Finset.sum_insert ha]

theorem coordX_frameE (k l : Fin 4) : coordX K (frameE K k) l = if k = l then 1 else 0 :=
  polar_frameE_frameF k l

theorem coordX_frameF (k l : Fin 4) : coordX K (frameF K k) l = 0 :=
  polar_frameF_frameF k l

theorem coordY_frameE (k l : Fin 4) : coordY K (frameE K k) l = 0 :=
  polar_frameE_frameE k l

theorem coordY_frameF (k l : Fin 4) : coordY K (frameF K k) l = if k = l then 1 else 0 :=
  polar_frameF_frameE k l

theorem coordX_frameVec (x₀ : K) (x y : Fin 3 → K) (y₀ : K) (k : Fin 4) :
    coordX K (frameVec K x₀ x y y₀) k =
      x₀ * (if (0 : Fin 4) = k then 1 else 0) +
        ∑ j : Fin 3, x j * (if j.succ = k then 1 else 0) := by
  unfold frameVec
  rw [coordX_add, coordX_add, coordX_add, coordX_smul, coordX_smul, coordX_sum, coordX_sum,
    coordX_frameE, coordX_frameF]
  have h1 : ∑ j : Fin 3, coordX K (x j • frameE K j.succ) k =
      ∑ j : Fin 3, x j * (if j.succ = k then 1 else 0) :=
    Finset.sum_congr rfl fun j _ => by rw [coordX_smul, coordX_frameE]
  have h2 : ∑ j : Fin 3, coordX K (y j • frameF K j.succ) k = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [coordX_smul, coordX_frameF, mul_zero]
  rw [h1, h2]
  ring

theorem coordY_frameVec (x₀ : K) (x y : Fin 3 → K) (y₀ : K) (k : Fin 4) :
    coordY K (frameVec K x₀ x y y₀) k =
      y₀ * (if (0 : Fin 4) = k then 1 else 0) +
        ∑ j : Fin 3, y j * (if j.succ = k then 1 else 0) := by
  unfold frameVec
  rw [coordY_add, coordY_add, coordY_add, coordY_smul, coordY_smul, coordY_sum, coordY_sum,
    coordY_frameE, coordY_frameF]
  have h1 : ∑ j : Fin 3, coordY K (y j • frameF K j.succ) k =
      ∑ j : Fin 3, y j * (if j.succ = k then 1 else 0) :=
    Finset.sum_congr rfl fun j _ => by rw [coordY_smul, coordY_frameF]
  have h2 : ∑ j : Fin 3, coordY K (x j • frameE K j.succ) k = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [coordY_smul, coordY_frameE, mul_zero]
  rw [h1, h2]
  ring

theorem coordX_frameVec_zero (x₀ : K) (x y : Fin 3 → K) (y₀ : K) :
    coordX K (frameVec K x₀ x y y₀) 0 = x₀ := by
  rw [coordX_frameVec]
  simp [Fin.succ_ne_zero]

theorem coordX_frameVec_succ (x₀ : K) (x y : Fin 3 → K) (y₀ : K) (j : Fin 3) :
    coordX K (frameVec K x₀ x y y₀) j.succ = x j := by
  rw [coordX_frameVec]
  simp [(Fin.succ_ne_zero j).symm, Fin.succ_inj]

theorem coordY_frameVec_zero (x₀ : K) (x y : Fin 3 → K) (y₀ : K) :
    coordY K (frameVec K x₀ x y y₀) 0 = y₀ := by
  rw [coordY_frameVec]
  simp [Fin.succ_ne_zero]

theorem coordY_frameVec_succ (x₀ : K) (x y : Fin 3 → K) (y₀ : K) (j : Fin 3) :
    coordY K (frameVec K x₀ x y y₀) j.succ = y j := by
  rw [coordY_frameVec]
  simp [(Fin.succ_ne_zero j).symm, Fin.succ_inj]

end Coords

section Expansion

variable {K : Type} [Field K]

theorem vec_eq_sum (v : Fin (2 * 4) → K) :
    v = ∑ k : Fin 4, (coordX K v k • frameE K k + coordY K v k • frameF K k) := by
  rw [← sub_eq_zero]
  apply AutOm.eq_zero_of_polar_pvec
  intro l t
  rcases pvec_eq_frame (K := K) l t with h | h
  · rw [h]
    show coordY K _ l = 0
    rw [coordY_sub, coordY_sum]
    have h1 : ∀ x : Fin 4, coordY K (coordX K v x • frameE K x + coordY K v x • frameF K x) l =
        coordY K v x * (if x = l then 1 else 0) := fun x => by
      rw [coordY_add, coordY_smul, coordY_smul, coordY_frameE, coordY_frameF]
      ring
    simp only [h1]
    simp
  · rw [h]
    show coordX K _ l = 0
    rw [coordX_sub, coordX_sum]
    have h1 : ∀ x : Fin 4, coordX K (coordX K v x • frameE K x + coordY K v x • frameF K x) l =
        coordX K v x * (if x = l then 1 else 0) := fun x => by
      rw [coordX_add, coordX_smul, coordX_smul, coordX_frameE, coordX_frameF]
      ring
    simp only [h1]
    simp

theorem vec_ext {v w : Fin (2 * 4) → K} (hx : ∀ k, coordX K v k = coordX K w k)
    (hy : ∀ k, coordY K v k = coordY K w k) : v = w := by
  rw [vec_eq_sum v, vec_eq_sum w]
  exact Finset.sum_congr rfl fun k _ => by rw [hx k, hy k]

theorem frameVec_coords (v : Fin (2 * 4) → K) :
    frameVec K (coordX K v 0) (fun j => coordX K v j.succ) (fun j => coordY K v j.succ)
      (coordY K v 0) = v := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [coordX_frameVec_zero]
    · rw [coordX_frameVec_succ]
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [coordY_frameVec_zero]
    · rw [coordY_frameVec_succ]

end Expansion

section Quad

variable {K : Type} [Field K]

theorem polar_pvec_false_right (v : Fin (2 * 4) → K) (k : Fin 4) :
    polar (coordinateQuadPlus 4 K) v (AutOm.pvec k false) = v (plusIndexEquiv 4 (.inl k)) := by
  obtain ⟨y, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective v
  rw [AutOm.pvec_false, ← AutOm.reindex_single, AutOm.polar_reindex_plus,
    CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr, reindexVectorEquiv_apply,
    Equiv.symm_apply_apply]

theorem polar_pvec_true_right (v : Fin (2 * 4) → K) (k : Fin 4) :
    polar (coordinateQuadPlus 4 K) v (AutOm.pvec k true) = v (plusIndexEquiv 4 (.inr k)) := by
  obtain ⟨y, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective v
  rw [AutOm.pvec_true, ← AutOm.reindex_single, AutOm.polar_reindex_plus,
    CFSG.LieType.Universal.Spin.polar_quadPlus_single_inl, reindexVectorEquiv_apply,
    Equiv.symm_apply_apply]

theorem quad_eq_sum (v : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K v = ∑ k : Fin 4, coordX K v k * coordY K v k := by
  rw [coordinateQuadPlus_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = 1
  · subst hk
    simp only [coordX, coordY, frameE, frameF]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false]
    rw [polar_pvec_true_right, polar_pvec_false_right, mul_comm]
  · simp only [coordX, coordY, frameE, frameF, ne_eq, hk, not_false_eq_true, decide_true,
      Bool.not_true]
    rw [polar_pvec_false_right, polar_pvec_true_right]

end Quad

end CFSG.LieType.SpinGeom
