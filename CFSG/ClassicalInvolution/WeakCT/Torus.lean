module

public import CFSG.ClassicalInvolution.WeakCT.Blocks

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix
open scoped MatrixGroups

section Torus2

variable (K : Type) [Field K]

@[expose] def torusHom : Kˣ →* SL(2, K) where
  toFun s := ⟨!![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    refine Subtype.ext ?_
    show !![((s * t : Kˣ) : K), 0; 0, (((s * t)⁻¹ : Kˣ) : K)] =
      !![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] * !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

variable {K}

theorem coe_torusHom (s : Kˣ) : ((torusHom K s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
    !![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] :=
  rfl

theorem torusHom_injective : Function.Injective (torusHom K) := by
  intro s t h
  have := congrFun (congrFun (congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) h) 0) 0
  exact Units.ext (by simpa [coe_torusHom] using this)

variable (K)

@[expose] def diagTorus2 : Subgroup SL(2, K) :=
  (torusHom K).range

@[expose] def D12 : Subgroup SL(3, K) :=
  (diagTorus2 K).map (blockSL K 3 2 0 (by omega))

@[expose] def D23 : Subgroup SL(3, K) :=
  (diagTorus2 K).map (blockSL K 3 2 1 (by omega))

variable {K}

theorem mem_diagTorus2_iff {A : SL(2, K)} : A ∈ diagTorus2 K ↔ ∃ s : Kˣ, torusHom K s = A :=
  MonoidHom.mem_range

theorem mem_diagTorus2_of_offDiag (A : SL(2, K)) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    A ∈ diagTorus2 K := by
  have hdet : A 0 0 * A 1 1 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two, h01, h10] at this
    simpa using this
  refine ⟨Units.mk (A 0 0) (A 1 1) hdet (by rw [mul_comm]; exact hdet), ?_⟩
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusHom, h01, h10]

end Torus2

section Torus3

variable {K : Type} [Field K]

theorem mem_D12_iff {g : SL(3, K)} :
    g ∈ D12 K ↔ ∃ u : Kˣ, blockSL K 3 2 0 (by omega) (torusHom K u) = g := by
  simp only [D12, diagTorus2, Subgroup.mem_map, MonoidHom.mem_range]
  exact ⟨fun ⟨_, ⟨u, rfl⟩, h⟩ => ⟨u, h⟩, fun ⟨u, h⟩ => ⟨_, ⟨u, rfl⟩, h⟩⟩

theorem mem_D23_iff {g : SL(3, K)} :
    g ∈ D23 K ↔ ∃ u : Kˣ, blockSL K 3 2 1 (by omega) (torusHom K u) = g := by
  simp only [D23, diagTorus2, Subgroup.mem_map, MonoidHom.mem_range]
  exact ⟨fun ⟨_, ⟨u, rfl⟩, h⟩ => ⟨u, h⟩, fun ⟨u, h⟩ => ⟨_, ⟨u, rfl⟩, h⟩⟩

theorem D12_le_B12 : D12 K ≤ B12 K :=
  Subgroup.map_le_range _ _

theorem D23_le_B23 : D23 K ≤ B23 K :=
  Subgroup.map_le_range _ _

theorem map_D12 {X : Type*} [Group X] (θ : SL(3, K) →* X) :
    (D12 K).map θ = (diagTorus2 K).map (θ.comp (blockSL K 3 2 0 (by omega))) :=
  Subgroup.map_map _ _ _

theorem map_D23 {X : Type*} [Group X] (θ : SL(3, K) →* X) :
    (D23 K).map θ = (diagTorus2 K).map (θ.comp (blockSL K 3 2 1 (by omega))) :=
  Subgroup.map_map _ _ _

theorem blockSL_torus_comm (s t : Kˣ) :
    blockSL K 3 2 0 (by omega) (torusHom K s) * blockSL K 3 2 1 (by omega) (torusHom K t) =
      blockSL K 3 2 1 (by omega) (torusHom K t) * blockSL K 3 2 0 (by omega) (torusHom K s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      coe_blockSL_three_zero, coe_blockSL_three_one, coe_torusHom, mul_comm]

theorem D12_D23_comm {a t : SL(3, K)} (ha : a ∈ D12 K) (ht : t ∈ D23 K) : a * t = t * a := by
  obtain ⟨u, rfl⟩ := mem_D12_iff.mp ha
  obtain ⟨v, rfl⟩ := mem_D23_iff.mp ht
  exact blockSL_torus_comm u v

@[expose] def conjDiag (v : Kˣ) (A : SL(2, K)) : SL(2, K) :=
  ⟨!![A 0 0, ((v⁻¹ : Kˣ) : K) * A 0 1; (v : K) * A 1 0, A 1 1], by
    have h := A.2
    have hv : ((v⁻¹ : Kˣ) : K) * (v : K) = 1 := by simp
    rw [Matrix.det_fin_two] at h ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination h - A 0 1 * A 1 0 * hv⟩

theorem coe_conjDiag (v : Kˣ) (A : SL(2, K)) :
    ((conjDiag v A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![A 0 0, ((v⁻¹ : Kˣ) : K) * A 0 1; (v : K) * A 1 0, A 1 1] :=
  rfl

theorem blockSL_one_torus_mul_blockSL_zero (v : Kˣ) (A : SL(2, K)) :
    blockSL K 3 2 1 (by omega) (torusHom K v) * blockSL K 3 2 0 (by omega) A =
      blockSL K 3 2 0 (by omega) (conjDiag v A) * blockSL K 3 2 1 (by omega) (torusHom K v) := by
  have hv : (v : K) ≠ 0 := v.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      coe_blockSL_three_zero, coe_blockSL_three_one, coe_torusHom, coe_conjDiag] <;>
    field_simp

theorem blockSL_zero_torus_mul_blockSL_one (s : Kˣ) (A : SL(2, K)) :
    blockSL K 3 2 0 (by omega) (torusHom K s) * blockSL K 3 2 1 (by omega) A =
      blockSL K 3 2 1 (by omega) (conjDiag s A) * blockSL K 3 2 0 (by omega) (torusHom K s) := by
  have hs : (s : K) ≠ 0 := s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      coe_blockSL_three_zero, coe_blockSL_three_one, coe_torusHom, coe_conjDiag] <;>
    field_simp

theorem D23_conj_mem_B12 {c m : SL(3, K)} (hc : c ∈ D23 K) (hm : m ∈ B12 K) :
    c * m * c⁻¹ ∈ B12 K := by
  obtain ⟨v, rfl⟩ := mem_D23_iff.mp hc
  obtain ⟨A, rfl⟩ := hm
  exact ⟨conjDiag v A, eq_mul_inv_iff_mul_eq.mpr (blockSL_one_torus_mul_blockSL_zero v A).symm⟩

theorem D12_conj_mem_B23 {c m : SL(3, K)} (hc : c ∈ D12 K) (hm : m ∈ B23 K) :
    c * m * c⁻¹ ∈ B23 K := by
  obtain ⟨v, rfl⟩ := mem_D12_iff.mp hc
  obtain ⟨A, rfl⟩ := hm
  exact ⟨conjDiag v A, eq_mul_inv_iff_mul_eq.mpr (blockSL_zero_torus_mul_blockSL_one v A).symm⟩

theorem eq_zero_of_eq_mul_self_of_ne_one {a u : K} (hu : u ≠ 1) (h : a = u * a) : a = 0 := by
  by_contra ha
  exact hu (mul_right_cancel₀ ha (by rw [one_mul]; exact h.symm))

theorem mem_diagTorus2_of_commute_one {s : Kˣ} (hs : s ≠ 1) {A : SL(2, K)}
    (h : blockSL K 3 2 1 (by omega) A * blockSL K 3 2 0 (by omega) (torusHom K s) =
      blockSL K 3 2 0 (by omega) (torusHom K s) * blockSL K 3 2 1 (by omega) A) :
    A ∈ diagTorus2 K := by
  have h' := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_three_zero, coe_blockSL_three_one,
    coe_torusHom] at h'
  have h12 := congrFun (congrFun h' 1) 2
  have h21 := congrFun (congrFun h' 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h12 h21
  have hs' : (s : K)⁻¹ ≠ 1 := fun h1 => hs (Units.ext (inv_eq_one.mp h1))
  exact mem_diagTorus2_of_offDiag A (eq_zero_of_eq_mul_self_of_ne_one hs' h12)
    (eq_zero_of_eq_mul_self_of_ne_one hs' (by linear_combination -h21))

theorem mem_diagTorus2_of_commute_zero {s : Kˣ} (hs : s ≠ 1) {A : SL(2, K)}
    (h : blockSL K 3 2 0 (by omega) A * blockSL K 3 2 1 (by omega) (torusHom K s) =
      blockSL K 3 2 1 (by omega) (torusHom K s) * blockSL K 3 2 0 (by omega) A) :
    A ∈ diagTorus2 K := by
  have h' := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_three_zero, coe_blockSL_three_one,
    coe_torusHom] at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h10 := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h01 h10
  have hs' : (s : K) ≠ 1 := fun h1 => hs (Units.ext h1)
  exact mem_diagTorus2_of_offDiag A
    (eq_zero_of_eq_mul_self_of_ne_one hs' (by linear_combination -h01))
    (eq_zero_of_eq_mul_self_of_ne_one hs' h10)

end Torus3

end CFSG.ClassicalInvolution.WeakCT
