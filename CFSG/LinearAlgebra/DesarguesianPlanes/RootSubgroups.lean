module

public import CFSG.LinearAlgebra.DesarguesianPlanes.RootSystemData

public section

namespace CFSG.DesarguesianPlanes

open Matrix
open scoped commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

theorem diag_conj_rootUp (a b : Fˣ) (c : F) :
    conjHom (linearCentralizerHom φ (diagGL a b)) (rootUp φ c) =
      rootUp φ ((a : F) * c * ((b⁻¹ : Fˣ) : F)) := by
  rw [conjHom_apply, rootUp, rootUp, ← map_mul, ← map_inv, ← map_mul, diagGL_mul_upperGL,
    mul_inv_cancel_right]

theorem diag_conj_rootLow (a b : Fˣ) (c : F) :
    conjHom (linearCentralizerHom φ (diagGL a b)) (rootLow φ c) =
      rootLow φ ((b : F) * c * ((a⁻¹ : Fˣ) : F)) := by
  rw [conjHom_apply, rootLow, rootLow, ← map_mul, ← map_inv, ← map_mul, diagGL_mul_lowerGL,
    mul_inv_cancel_right]

theorem diag_map_rootX₁ (a b : Fˣ) :
    (rootX₁ φ).map (conjHom (linearCentralizerHom φ (diagGL a b))) = rootX₁ φ := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp hy
    rw [diag_conj_rootUp]
    exact (mem_rootX₁ φ).mpr ⟨_, rfl⟩
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp hx
    refine ⟨rootUp φ (((a⁻¹ : Fˣ) : F) * c * (b : F)), (mem_rootX₁ φ).mpr ⟨_, rfl⟩, ?_⟩
    rw [diag_conj_rootUp]
    congr 1
    simp only [Units.val_inv_eq_inv_val]
    field_simp

theorem diag_map_rootX₂ (a b : Fˣ) :
    (rootX₂ φ).map (conjHom (linearCentralizerHom φ (diagGL a b))) = rootX₂ φ := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootX₂ φ).mp hy
    rw [diag_conj_rootLow]
    exact (mem_rootX₂ φ).mpr ⟨_, rfl⟩
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_rootX₂ φ).mp hx
    refine ⟨rootLow φ (((b⁻¹ : Fˣ) : F) * c * (a : F)), (mem_rootX₂ φ).mpr ⟨_, rfl⟩, ?_⟩
    rw [diag_conj_rootLow]
    congr 1
    simp only [Units.val_inv_eq_inv_val]
    field_simp

theorem swapW_conj_rootUp (c : F) : conjHom (swapW φ) (rootUp φ c) = rootLow φ c := by
  rw [conjHom_apply, swapW, rootUp, rootLow, ← map_mul, ← map_inv, ← map_mul, swapGL_mul_upperGL,
    mul_inv_cancel_right]

theorem swapW_map_rootX₁ : (rootX₁ φ).map (conjHom (swapW φ)) = rootX₂ φ := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp hy
    rw [swapW_conj_rootUp]
    exact (mem_rootX₂ φ).mpr ⟨_, rfl⟩
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_rootX₂ φ).mp hx
    exact ⟨rootUp φ c, (mem_rootX₁ φ).mpr ⟨_, rfl⟩, swapW_conj_rootUp φ c⟩

theorem map_conjHom_one (H : Subgroup G) : H.map (conjHom (1 : G)) = H := by
  ext x
  simp

theorem swapW_map_rootX₂ : (rootX₂ φ).map (conjHom (swapW φ)) = rootX₁ φ := by
  rw [← swapW_map_rootX₁, map_conjHom_map, swapW_mul_self, map_conjHom_one]

section Torus

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include hZ hZodd h2 in
theorem torus_map_rootX₁ {t : G} (ht : IsTorus φ t) : (rootX₁ φ).map (conjHom t) = rootX₁ φ := by
  obtain ⟨a, b, rfl⟩ := (isTorus_iff φ hZ hZodd h2 t).mp ht
  exact diag_map_rootX₁ φ a b

include hZ hZodd h2 in
theorem torus_map_rootX₂ {t : G} (ht : IsTorus φ t) : (rootX₂ φ).map (conjHom t) = rootX₂ φ := by
  obtain ⟨a, b, rfl⟩ := (isTorus_iff φ hZ hZodd h2 t).mp ht
  exact diag_map_rootX₂ φ a b

theorem map_conjHom_conj (H : Subgroup G) (g t : G)
    (h : H.map (conjHom (g⁻¹ * t * g)) = H) :
    (H.map (conjHom g)).map (conjHom t) = H.map (conjHom g) := by
  rw [map_conjHom_map, show t * g = g * (g⁻¹ * t * g) by group, ← map_conjHom_map, h]

variable {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem torus_map_rootSub {t : G} (ht : IsTorus φ t) (i j : Fin 3) :
    (rootSub φ Y i j).map (conjHom t) = rootSub φ Y i j := by
  have hYt : IsTorus φ (Y * t * Y⁻¹) := ht.conj_Y φ hZ hZodd h2 hJ hY₁ hY₂
  have hY2t : IsTorus φ (Y ^ 2 * t * (Y ^ 2)⁻¹) := by
    have := hYt.conj_Y φ hZ hZodd h2 hJ hY₁ hY₂
    rw [show Y * (Y * t * Y⁻¹) * Y⁻¹ = Y ^ 2 * t * (Y ^ 2)⁻¹ by
      simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc]] at this
    exact this
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    rootSub_01, rootSub_10, rootSub_12, rootSub_21, rootSub_20, rootSub_02]
  · simp [rootSub, Subgroup.map_bot]
  · exact torus_map_rootX₁ φ hZ hZodd h2 ht
  · apply map_conjHom_conj
    rw [inv_inv]
    exact torus_map_rootX₂ φ hZ hZodd h2 hY2t
  · exact torus_map_rootX₂ φ hZ hZodd h2 ht
  · simp [rootSub, Subgroup.map_bot]
  · apply map_conjHom_conj
    rw [inv_inv]
    exact torus_map_rootX₁ φ hZ hZodd h2 hYt
  · apply map_conjHom_conj
    rw [inv_inv]
    exact torus_map_rootX₁ φ hZ hZodd h2 hY2t
  · apply map_conjHom_conj
    rw [inv_inv]
    exact torus_map_rootX₂ φ hZ hZodd h2 hYt
  · simp [rootSub, Subgroup.map_bot]


include hZ hZodd h2 hJ hY₁ hY₂ in
theorem rootSub_map_inv_Y (i j : Fin 3) :
    (rootSub φ Y i j).map (conjHom Y⁻¹) = rootSub φ Y (i + 1) (j + 1) := by
  have hcube : IsTorus φ (Y⁻¹ * (Y ^ 2)⁻¹) := by
    have := (isTorus_Y_cube φ hZ hZodd h2 hJ hY₁ hY₂).inv
    rw [show (Y ^ 3)⁻¹ = Y⁻¹ * (Y ^ 2)⁻¹ by
      simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc]] at this
    exact this
  have hsq : Y⁻¹ * Y⁻¹ = (Y ^ 2)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.reduceAdd, rootSub_01, rootSub_10, rootSub_12, rootSub_21, rootSub_20, rootSub_02]
  · simp [rootSub, Subgroup.map_bot]
  · rw [map_conjHom_map, torus_map_rootX₂ φ hZ hZodd h2 hcube]
  · simp [rootSub, Subgroup.map_bot]
  · rw [map_conjHom_map, hsq]
  · rw [map_conjHom_map, torus_map_rootX₁ φ hZ hZodd h2 hcube]
  · rw [map_conjHom_map, hsq]
  · simp [rootSub, Subgroup.map_bot]


@[expose] def swap01 : Fin 3 → Fin 3 := ![1, 0, 2]

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem rootSub_map_W (i j : Fin 3) :
    (rootSub φ Y i j).map (conjHom (swapW φ)) = rootSub φ Y (swap01 i) (swap01 j) := by
  set c := Y ^ 2 * swapW φ * Y⁻¹ * (swapW φ)⁻¹ with hc
  have hct : IsTorus φ c := isTorus_Y_sq_W φ hZ hZodd h2 hJ hY₁ hY₂
  have hWY : swapW φ * Y⁻¹ = (Y ^ 2)⁻¹ * (c * swapW φ) := by
    rw [hc]
    group
  have h12 : (rootSub φ Y 1 2).map (conjHom (swapW φ)) = rootSub φ Y 0 2 := by
    rw [rootSub_12, rootSub_02, map_conjHom_map, hWY, ← map_conjHom_map, ← map_conjHom_map,
      swapW_map_rootX₁, torus_map_rootX₂ φ hZ hZodd h2 hct]
  have h21 : (rootSub φ Y 2 1).map (conjHom (swapW φ)) = rootSub φ Y 2 0 := by
    rw [rootSub_21, rootSub_20, map_conjHom_map, hWY, ← map_conjHom_map, ← map_conjHom_map,
      swapW_map_rootX₂, torus_map_rootX₁ φ hZ hZodd h2 hct]
  have hWW : ∀ H : Subgroup G, (H.map (conjHom (swapW φ))).map (conjHom (swapW φ)) = H := by
    intro H
    rw [map_conjHom_map, swapW_mul_self, map_conjHom_one]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, swap01,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · simp [rootSub, Subgroup.map_bot]
  · exact swapW_map_rootX₁ φ
  · rw [← h12, hWW]
  · exact swapW_map_rootX₂ φ
  · simp [rootSub, Subgroup.map_bot]
  · exact h12
  · rw [← h21, hWW]
  · exact h21
  · simp [rootSub, Subgroup.map_bot]

@[expose] def TorusTransitive (H : Subgroup G) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, a ≠ 1 → b ≠ 1 → ∃ t, IsTorus φ t ∧ conjHom t a = b

theorem TorusTransitive.map {H : Subgroup G} (hH : TorusTransitive φ H) (g : G)
    (hg : ∀ t, IsTorus φ t → IsTorus φ (g * t * g⁻¹)) :
    TorusTransitive φ (H.map (conjHom g)) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ha1 hb1
  have ha1' : a ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hb1' : b ≠ 1 := fun h => hb1 (by rw [h, map_one])
  obtain ⟨t, ht, htab⟩ := hH a ha b hb ha1' hb1'
  refine ⟨g * t * g⁻¹, hg t ht, ?_⟩
  rw [← htab]
  simp only [conjHom_apply]
  group

theorem torusTransitive_rootX₁ : TorusTransitive φ (rootX₁ φ) := by
  intro a ha b hb ha1 hb1
  obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp ha
  obtain ⟨d, rfl⟩ := (mem_rootX₁ φ).mp hb
  have hc : c ≠ 0 := fun h => ha1 (by rw [h, rootUp, upperGL_zero, map_one])
  have hd : d ≠ 0 := fun h => hb1 (by rw [h, rootUp, upperGL_zero, map_one])
  refine ⟨linearCentralizerHom φ (diagGL (Units.mk0 (d / c) (div_ne_zero hd hc)) 1),
    isTorus_diag φ _ _, ?_⟩
  rw [diag_conj_rootUp]
  congr 1
  simp only [Units.val_mk0, inv_one, Units.val_one, mul_one]
  field_simp

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem rootSub_transitive {i j : Fin 3} (hij : i ≠ j) : TorusTransitive φ (rootSub φ Y i j) := by
  have hYinv : ∀ t, IsTorus φ t → IsTorus φ (Y⁻¹ * t * Y⁻¹⁻¹) := fun t ht => by
    rw [inv_inv]; exact ht.conj_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂
  have hY2inv : ∀ t, IsTorus φ t → IsTorus φ ((Y ^ 2)⁻¹ * t * (Y ^ 2)⁻¹⁻¹) := fun t ht => by
    rw [inv_inv]
    have := (ht.conj_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂).conj_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂
    rw [show Y⁻¹ * (Y⁻¹ * t * Y) * Y = (Y ^ 2)⁻¹ * t * Y ^ 2 by
      simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc]] at this
    exact this
  have hW : ∀ t, IsTorus φ t → IsTorus φ (swapW φ * t * (swapW φ)⁻¹) := fun t ht =>
    ht.conj_W φ hZ hZodd h2 hJ
  have h2' : TorusTransitive φ (rootX₂ φ) := by
    rw [← swapW_map_rootX₁]
    exact (torusTransitive_rootX₁ φ).map φ _ hW
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    rootSub_01, rootSub_10, rootSub_12, rootSub_21, rootSub_20, rootSub_02] at hij ⊢
  · exact absurd rfl hij
  · exact torusTransitive_rootX₁ φ
  · exact h2'.map φ _ hY2inv
  · exact h2'
  · exact absurd rfl hij
  · exact (torusTransitive_rootX₁ φ).map φ _ hYinv
  · exact (torusTransitive_rootX₁ φ).map φ _ hY2inv
  · exact h2'.map φ _ hYinv
  · exact absurd rfl hij

end Torus

end CFSG.DesarguesianPlanes
