module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap
open TauCeti

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def aux_planeLin : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) where
  toFun c := fun i => if i = 0 then - c 1 else c 0
  invFun c := fun i => if i = 0 then c 1 else - c 0
  left_inv c := by funext i; fin_cases i <;> simp
  right_inv c := by funext i; fin_cases i <;> simp
  map_add' c d := by funext i; fin_cases i <;> simp [add_comm]
  map_smul' a c := by funext i; fin_cases i <;> simp

@[simp] lemma aux_planeLin_apply (c : Fin 2 → ZMod 3) (i : Fin 2) :
    aux_planeLin c i = if i = 0 then - c 1 else c 0 := rfl

@[expose] noncomputable def aux_pairIso {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {x y : V} {a b : (ZMod 3)ˣ} (hx : Q x = a) (hy : Q y = b)
    (hxy : polar Q x y = 0) :
    (TauCeti.presentedForm ⟨2, ![a, b]⟩).IsometryEquiv
      (Q.restrict (LinearMap.range (Fintype.linearCombination (ZMod 3) ![x, y]))) where
  toLinearEquiv := LinearEquiv.ofInjective _ <| by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at hc
    have h2 : (2 : ZMod 3) ≠ 0 := (isUnit_of_invertible (2 : ZMod 3)).ne_zero
    have hc0 := congrArg (polar Q x) hc
    have hc1 := congrArg (polar Q y) hc
    simp only [polar_add_right, polar_smul_right, polar_self, polar_comm Q y x, hxy, hx, hy,
      polar_zero_right, smul_eq_mul, mul_zero, add_zero, zero_add] at hc0 hc1
    ext i
    fin_cases i
    · simpa [h2, a.ne_zero] using hc0
    · simpa [h2, b.ne_zero] using hc1
  map_app' c := by
    simp only [QuadraticMap.restrict_apply, LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
      LinearEquiv.ofInjective_apply]
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, QuadraticMap.map_add, QuadraticMap.map_smul,
      polar_smul_left, polar_smul_right, hxy, hx, hy, smul_eq_mul]
    rw [presentedForm_apply]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    ring

@[simp] lemma aux_pairIso_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {x y : V} {a b : (ZMod 3)ˣ} (hx : Q x = a) (hy : Q y = b)
    (hxy : polar Q x y = 0) (c : Fin 2 → ZMod 3) :
    (aux_pairIso hx hy hxy c : V) = Fintype.linearCombination (ZMod 3) ![x, y] c := rfl

lemma aux_planeLin_action {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {p : OGroup Q} (hp : p * p = piOrth Q) {v : V}
    {a : (ZMod 3)ˣ} (ha : Q v = a) (c : Fin 2 → ZMod 3) :
    (aux_pairIso ha ((aux_Q_p v).trans ha) (aux_polar hp v) (aux_planeLin c) : V) =
      (p : V ≃ₗ[ZMod 3] V)
        (aux_pairIso ha ((aux_Q_p v).trans ha) (aux_polar hp v) c : V) := by
  rw [aux_pairIso_apply, aux_pairIso_apply]
  simp only [Fintype.linearCombination_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [map_add, map_smul, map_smul, aux_p_apply_apply hp v]
  simp only [aux_planeLin_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, smul_neg]
  module

lemma aux_plane_invariant {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {p : OGroup Q} (hp : p * p = piOrth Q) (v : V) :
    (LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v])).map
        (p : V →ₗ[ZMod 3] V) =
      LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v]) := by
  set W : Submodule (ZMod 3) V :=
    LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v]) with hW
  have hvW : v ∈ W := by
    rw [hW, Fintype.range_linearCombination]
    exact Submodule.subset_span (by simp)
  have hpvW : (p : V ≃ₗ[ZMod 3] V) v ∈ W := by
    rw [hW, Fintype.range_linearCombination]
    exact Submodule.subset_span (by simp)
  have hpmaps : ∀ z ∈ W, (p : V ≃ₗ[ZMod 3] V) z ∈ W := by
    intro z hz
    rw [hW, Fintype.range_linearCombination] at hz
    have hle : Submodule.span (ZMod 3) (Set.range ![v, (p : V ≃ₗ[ZMod 3] V) v]) ≤
        Submodule.comap (p : V ≃ₗ[ZMod 3] V).toLinearMap W := by
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      fin_cases i
      · change (p : V ≃ₗ[ZMod 3] V) v ∈ W
        exact hpvW
      · change (p : V ≃ₗ[ZMod 3] V) ((p : V ≃ₗ[ZMod 3] V) v) ∈ W
        rw [aux_p_apply_apply hp v]
        exact W.neg_mem hvW
    exact hle hz
  change W.map (p : V →ₗ[ZMod 3] V) = W
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact hpmaps
  · intro z hz
    refine Submodule.mem_map.mpr ⟨-((p : V ≃ₗ[ZMod 3] V) z), W.neg_mem (hpmaps z hz), ?_⟩
    change (p : V ≃ₗ[ZMod 3] V) (-((p : V ≃ₗ[ZMod 3] V) z)) = z
    rw [map_neg, aux_p_apply_apply hp z, neg_neg]

lemma aux_complement_invariant {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {p : OGroup Q} (hp : p * p = piOrth Q) (v : V) :
    (LinearMap.BilinForm.orthogonal Q.polarBilin
      (LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v]))).map
        (p : V →ₗ[ZMod 3] V) =
      LinearMap.BilinForm.orthogonal Q.polarBilin
        (LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v])) := by
  set W : Submodule (ZMod 3) V :=
    LinearMap.range (Fintype.linearCombination (ZMod 3) ![v, (p : V ≃ₗ[ZMod 3] V) v]) with hW
  set Wc : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin W with hWc
  have hWmap : W.map (p : V →ₗ[ZMod 3] V) = W := aux_plane_invariant hp v
  have hpmapsc : ∀ z ∈ Wc, (p : V ≃ₗ[ZMod 3] V) z ∈ Wc := by
    intro z hz
    have hz' : z ∈ LinearMap.BilinForm.orthogonal Q.polarBilin W := hz
    rw [hWc, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    obtain ⟨u', hu'W, hu'eq⟩ := Submodule.mem_map.mp (by rw [hWmap]; exact hu)
    rw [← hu'eq, QuadraticMap.polarBilin_apply_apply]
    change polar Q ((p : V ≃ₗ[ZMod 3] V) u') ((p : V ≃ₗ[ZMod 3] V) z) = 0
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup p.2 u' z]
    simpa only [QuadraticMap.polarBilin_apply_apply] using
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hz') u' hu'W
  change Wc.map (p : V →ₗ[ZMod 3] V) = Wc
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact hpmapsc
  · intro z hz
    refine Submodule.mem_map.mpr ⟨-((p : V ≃ₗ[ZMod 3] V) z), Wc.neg_mem (hpmapsc z hz), ?_⟩
    change (p : V ≃ₗ[ZMod 3] V) (-((p : V ≃ₗ[ZMod 3] V) z)) = z
    rw [map_neg, aux_p_apply_apply hp z, neg_neg]

end CFSG.OddStandard.SmallF3.Omega
