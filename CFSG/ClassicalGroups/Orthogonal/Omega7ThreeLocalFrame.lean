module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalDefs
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaOddOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open QuadraticMap CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def modelPolar (K : Type) [Field K] (a : K) (u w : Idx → K) : K :=
  ∑ i : Fin 3, (2 * u (.inl i) * w (.inl i) - u (.inl i) * w (.inr (.inl i)) -
    u (.inr (.inl i)) * w (.inl i) + 2 * u (.inr (.inl i)) * w (.inr (.inl i))) +
    2 * a * u (.inr (.inr ())) * w (.inr (.inr ()))

theorem modelQuad_add (a : K) (u w : Idx → K) :
    modelQuad K a (u + w) = modelQuad K a u + modelQuad K a w + modelPolar K a u w := by
  simp only [modelQuad, modelPolar, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem modelPolar_comm (a : K) (u w : Idx → K) : modelPolar K a u w = modelPolar K a w u := by
  simp only [modelPolar, Fin.sum_univ_three]
  ring

theorem eq_zero_of_forall_modelPolar_eq_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {a : K}
    (ha : a ≠ 0) {u : Idx → K} (h : ∀ w, modelPolar K a u w = 0) : u = 0 := by
  have hx : ∀ i : Fin 3, 2 * u (.inl i) - u (.inr (.inl i)) = 0 := by
    intro i
    have e := h (Pi.single (.inl i) 1)
    fin_cases i <;> simpa [modelPolar, Fin.sum_univ_three, Pi.single_apply] using e
  have hy : ∀ i : Fin 3, - u (.inl i) + 2 * u (.inr (.inl i)) = 0 := by
    intro i
    have e := h (Pi.single (.inr (.inl i)) 1)
    fin_cases i <;> simpa [modelPolar, Fin.sum_univ_three, Pi.single_apply, sub_eq_add_neg] using e
  have hz : 2 * a * u (.inr (.inr ())) = 0 := by
    have e := h (Pi.single (.inr (.inr ())) 1)
    simpa [modelPolar, Fin.sum_univ_three, Pi.single_apply] using e
  funext j
  rcases j with i | i | z
  · have h3' : 3 * u (.inl i) = 0 := by linear_combination 2 * hx i + hy i
    simpa [h3] using h3'
  · have h3' : 3 * u (.inr (.inl i)) = 0 := by linear_combination hx i + 2 * hy i
    simpa [h3] using h3'
  · have : u (.inr (.inr ())) = 0 := by
      have := mul_eq_zero.mp hz
      simpa [h2, ha] using this
    simpa using this

theorem exists_planeNorm_eq [Finite K] (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0) (c : K) :
    ∃ s t : K, s ^ 2 - s * t + t ^ 2 = c := by
  have := Fintype.ofFinite K
  open Polynomial in
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 - C c : K[X])) (g := (C 3 * X ^ 2 : K[X]))
    (degree_X_pow_sub_C (by norm_num) c) (by exact degree_C_mul_X_pow 2 h3)
    (FiniteField.odd_card_of_char_ne_two hK)
  refine ⟨x + y, 2 * y, ?_⟩
  simp at hxy
  linear_combination hxy

@[expose] noncomputable def Frame.lin (F : Frame K) : (Idx → K) ≃ₗ[K] (Idx → K) :=
  toLinEquiv Idx K F.P

theorem Frame.lin_apply (F : Frame K) (w : Idx → K) :
    F.lin w = (F.P : Matrix Idx Idx K) *ᵥ w := rfl

theorem Frame.quadOdd_lin (F : Frame K) (w : Idx → K) :
    quadOdd 3 K (F.lin w) = modelQuad K F.a w := by
  rw [F.lin_apply]
  exact (congrFun (coe_quadOdd 3 K) _).trans (F.isometry w)

theorem Frame.polar_lin (F : Frame K) (u w : Idx → K) :
    polar (quadOdd 3 K) (F.lin u) (F.lin w) = modelPolar K F.a u w := by
  rw [polar, ← map_add, F.quadOdd_lin, F.quadOdd_lin, F.quadOdd_lin, modelQuad_add]
  ring

@[expose] def modelRefl (K : Type) [Field K] (a : K) (u x : Idx → K) : Idx → K :=
  x - (modelPolar K a u x / modelQuad K a u) • u

theorem Frame.reflect_lin (F : Frame K) {u : Idx → K} (hu : modelQuad K F.a u ≠ 0)
    (y : Idx → K) :
    reflect (quadOdd 3 K) (F.lin u) (F.lin y) = F.lin (modelRefl K F.a u y) := by
  rw [reflect_apply (by rwa [F.quadOdd_lin]), F.polar_lin, F.quadOdd_lin, modelRefl, map_sub,
    map_smul]

theorem exists_mem_orthogonalGroup_apply_eq_of_map_eq {V : Type*} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {u w : V}
    (hQ : Q u = Q w) (hu : Q u ≠ 0) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g u = w := by
  have hQd : Q (u - w) = 2 * Q u - polar Q u w := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, ← hQ]
    ring
  have hQs : Q (u + w) = 2 * Q u + polar Q u w := by
    rw [QuadraticMap.map_add Q, ← hQ]
    ring
  by_cases hd : Q (u - w) = 0
  · have hpol : polar Q u w = 2 * Q u := by
      rw [hd] at hQd
      linear_combination hQd
    have hs : Q (u + w) ≠ 0 := by
      rw [hQs, hpol]
      have : 2 * Q u + 2 * Q u = 2 * (2 * Q u) := by ring
      rw [this]
      exact mul_ne_zero h2 (mul_ne_zero h2 hu)
    refine ⟨reflect Q w * reflect Q (u + w),
      Subgroup.mul_mem _ (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _), ?_⟩
    have hw : Q w ≠ 0 := hQ ▸ hu
    have h1 : reflect Q (u + w) u = -w := by
      rw [reflect_apply hs]
      have : polar Q (u + w) u = Q (u + w) := by
        rw [polar_add_left, polar_self_eq_two_mul, polar_comm Q w u, hQs]
      rw [this, div_self hs, one_smul]
      abel
    rw [LinearEquiv.mul_apply, h1, map_neg, reflect_apply hw, polar_self_eq_two_mul,
      mul_div_assoc, div_self hw, mul_one]
    module
  · refine ⟨reflect Q (u - w), reflect_mem_orthogonalGroup Q _, ?_⟩
    rw [reflect_apply hd]
    have : polar Q (u - w) u = Q (u - w) := by
      rw [polar_sub_left, polar_self_eq_two_mul, polar_comm Q w u, hQd]
    rw [this, div_self hd, one_smul]
    abel

theorem reflect_mul_reflect_mem_commutator_of_map_eq {V : Type*} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) {u w : V}
    (hQ : Q u = Q w) (hu : Q u ≠ 0) :
    reflect Q u * reflect Q w ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨g, hg, hgu⟩ := exists_mem_orthogonalGroup_apply_eq_of_map_eq h2 hQ hu
  have h4 : ⁅reflect Q u, g⁆ = reflect Q u * reflect Q w := by
    rw [commutatorElement_def, reflect_inv, mul_assoc, mul_assoc, ← mul_assoc g, reflect_conj hg,
      hgu]
  rw [← h4]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q _) hg

theorem Frame.mem_Omega7_conj_of_odd [Finite K] (F : Frame K) {m : GL Idx K}
    (hm : ∀ w, modelQuad K F.a ((m : Matrix Idx Idx K) *ᵥ w) = modelQuad K F.a w)
    (hodd : Odd (orderOf m)) : F.P * m * F.P⁻¹ ∈ Omega7 K := by
  have hPP : (F.P : Matrix Idx Idx K) * ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine mem_statedOmega_quadOdd_of_odd F.hK _ (fun w => ?_) ?_
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.isometry,
      hm, ← F.isometry, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  · have h := orderOf_injective (MulAut.conj F.P).toMonoidHom (MulAut.conj F.P).injective m
    rw [← h] at hodd
    exact hodd

theorem Frame.mem_Omega7_conj_of_reflect_pair [Finite K] (F : Frame K) {m : GL Idx K}
    {u w : Idx → K} (hQ : modelQuad K F.a u = modelQuad K F.a w)
    (hu : modelQuad K F.a u ≠ 0)
    (hm : ∀ x, (m : Matrix Idx Idx K) *ᵥ x = modelRefl K F.a u (modelRefl K F.a w x)) :
    F.P * m * F.P⁻¹ ∈ Omega7 K := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero F.hK
  have hw : modelQuad K F.a w ≠ 0 := hQ ▸ hu
  have hQ' : quadOdd 3 K (F.lin u) = quadOdd 3 K (F.lin w) := by
    rw [F.quadOdd_lin, F.quadOdd_lin, hQ]
  have hu' : quadOdd 3 K (F.lin u) ≠ 0 := by rwa [F.quadOdd_lin]
  have hmem := reflect_mul_reflect_mem_commutator_of_map_eq h2 hQ' hu'
  have hPP : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) * (F.P : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : toLinEquiv Idx K (F.P * m * F.P⁻¹) =
      reflect (quadOdd 3 K) (F.lin u) * reflect (quadOdd 3 K) (F.lin w) := by
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ : ∃ y, F.lin y = x := ⟨F.lin.symm x, F.lin.apply_symm_apply x⟩
    have h1 : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ ((F.P : Matrix Idx Idx K) *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    rw [LinearEquiv.mul_apply, F.reflect_lin hw, F.reflect_lin hu, ← hm, toLinEquiv_apply,
      F.lin_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h1]
    rfl
  show F.P * m * F.P⁻¹ ∈ StatedOmega (StatedQuadOdd 3 K)
  rw [statedOmega_eq_comap (coe_quadOdd 3 K), Subgroup.mem_comap]
  show toLinEquiv Idx K (F.P * m * F.P⁻¹) ∈ _
  rw [key]
  exact hmem

@[expose] noncomputable def Frame.reflGL (F : Frame K) (u : Idx → K) : GL Idx K :=
  F.P⁻¹ * (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) * F.P

theorem Frame.reflGL_mulVec (F : Frame K) {u : Idx → K} (hu : modelQuad K F.a u ≠ 0)
    (x : Idx → K) :
    ((F.reflGL u : GL Idx K) : Matrix Idx Idx K) *ᵥ x = modelRefl K F.a u x := by
  have hPP : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) * (F.P : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ ((F.P : Matrix Idx Idx K) *ᵥ
      (modelRefl K F.a u x)) = modelRefl K F.a u x := by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have h2 : (((toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) : GL Idx K) :
      Matrix Idx Idx K) *ᵥ (F.lin x) = reflect (quadOdd 3 K) (F.lin u) (F.lin x) := by
    rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
  rw [reflGL, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← F.lin_apply, h2, F.reflect_lin hu, F.lin_apply, h1]

theorem Frame.mem_Omega7_conj_reflGL_mul [Finite K] (F : Frame K) {u w : Idx → K}
    (hQ : modelQuad K F.a u = modelQuad K F.a w) (hu : modelQuad K F.a u ≠ 0) :
    F.P * (F.reflGL u * F.reflGL w) * F.P⁻¹ ∈ Omega7 K := by
  have hw : modelQuad K F.a w ≠ 0 := hQ ▸ hu
  refine F.mem_Omega7_conj_of_reflect_pair hQ hu fun x => ?_
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, F.reflGL_mulVec hw, F.reflGL_mulVec hu]

theorem Frame.reflGL_mul_self (F : Frame K) (u : Idx → K) : F.reflGL u * F.reflGL u = 1 := by
  have h : (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) *
      (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) = 1 := by
    rw [← map_mul, reflect_mul_self, map_one]
  unfold reflGL
  calc F.P⁻¹ * (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) * F.P *
        (F.P⁻¹ * (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) * F.P)
      = F.P⁻¹ * ((toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) *
        (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u))) * F.P := by group
    _ = 1 := by rw [h]; group

theorem Frame.modelQuad_modelRefl (F : Frame K) {x : Idx → K} (hx : modelQuad K F.a x ≠ 0)
    (u : Idx → K) : modelQuad K F.a (modelRefl K F.a x u) = modelQuad K F.a u := by
  have hmem := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (reflect_mem_orthogonalGroup (quadOdd 3 K) (F.lin x)) (F.lin u)
  rw [F.reflect_lin hx, F.quadOdd_lin, F.quadOdd_lin] at hmem
  exact hmem

theorem Frame.reflGL_conj_reflGL (F : Frame K) {x : Idx → K} (hx : modelQuad K F.a x ≠ 0)
    (u : Idx → K) :
    F.reflGL x * F.reflGL u * F.reflGL x = F.reflGL (modelRefl K F.a x u) := by
  have hg := reflect_mem_orthogonalGroup (quadOdd 3 K) (F.lin x)
  have hconj := reflect_conj hg (F.lin u)
  rw [reflect_inv, F.reflect_lin hx] at hconj
  have h : (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin (modelRefl K F.a x u))) =
      (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin x)) *
        (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin u)) *
        (toLinEquiv Idx K).symm (reflect (quadOdd 3 K) (F.lin x)) := by
    rw [← map_mul, ← map_mul, ← hconj]
  unfold reflGL
  rw [h]
  group

theorem Frame.mem_Omega7_conj_reflGL_four [Finite K] (F : Frame K) {a b x y : Idx → K}
    (hax : modelQuad K F.a a = modelQuad K F.a x) (ha : modelQuad K F.a a ≠ 0)
    (hby : modelQuad K F.a b = modelQuad K F.a y) (hb : modelQuad K F.a b ≠ 0) :
    F.P * (F.reflGL a * F.reflGL b * F.reflGL x * F.reflGL y) * F.P⁻¹ ∈ Omega7 K := by
  have hx : modelQuad K F.a x ≠ 0 := hax ▸ ha
  have h1 := F.mem_Omega7_conj_reflGL_mul hax ha
  have h2 := F.mem_Omega7_conj_reflGL_mul
    (u := modelRefl K F.a x b) (w := y)
    ((F.modelQuad_modelRefl hx b).trans hby) (by rwa [F.modelQuad_modelRefl hx b])
  have key : F.reflGL a * F.reflGL b * F.reflGL x * F.reflGL y =
      (F.reflGL a * F.reflGL x) * (F.reflGL (modelRefl K F.a x b) * F.reflGL y) := by
    rw [← F.reflGL_conj_reflGL hx b]
    calc F.reflGL a * F.reflGL b * F.reflGL x * F.reflGL y
        = F.reflGL a * (F.reflGL x * F.reflGL x) * F.reflGL b * F.reflGL x * F.reflGL y := by
          rw [F.reflGL_mul_self, mul_one]
      _ = _ := by group
  rw [key]
  have := Subgroup.mul_mem _ h1 h2
  convert this using 1
  group

theorem conj_rotGL_eq_of_mul_eq {m : GL Idx K} {v v' : F3Cube}
    (h : (m : Matrix Idx Idx K) * rotMat K (Multiplicative.toAdd v) =
      rotMat K (Multiplicative.toAdd v') * m) :
    m * rotGL K v * m⁻¹ = rotGL K v' := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simpa [rotGL, rotHom, Units.val_mul] using h

@[expose] def Realized [Finite K] (F : Frame K) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) :
    Prop :=
  ∃ n : ↥(Omega7 K), ∀ v : F3Cube, n * c₀ F v * n⁻¹ =
    c₀ F (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i))

theorem Realized.one [Finite K] (F : Frame K) : Realized F 1 (fun _ => 1) := by
  refine ⟨1, fun v => ?_⟩
  rw [one_mul, inv_one, mul_one]
  congr 1
  apply Multiplicative.toAdd.injective
  funext i
  simp

theorem Realized.mul [Finite K] {F : Frame K} {σ₁ σ₂ : Equiv.Perm (Fin 3)}
    {ε₁ ε₂ : Fin 3 → ZMod 3} (h₁ : Realized F σ₁ ε₁) (h₂ : Realized F σ₂ ε₂) :
    Realized F (σ₂ * σ₁) (fun i => ε₁ i * ε₂ (σ₁ i)) := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  refine ⟨n₁ * n₂, fun v => ?_⟩
  have : n₁ * n₂ * c₀ F v * (n₁ * n₂)⁻¹ = n₁ * (n₂ * c₀ F v * n₂⁻¹) * n₁⁻¹ := by group
  rw [this, hn₂, hn₁]
  congr 1
  apply Multiplicative.toAdd.injective
  funext i
  simp [mul_assoc]

theorem Frame.realized_of_model [Finite K] (F : Frame K) (σ : Equiv.Perm (Fin 3))
    (ε : Fin 3 → ZMod 3) {m : GL Idx K} (hmem : F.P * m * F.P⁻¹ ∈ Omega7 K)
    (hconj : ∀ v : F3Cube, m * rotGL K v * m⁻¹ =
      rotGL K (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i))) :
    Realized F σ ε := by
  refine ⟨⟨F.P * m * F.P⁻¹, hmem⟩, fun v => ?_⟩
  apply Subtype.ext
  show F.P * m * F.P⁻¹ * c₀GL F v * (F.P * m * F.P⁻¹)⁻¹ = c₀GL F _
  simp only [c₀GL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← hconj v]
  group

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
