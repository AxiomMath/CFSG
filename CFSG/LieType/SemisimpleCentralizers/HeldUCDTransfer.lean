module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix CFSG.LocalAnalysis.ComponentInitial

section Trace

variable {L K : Type} [Field L] [Finite L] [Field K] [Finite K] [Algebra L K]

theorem trace_comp_eq (ρ : K →+* K) (τ : L →+* L)
    (hρL : ∀ l : L, ρ (algebraMap L K l) = algebraMap L K (τ l)) (z : K) :
    Algebra.trace L K (ρ z) = τ (Algebra.trace L K z) := by
  apply (algebraMap L K).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow, ← hρL, FiniteField.algebraMap_trace_eq_sum_pow,
    map_sum]
  simp only [map_pow]

theorem eq_of_trace_mul_eq (u v : K)
    (h : ∀ c : K, Algebra.trace L K (u * c) = Algebra.trace L K (v * c)) : u = v := by
  have h0 : ∀ c : K, Algebra.trace L K ((u - v) * c) = 0 := fun c => by
    rw [sub_mul, map_sub, h c, sub_self]
  have := (traceForm_nondegenerate L K).1 (u - v) (fun c => by
    rw [Algebra.traceForm_apply]
    exact h0 c)
  exact sub_eq_zero.mp this

end Trace

section Transfer

variable {L K W : Type} [Field L] [Finite L] [Field K] [Finite K] [Algebra L K]
  [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower L K W]

theorem exists_trace_form (ρ : K →+* K) (τ : L →+* L) (hρρ : ∀ x, ρ (ρ x) = x)
    (hρL : ∀ l : L, ρ (algebraMap L K l) = algebraMap L K (τ l))
    (h : W →ₛₗ[τ] W →ₗ[L] L) (hherm : ∀ x y, τ (h x y) = h y x)
    (hadj : ∀ (c : K) (x y : W), h (c • x) y = h x (ρ c • y))
    (hnd : ∀ x : W, (∀ y, h x y = 0) → x = 0) :
    ∃ B : W →ₛₗ[ρ] W →ₗ[K] K, (∀ x y, ρ (B x y) = B y x) ∧
      (∀ x : W, (∀ y, B x y = 0) → x = 0) ∧ ∀ x y, h x y = Algebra.trace L K (B x y) := by
  let D : K ≃ₗ[L] Module.Dual L K :=
    (Algebra.traceForm L K).toDual (traceForm_nondegenerate L K)
  have hD : ∀ (u c : K), D u c = Algebra.trace L K (u * c) := fun u c => by
    show (Algebra.traceForm L K).toDual (traceForm_nondegenerate L K) u c = _
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]
  let φ : W → W → Module.Dual L K := fun x y =>
    (h x).comp ((LinearMap.toSpanSingleton K W y).restrictScalars L)
  let B0 : W → W → K := fun x y => D.symm (φ x y)
  have hkey : ∀ x y c, Algebra.trace L K (B0 x y * c) = h x (c • y) := by
    intro x y c
    rw [← hD, show D (B0 x y) = φ x y from D.apply_symm_apply (φ x y)]
    rfl
  have hadd_x : ∀ x x' y, B0 (x + x') y = B0 x y + B0 x' y := by
    intro x x' y
    refine eq_of_trace_mul_eq (L := L) _ _ ?_
    intro c
    simp only [map_add, add_mul, hkey, LinearMap.add_apply]
  have hsmul_x : ∀ (a : K) x y, B0 (a • x) y = ρ a • B0 x y := by
    intro a x y
    refine eq_of_trace_mul_eq (L := L) _ _ ?_
    intro c
    rw [hkey, hadj, smul_smul, ← hkey, smul_eq_mul]
    congr 1
    ring
  have hadd_y : ∀ x y y', B0 x (y + y') = B0 x y + B0 x y' := by
    intro x y y'
    refine eq_of_trace_mul_eq (L := L) _ _ ?_
    intro c
    simp only [map_add, add_mul, hkey, smul_add, LinearMap.map_add]
  have hsmul_y : ∀ (a : K) x y, B0 x (a • y) = a • B0 x y := by
    intro a x y
    refine eq_of_trace_mul_eq (L := L) _ _ ?_
    intro c
    rw [hkey, smul_smul, ← hkey, smul_eq_mul]
    congr 1
    ring
  have hsymm : ∀ x y, ρ (B0 x y) = B0 y x := by
    intro x y
    refine eq_of_trace_mul_eq (L := L) _ _ ?_
    intro c
    rw [hkey, ← hherm (c • x) y, hadj, ← hkey, ← trace_comp_eq ρ τ hρL, map_mul ρ, hρρ]
  have hsep : ∀ x : W, (∀ y, B0 x y = 0) → x = 0 := by
    intro x hx
    refine hnd x (fun y => ?_)
    have := hkey x y 1
    rw [mul_one, hx y, map_zero, one_smul] at this
    exact this.symm
  have hrep : ∀ x y, h x y = Algebra.trace L K (B0 x y) := by
    intro x y
    have := hkey x y 1
    rw [mul_one, one_smul] at this
    exact this.symm
  refine ⟨LinearMap.mk₂'ₛₗ ρ (RingHom.id K) B0 hadd_x hsmul_x hadd_y hsmul_y, fun x y => hsymm x y,
    hsep, hrep⟩

end Transfer


section Unitary

variable {K W : Type} [Field K] [AddCommGroup W] [Module K W]

theorem form_apply_of_orthonormal {ρ : K →+* K} {B : W →ₛₗ[ρ] W →ₗ[K] K} {d : ℕ}
    (e : Module.Basis (Fin d) K W) (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
    (x y : W) : B x y = ∑ a, ρ (e.repr x a) * e.repr y a := by
  have hxy : B x y = B (∑ a, e.repr x a • e a) (∑ b, e.repr y b • e b) := by
    rw [e.sum_repr, e.sum_repr]
  rw [hxy]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, he,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, RingHom.id_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem sum_mulVec_mul_eq {ρ : K →+* K} {d : ℕ} (M : Matrix (Fin d) (Fin d) K) (r s : Fin d → K) :
    ∑ j, ρ (∑ a, M j a * r a) * (∑ b, M j b * s b) =
      ∑ a, ∑ b, (((M.map ρ)ᵀ * M) a b) * (ρ (r a) * s b) := by
  simp only [map_sum, map_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  calc ∑ j, ∑ b, ∑ a, ρ (M j a) * ρ (r a) * (M j b * s b)
      = ∑ j, ∑ a, ∑ b, ρ (M j a) * ρ (r a) * (M j b * s b) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ b, ρ (M j a) * ρ (r a) * (M j b * s b) := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ j, ρ (M j a) * ρ (r a) * (M j b * s b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun j _ => by ring

theorem form_map_apply {ρ : K →+* K} {B : W →ₛₗ[ρ] W →ₗ[K] K} {d : ℕ}
    (e : Module.Basis (Fin d) K W) (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
    (g : W →ₗ[K] W) (x y : W) :
    B (g x) (g y) = ∑ a, ∑ b, ((((LinearMap.toMatrix e e g).map ρ)ᵀ * LinearMap.toMatrix e e g) a b)
      * (ρ (e.repr x a) * e.repr y b) := by
  have hx : ∀ j, e.repr (g x) j = ∑ a, LinearMap.toMatrix e e g j a * e.repr x a := by
    intro j
    rw [← LinearMap.toMatrix_mulVec_repr e e g x]
    rfl
  have hy : ∀ j, e.repr (g y) j = ∑ b, LinearMap.toMatrix e e g j b * e.repr y b := by
    intro j
    rw [← LinearMap.toMatrix_mulVec_repr e e g y]
    rfl
  rw [form_apply_of_orthonormal e he (g x) (g y)]
  simp only [hx, hy]
  exact sum_mulVec_mul_eq _ _ _

theorem unitary_iff_matrix {ρ : K →+* K} {B : W →ₛₗ[ρ] W →ₗ[K] K} {d : ℕ}
    (e : Module.Basis (Fin d) K W) (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
    (g : W →ₗ[K] W) :
    (∀ x y, B (g x) (g y) = B x y) ↔
      ((LinearMap.toMatrix e e g).map ρ)ᵀ * LinearMap.toMatrix e e g = 1 := by
  constructor
  · intro hg
    ext a b
    have h1 := hg (e a) (e b)
    rw [form_map_apply e he, he] at h1
    simp only [Module.Basis.repr_self_apply, apply_ite ρ, map_one, map_zero, ite_mul, one_mul,
      zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    rw [Matrix.one_apply]
    exact h1
  · intro hM x y
    rw [form_map_apply e he, hM, form_apply_of_orthonormal e he]
    simp [Matrix.one_apply]

theorem nonempty_mulEquiv_heldGU {d : ℕ} (ρE : K ≃+* K) (hρ : ∀ x, ρE (ρE x) = x)
    (B : W →ₛₗ[(ρE : K →+* K)] W →ₗ[K] K) (e : Module.Basis (Fin d) K W)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) :
    Nonempty (sesqUnitaryGroup B ≃* Held.heldGU d K ρE hρ) := by
  let Ψ : LinearMap.GeneralLinearGroup K W ≃* GL (Fin d) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv e).toMulEquiv
  have hΨ : ∀ g : LinearMap.GeneralLinearGroup K W,
      ((Ψ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        LinearMap.toMatrix e e (g : W →ₗ[K] W) := fun g => rfl
  have hmem : ∀ g : LinearMap.GeneralLinearGroup K W, g ∈ sesqUnitaryGroup B ↔
      ((LinearMap.toMatrix e e (g : W →ₗ[K] W)).map ρE)ᵀ * LinearMap.toMatrix e e (g : W →ₗ[K] W)
        = 1 := by
    intro g
    rw [mem_sesqUnitaryGroup]
    exact unitary_iff_matrix e he (g : W →ₗ[K] W)
  let f : sesqUnitaryGroup B →* Held.heldGU d K ρE hρ :=
    MonoidHom.codRestrict ((Ψ : LinearMap.GeneralLinearGroup K W →* GL (Fin d) K).comp
      (sesqUnitaryGroup B).subtype) _ (fun g => by
        rw [Held.mem_heldGU]
        exact (hmem (g : LinearMap.GeneralLinearGroup K W)).mp g.2)
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro g₁ g₂ h
    apply Subtype.ext
    apply Ψ.injective
    exact congrArg Subtype.val h
  · intro A
    have hA : Ψ.symm A ∈ sesqUnitaryGroup B := by
      rw [hmem, ← hΨ, MulEquiv.apply_symm_apply]
      exact Held.mem_heldGU.mp A.2
    refine ⟨⟨Ψ.symm A, hA⟩, ?_⟩
    apply Subtype.ext
    exact Ψ.apply_symm_apply A

theorem unitary_trace_iff {L : Type} [Field L] [Finite L] [Algebra L K] [Finite K] {ρ : K →+* K}
    {W : Type} [AddCommGroup W] [Module K W] [Module L W]
    [IsScalarTower L K W] {τ : L →+* L} (h : W →ₛₗ[τ] W →ₗ[L] L)
    (B : W →ₛₗ[ρ] W →ₗ[K] K) (hrep : ∀ x y, h x y = Algebra.trace L K (B x y))
    (g : W →ₗ[K] W) :
    (∀ x y, h (g x) (g y) = h x y) ↔ (∀ x y, B (g x) (g y) = B x y) := by
  have hkey : ∀ u v (c : K), Algebra.trace L K (B u v * c) = h u (c • v) := by
    intro u v c
    rw [hrep, map_smul, smul_eq_mul, mul_comm]
  constructor
  · intro hg x y
    refine eq_of_trace_mul_eq (L := L) _ _ (fun c => ?_)
    rw [hkey, hkey, ← map_smul g c y, hg]
  · intro hB x y
    rw [hrep, hrep, hB]

end Unitary

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
