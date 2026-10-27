module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Determinant

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem det_eq_prod_of_basis_apply_eq_smul {ι : Type*} [Fintype ι]
    (B : Basis ι K V) (f : V →ₗ[K] V) (c : ι → K) (hf : ∀ i, f (B i) = c i • B i) :
    LinearMap.det f = ∏ i, c i := by
  classical
  have hm : LinearMap.toMatrix B B f = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hf j, map_smul, B.repr_self, Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_diagonal]

theorem LinearEquiv.det_eq_one_of_mem_normalizer_of_centralizer
    [Finite K] [FiniteDimensional K V] {A : Subgroup (V ≃ₗ[K] V)} {b : V ≃ₗ[K] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)))
    (hC : A ⊓ Subgroup.centralizer {b} = ⊥)
    {a : V ≃ₗ[K] V} (ha : a ∈ A) : LinearEquiv.det a = 1 := by
  have hC' : ∀ x ∈ A, x * b = b * x → x = 1 := by
    intro x hx hxb
    have : x ∈ A ⊓ Subgroup.centralizer {b} :=
      ⟨hx, Subgroup.mem_centralizer_iff.mpr (by simp [hxb.symm])⟩
    simpa [hC] using this
  have hbA : ∀ x ∈ A, b * x * b⁻¹ ∈ A := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hb x).mp hx
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective _ _root_.LinearEquiv.coe_injective
  set d : A → A := fun x => ⟨(x : V ≃ₗ[K] V)⁻¹ * (b * x * b⁻¹),
    mul_mem (inv_mem x.2) (hbA x x.2)⟩ with hd
  have hinj : Function.Injective d := by
    intro x y hxy
    have h : (x : V ≃ₗ[K] V)⁻¹ * (b * (x : V ≃ₗ[K] V) * b⁻¹)
        = (y : V ≃ₗ[K] V)⁻¹ * (b * (y : V ≃ₗ[K] V) * b⁻¹) := congrArg Subtype.val hxy
    have h1 : (x : V ≃ₗ[K] V)⁻¹ * b * (x : V ≃ₗ[K] V)
        = (y : V ≃ₗ[K] V)⁻¹ * b * (y : V ≃ₗ[K] V) := by
      apply mul_right_cancel (b := b⁻¹)
      simpa [mul_assoc] using h
    have h3 : ((y : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V)⁻¹) * b
        = b * ((y : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V)⁻¹) := by
      calc ((y : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V)⁻¹) * b
          = ((y : V ≃ₗ[K] V) * ((x : V ≃ₗ[K] V)⁻¹ * b * (x : V ≃ₗ[K] V)))
              * (x : V ≃ₗ[K] V)⁻¹ := by group
        _ = ((y : V ≃ₗ[K] V) * ((y : V ≃ₗ[K] V)⁻¹ * b * (y : V ≃ₗ[K] V)))
              * (x : V ≃ₗ[K] V)⁻¹ := by rw [h1]
        _ = b * ((y : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V)⁻¹) := by group
    exact (Subtype.ext (mul_inv_eq_one.mp (hC' _ (mul_mem y.2 (inv_mem x.2)) h3))).symm
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨a, ha⟩
  have hax : a = (x : V ≃ₗ[K] V)⁻¹ * (b * (x : V ≃ₗ[K] V) * b⁻¹) :=
    (congrArg Subtype.val hx).symm
  have key : ∀ u w : Kˣ, u⁻¹ * (w * u * w⁻¹) = 1 := by
    intro u w
    rw [mul_comm w u, mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel]
  rw [hax]
  simp only [map_mul, map_inv]
  exact key _ _

theorem prod_lineScalars_eq_one [Finite K] {q : ℕ} (_hq : 2 ≤ q)
    {L : Fin q → Submodule K V} (hL : DirectSum.IsInternal L)
    (hdim : ∀ i, finrank K (L i) = 1)
    {A : Subgroup (V ≃ₗ[K] V)}
    (_hA : ∀ a ∈ A, ∀ i, (L i).map (a : V →ₗ[K] V) ≤ L i)
    {b : V ≃ₗ[K] V} (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)))
    {σ : Equiv.Perm (Fin q)}
    (_hσ : ∀ i, (L i).map (b : V →ₗ[K] V) = L (σ i))
    (_hσtrans : ∀ i j, ∃ n : ℕ, (σ ^ n) i = j)
    (hC : A ⊓ Subgroup.centralizer {b} = ⊥)
    {v : Fin q → V} (hv : ∀ i, v i ∈ L i) (hv0 : ∀ i, v i ≠ 0)
    {a : V ≃ₗ[K] V} (ha : a ∈ A) {lam : Fin q → K} (hlam : ∀ i, a (v i) = lam i • v i) :
    ∏ i, lam i = 1 := by
  have hli : LinearIndependent K v :=
    iSupIndep.linearIndependent L hL.submodule_iSupIndep hv hv0
  have hsp : ⊤ ≤ span K (Set.range v) := by
    rw [Submodule.span_range_eq_iSup]
    have hspan : ∀ i, K ∙ v i = L i := fun i =>
      (eq_span_singleton_of_mem_of_finrank_eq_one (hdim i) (hv i) (hv0 i)).symm
    simp only [hspan]
    exact le_of_eq hL.submodule_iSup_eq_top.symm
  let B : Basis (Fin q) K V := Basis.mk hli hsp
  have : FiniteDimensional K V := B.finiteDimensional_of_finite
  have hdet : LinearMap.det (a : V →ₗ[K] V) = ∏ i, lam i :=
    det_eq_prod_of_basis_apply_eq_smul B _ lam (by simpa [B] using hlam)
  have h1 := LinearEquiv.det_eq_one_of_mem_normalizer_of_centralizer hb hC ha
  rw [← hdet, ← _root_.LinearEquiv.coe_det, h1, Units.val_one]

theorem prod_lineScalars_eq_one_zmod (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {q : ℕ} (hq : 2 ≤ q)
    {L : Fin q → Submodule (ZMod p) V} (hL : DirectSum.IsInternal L)
    (hdim : ∀ i, finrank (ZMod p) (L i) = 1)
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : ∀ a ∈ A, ∀ i, (L i).map (a : V →ₗ[ZMod p] V) ≤ L i)
    {b : V ≃ₗ[ZMod p] V} (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    {σ : Equiv.Perm (Fin q)}
    (hσ : ∀ i, (L i).map (b : V →ₗ[ZMod p] V) = L (σ i))
    (hσtrans : ∀ i j, ∃ n : ℕ, (σ ^ n) i = j)
    (hC : A ⊓ Subgroup.centralizer {b} = ⊥)
    {v : Fin q → V} (hv : ∀ i, v i ∈ L i) (hv0 : ∀ i, v i ≠ 0)
    {a : V ≃ₗ[ZMod p] V} (ha : a ∈ A) {lam : Fin q → ZMod p}
    (hlam : ∀ i, a (v i) = lam i • v i) :
    ∏ i, lam i = 1 :=
  prod_lineScalars_eq_one hq hL hdim hA hb hσ hσtrans hC hv hv0 ha hlam

end CFSG.FeitThompson
