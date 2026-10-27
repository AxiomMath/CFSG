module

public import CFSG.LargeExtraspecial.GLW4Mat
public import CFSG.LargeExtraspecial.GLRFormBeta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

@[expose] noncomputable def matX (e : Basis (Fin 4) (ZMod 2) C.At) (x : C.Xbar) : Mat :=
  LinearMap.toMatrix e e (C.resAt x : C.At →ₗ[ZMod 2] C.At)

variable {C}

theorem matX_mul (e : Basis (Fin 4) (ZMod 2) C.At) (x y : C.Xbar) :
    matX C e (x * y) = matX C e x * matX C e y := by
  simp only [matX, map_mul]
  rw [← LinearMap.toMatrix_comp]
  rfl

theorem matX_one (e : Basis (Fin 4) (ZMod 2) C.At) : matX C e 1 = 1 := by
  simp only [matX, map_one]
  exact LinearMap.toMatrix_one e

theorem resAt_basis (e : Basis (Fin 4) (ZMod 2) C.At) (x : C.Xbar) (j : Fin 4) :
    C.resAt x (e j) = ∑ i, matX C e x i j • e i := by
  conv_lhs => rw [← e.sum_repr (C.resAt x (e j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [matX, LinearMap.toMatrix_apply, LinearEquiv.coe_coe]

theorem matX_injective (e : Basis (Fin 4) (ZMod 2) C.At) : Function.Injective (matX C e) := by
  intro x y h
  apply C.resAt_injective
  apply LinearEquiv.toLinearMap_injective
  exact (LinearMap.toMatrix e e).injective h

theorem exists_matX_eq (e : Basis (Fin 4) (ZMod 2) C.At) {g g' : Mat} (hg : g * g' = 1)
    (hg' : g' * g = 1) : ∃ x : C.Xbar, matX C e x = g := by
  let f : C.At ≃ₗ[ZMod 2] C.At :=
    LinearEquiv.ofLinearMap (Matrix.toLin e e g) (Matrix.toLin e e g')
      (by rw [← Matrix.toLin_mul, hg, Matrix.toLin_one])
      (by rw [← Matrix.toLin_mul, hg', Matrix.toLin_one])
  obtain ⟨x, hx⟩ := C.resAt_bijective.2 f
  refine ⟨x, ?_⟩
  rw [matX, hx]
  exact LinearMap.toMatrix_toLin e e g

variable (C) in
@[expose] noncomputable def gram (e : Basis (Fin 4) (ZMod 2) C.At) (s : S.O) : Mat :=
  fun i j => C.formOf s (e i) (e j)

theorem gram_mul (e : Basis (Fin 4) (ZMod 2) C.At) (s : S.O) (x : C.Xbar) :
    gram C e (s * x) = gram C e s * matX C e x := by
  ext i j
  simp only [gram, Matrix.mul_apply]
  rw [Config.formOf_mul_apply C s x.2, show (⟨(x : S.O), x.2⟩ : C.Xbar) = x from rfl,
    resAt_basis, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem toBilin_basis (e : Basis (Fin 4) (ZMod 2) C.At) (M : Mat) (i j : Fin 4) :
    Matrix.toBilin e M (e i) (e j) = M i j := by
  rw [← LinearMap.BilinForm.toMatrix_apply e, LinearMap.BilinForm.toMatrix_toBilin]

theorem exists_s₁ (e : Basis (Fin 4) (ZMod 2) C.At) :
    ∃ s₁ ∈ S.Mbar, s₁ ∉ C.Xbar ∧ s₁ * s₁ = 1 ∧ gram C e s₁ = J := by
  obtain ⟨σ₀, hσ₀, hσ₀X⟩ := C.exists_not_mem_Xbar
  set β := Matrix.toBilin e J with hβ
  have hsep : ∀ a', (∀ a, β a a' = 0) → a' = 0 := by
    intro a' ha'
    have hv : J *ᵥ e.repr a' = 0 := by
      ext i
      have := ha' (e i)
      rw [hβ, Matrix.toBilin_apply] at this
      simpa [Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, Finset.sum_ite_eq]
        using this
    have h0 : (e.repr a' : Fin 4 → ZMod 2) = 0 := by
      rw [← Matrix.one_mulVec (e.repr a' : Fin 4 → ZMod 2), ← J_mul_J, ← Matrix.mulVec_mulVec,
        hv, mulVec_zero]
    have h1 : e.repr a' = 0 := DFunLike.coe_injective (by rw [h0, Finsupp.coe_zero])
    exact (LinearEquiv.map_eq_zero_iff e.repr).mp h1
  obtain ⟨x, hx⟩ := C.exists_formOf_mul_eq hσ₀ hσ₀X β hsep
  have hs : σ₀ * x ∈ S.Mbar := S.Mbar.mul_mem hσ₀ (C.Xbar_le x.2)
  have hsX : σ₀ * x ∉ C.Xbar := fun h => hσ₀X (by
    simpa using C.Xbar.mul_mem h (C.Xbar.inv_mem x.2))
  have hgram : gram C e (σ₀ * x) = J := by
    ext i j
    simp only [gram, hx, hβ, toBilin_basis]
  refine ⟨σ₀ * x, hs, hsX, Config.mul_self_eq_one_of_formOf_symm hs hsX fun a a' => ?_, hgram⟩
  rw [hx, hβ, Matrix.toBilin_apply, Matrix.toBilin_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hJ : ∀ i j : Fin 4, J j i = J i j := fun i j => by
    rw [← Matrix.transpose_apply J i j, J_transpose]
  rw [hJ i j]
  ring

theorem formOf_conj (s : S.O) (x : C.Xbar) (a a' : C.At) :
    C.formOf ((x : S.O) * s * (x : S.O)⁻¹) a a' =
      C.formOf s (C.resAt x⁻¹ a) (C.resAt x⁻¹ a') := by
  rw [Config.formOf_apply, Config.formOf_apply, Config.resAt_apply, Config.resAt_apply,
    Subgroup.coe_inv]
  symm
  rw [← Config.polar_apply_apply (x : S.O), Config.apply_inv_apply, Config.mul_apply,
    Config.mul_apply]

theorem gram_conj (e : Basis (Fin 4) (ZMod 2) C.At) (s : S.O) (x : C.Xbar) :
    gram C e ((x : S.O) * s * (x : S.O)⁻¹) =
      (matX C e x⁻¹)ᵀ * gram C e s * matX C e x⁻¹ := by
  ext i j
  simp only [gram, formOf_conj, resAt_basis, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem eq_of_gram_eq (e : Basis (Fin 4) (ZMod 2) C.At) {s₁ s s' : S.O} (hs₁ : gram C e s₁ = J)
    (h₁ : s₁ ∈ S.Mbar) (h₁X : s₁ ∉ C.Xbar) (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar)
    (hs' : s' ∈ S.Mbar) (hs'X : s' ∉ C.Xbar) (h : gram C e s = gram C e s') : s = s' := by
  have h₁X' : s₁⁻¹ ∉ C.Xbar := fun h' => h₁X (by simpa using C.Xbar.inv_mem h')
  have hy : s₁⁻¹ * s ∈ C.Xbar :=
    C.mul_mem_Xbar_of_not_mem (S.Mbar.inv_mem h₁) hs h₁X' hsX
  have hy' : s₁⁻¹ * s' ∈ C.Xbar :=
    C.mul_mem_Xbar_of_not_mem (S.Mbar.inv_mem h₁) hs' h₁X' hs'X
  have e1 : gram C e s = J * matX C e ⟨_, hy⟩ := by
    rw [← hs₁, ← gram_mul]
    congr 1
    group
  have e2 : gram C e s' = J * matX C e ⟨_, hy'⟩ := by
    rw [← hs₁, ← gram_mul]
    congr 1
    group
  have hm : matX C e ⟨_, hy⟩ = matX C e ⟨_, hy'⟩ := by
    have := congrArg (J * ·) (e1.symm.trans (h.trans e2))
    simpa [← Matrix.mul_assoc, J_mul_J] using this
  have := congrArg Subtype.val (matX_injective e hm)
  simpa using this

end CFSG.LargeExtraspecial.GLW4
