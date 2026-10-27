module

public import CFSG.LargeExtraspecial.GLW4Tau

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR

theorem H₁_mul_G₃ : H₁ * G₃ = H₂ := by decide

theorem H₁_mul_G₂ : H₁ * G₂ = H₃ := by decide

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem formOf_eq_dot_gram (e : Basis (Fin 4) (ZMod 2) C.At) (s : S.O) (a a' : C.At) :
    C.formOf s a a' = e.equivFun a ⬝ᵥ (gram C e s *ᵥ e.equivFun a') := by
  have hM : LinearMap.BilinForm.toMatrix e (C.formOf s) = gram C e s := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [← Matrix.toBilin_toMatrix e (C.formOf s), hM, Matrix.toBilin_apply]
  simp only [dotProduct, mulVec, Basis.equivFun_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_inv (e : Basis (Fin 4) (ZMod 2) C.At) (s : S.O) :
    gram C e s⁻¹ = (gram C e s)ᵀ := by
  ext i j
  simp only [gram, Matrix.transpose_apply, Config.formOf_apply]
  rw [← Config.polar_apply_apply s ((e i : C.At) : S.Qt), Config.apply_inv_apply, polar_comm]

theorem eq_of_gram_eq' (e : Basis (Fin 4) (ZMod 2) C.At) {s s' : S.O} (hs : s ∈ S.Mbar)
    (hsX : s ∉ C.Xbar) (hs' : s' ∈ S.Mbar) (hs'X : s' ∉ C.Xbar)
    (h : gram C e s = gram C e s') : s = s' := by
  obtain ⟨s₁, h₁, h₁X, -, hJ⟩ := exists_s₁ e
  exact eq_of_gram_eq e hJ h₁ h₁X hs hsX hs' hs'X h

theorem inv_not_mem_Xbar {s : S.O} (hsX : s ∉ C.Xbar) : s⁻¹ ∉ C.Xbar := fun h =>
  hsX (by simpa using C.Xbar.inv_mem h)

theorem mul_not_mem_Xbar {s x : S.O} (hsX : s ∉ C.Xbar) (hx : x ∈ C.Xbar) : s * x ∉ C.Xbar :=
  fun h => hsX (by simpa using C.Xbar.mul_mem h (C.Xbar.inv_mem hx))

theorem mul_not_mem_Xbar' {s x : S.O} (hx : x ∈ C.Xbar) (hsX : s ∉ C.Xbar) : x * s ∉ C.Xbar :=
  fun h => hsX (by simpa using C.Xbar.mul_mem (C.Xbar.inv_mem hx) h)

theorem conj_not_mem_Xbar {s x : S.O} (hsX : s ∉ C.Xbar) (hx : x ∈ C.Xbar) :
    x * s * x⁻¹ ∉ C.Xbar :=
  mul_not_mem_Xbar (mul_not_mem_Xbar' hx hsX) (C.Xbar.inv_mem hx)

theorem mul_self_eq_one_of_gram (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hs : s ∈ S.Mbar)
    (hsX : s ∉ C.Xbar) (hsym : (gram C e s)ᵀ = gram C e s) : s * s = 1 := by
  have h := eq_of_gram_eq' e hs hsX (S.Mbar.inv_mem hs) (inv_not_mem_Xbar hsX)
    (by rw [gram_inv, hsym])
  calc s * s = s * s⁻¹ := congrArg (s * ·) h
    _ = 1 := mul_inv_cancel s

theorem commute_of_mul_self {a b : S.O} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) : a * b = b * a := by
  have h1 := eq_inv_of_mul_eq_one_left hab
  rw [h1, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

theorem exists_rho_data (e : Basis (Fin 4) (ZMod 2) C.At) {R : S.O} (hR : R ∈ S.Mbar)
    (hRX : R ∉ C.Xbar) (hN : gram C e R = N) :
    ∃ s₁ s₂ s₃ x : S.O, s₁ ∈ S.Mbar ∧ s₁ ∉ C.Xbar ∧ s₂ ∈ S.Mbar ∧ s₂ ∉ C.Xbar ∧
      s₃ ∈ S.Mbar ∧ s₃ ∉ C.Xbar ∧ x ∈ C.Xbar ∧ s₁ * s₁ = 1 ∧ s₁ * s₂ = s₂ * s₁ ∧
      s₁ * s₃ = s₃ * s₁ ∧ s₁ * s₂ * s₃ = R ∧ x * s₁ * x⁻¹ = s₁ ∧ x * s₂ * x⁻¹ = s₃ ∧
      ∀ a, C.formOf s₁ a a = 0 := by
  obtain ⟨y₁, hy₁⟩ := exists_matX_eq e G₁_mul_G₁ G₁_mul_G₁
  obtain ⟨y₂, hy₂⟩ := exists_matX_eq e G₂_mul_G₂ G₂_mul_G₂
  obtain ⟨y₃, hy₃⟩ := exists_matX_eq e G₃_mul_G₃ G₃_mul_G₃
  obtain ⟨x, hx⟩ := exists_matX_eq e kN_mul_kN kN_mul_kN
  have hM : ∀ y : C.Xbar, (y : S.O) ∈ S.Mbar := fun y => C.Xbar_le y.2
  set s₁ := R * (y₁ : S.O) with hs₁
  set s₂ := s₁ * (y₃ : S.O) with hs₂
  set s₃ := s₁ * (y₂ : S.O) with hs₃
  have m₁ : s₁ ∈ S.Mbar := S.Mbar.mul_mem hR (hM y₁)
  have m₁X : s₁ ∉ C.Xbar := mul_not_mem_Xbar hRX y₁.2
  have m₂ : s₂ ∈ S.Mbar := S.Mbar.mul_mem m₁ (hM y₃)
  have m₂X : s₂ ∉ C.Xbar := mul_not_mem_Xbar m₁X y₃.2
  have m₃ : s₃ ∈ S.Mbar := S.Mbar.mul_mem m₁ (hM y₂)
  have m₃X : s₃ ∉ C.Xbar := mul_not_mem_Xbar m₁X y₂.2
  have g₁ : gram C e s₁ = H₁ := by rw [hs₁, gram_mul, hN, hy₁, N_mul_G₁]
  have g₂ : gram C e s₂ = H₂ := by rw [hs₂, gram_mul, g₁, hy₃, H₁_mul_G₃]
  have g₃ : gram C e s₃ = H₃ := by rw [hs₃, gram_mul, g₁, hy₂, H₁_mul_G₂]
  have i₁ : s₁ * s₁ = 1 := mul_self_eq_one_of_gram e m₁ m₁X (by rw [g₁, H₁_transpose])
  have i₂ : s₂ * s₂ = 1 := mul_self_eq_one_of_gram e m₂ m₂X (by rw [g₂, H₂_transpose])
  have i₃ : s₃ * s₃ = 1 := mul_self_eq_one_of_gram e m₃ m₃X (by rw [g₃, H₃_transpose])
  have p₂ : s₁ * s₂ = y₃ := by rw [hs₂, ← mul_assoc, i₁, one_mul]
  have p₃ : s₁ * s₃ = y₂ := by rw [hs₃, ← mul_assoc, i₁, one_mul]
  have c₂ : s₁ * s₂ = s₂ * s₁ := commute_of_mul_self i₁ i₂ (by
    rw [p₂]; exact mul_self_eq_one_of_matX e hy₃ G₃_mul_G₃)
  have c₃ : s₁ * s₃ = s₃ * s₁ := commute_of_mul_self i₁ i₃ (by
    rw [p₃]; exact mul_self_eq_one_of_matX e hy₂ G₂_mul_G₂)
  have hRs : s₁ * s₂ * s₃ = R := by
    rw [p₂]
    refine eq_of_gram_eq' e (S.Mbar.mul_mem (hM y₃) m₃) (mul_not_mem_Xbar' y₃.2 m₃X) hR hRX ?_
    have h1 : (y₃ : S.O) * s₃ = ((y₃ : S.O) * s₃ * (y₃ : S.O)⁻¹) * (y₃ : S.O) := by group
    rw [h1, gram_mul, gram_conj, matX_inv e hy₃ G₃_mul_G₃, g₃, hy₃, Matrix.mul_assoc,
      G₃_mul_G₃, Matrix.mul_one, G₃_transpose_mul_H₃, hN]
  have hkN := matX_inv e hx kN_mul_kN
  have hx₁ : (x : S.O) * s₁ * (x : S.O)⁻¹ = s₁ :=
    eq_of_gram_eq' e (S.Mbar.mul_mem (S.Mbar.mul_mem (hM x) m₁) (S.Mbar.inv_mem (hM x)))
      (conj_not_mem_Xbar m₁X x.2) m₁ m₁X (by rw [gram_conj, hkN, g₁, cong_kN_H₁])
  have hx₂ : (x : S.O) * s₂ * (x : S.O)⁻¹ = s₃ :=
    eq_of_gram_eq' e (S.Mbar.mul_mem (S.Mbar.mul_mem (hM x) m₂) (S.Mbar.inv_mem (hM x)))
      (conj_not_mem_Xbar m₂X x.2) m₃ m₃X (by rw [gram_conj, hkN, g₂, cong_kN_H₂, g₃])
  refine ⟨s₁, s₂, s₃, x, m₁, m₁X, m₂, m₂X, m₃, m₃X, x.2, i₁, c₂, c₃, hRs, hx₁, hx₂, fun a => ?_⟩
  rw [formOf_eq_dot_gram e, g₁]
  exact H₁_alt _

end CFSG.LargeExtraspecial.GLW4
