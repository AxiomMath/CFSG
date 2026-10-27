module

public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Eig
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Basic

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix

section Split

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem mulVec_pow_eigen {A : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K} {κ : K}
    (h : A *ᵥ v = κ • v) (n : ℕ) : (A ^ n) *ᵥ v = κ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]

omit [Finite K] in
theorem unit_pow_eq_of_mulVec {A : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K} {κ α : K} (hv : v ≠ 0)
    (h : A *ᵥ v = κ • v) {r : ℕ} (hA : A ^ r = α • (1 : Matrix (Fin 3) (Fin 3) K)) : α = κ ^ r := by
  have h1 := mulVec_pow_eigen h r
  rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  by_contra hne
  apply hv
  have : (α - κ ^ r) • v = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp this with h' | h'
  · exact absurd (sub_eq_zero.mp h') hne
  · exact h'

theorem lin3_comm_diag {r : ℕ} (hr : r.Prime) (hrK : r ∣ Nat.card K - 1)
    (a b : Matrix (Fin 3) (Fin 3) K) (α β : K) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (ha : a ^ r = α • (1 : Matrix (Fin 3) (Fin 3) K)) (hb : b ^ r = β • (1 : Matrix (Fin 3) (Fin 3) K))
    (hab : a * b = b * a)
    (hind : ∀ (i j : ℕ) (c : K), c ≠ 0 → a ^ i * b ^ j = c • (1 : Matrix (Fin 3) (Fin 3) K) →
      r ∣ i ∧ r ∣ j) :
    ∃ (B : Matrix (Fin 3) (Fin 3) K) (da db : Fin 3 → K), IsUnit B.det ∧
      a * B = B * Matrix.diagonal da ∧ b * B = B * Matrix.diagonal db := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hr0 : 0 < r := hr.pos
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  have hω : IsPrimitiveRoot (ω₀ : K) r := by
    have h1 := IsPrimitiveRoot.orderOf ω₀
    rw [hω₀] at h1
    exact IsPrimitiveRoot.coe_units_iff.mpr h1
  obtain ⟨i, j, γ, hi, hj, hij, hγ⟩ := exists_exponents_pow hr (Units.mk0 α hα0) (Units.mk0 β hβ0)
  have hγ' : α ^ i * β ^ j = (γ : K) ^ r := by
    have := congrArg (fun u : Kˣ => (u : K)) hγ
    simpa using this
  have hcab : Commute a b := hab
  set x : Matrix (Fin 3) (Fin 3) K := a ^ i * b ^ j with hx
  have hxr : x ^ r = ((γ : K) ^ r) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have e1 : x ^ r = (a ^ r) ^ i * (b ^ r) ^ j := by
      rw [hx, (hcab.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i r, mul_comm j r,
        pow_mul, pow_mul]
    rw [e1, ha, hb, smul_pow, smul_pow, one_pow, one_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, hγ']
  have hγne : (γ : K) ≠ 0 := γ.ne_zero
  set x₀ : Matrix (Fin 3) (Fin 3) K := ((γ : K)⁻¹) • x with hx₀
  have hx₀r : x₀ ^ r = 1 := by
    rw [hx₀, smul_pow, hxr, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hγne), one_smul]
  have hxx₀ : x = (γ : K) • x₀ := by
    rw [hx₀, smul_smul, mul_inv_cancel₀ hγne, one_smul]
  have hns : ∀ c : K, x₀ ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, zero_pow hr0.ne'] at hx₀r
      have := congrFun (congrFun hx₀r 0) 0
      simp at this
    have hxc : a ^ i * b ^ j = ((γ : K) * c) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have : x = (γ : K) • x₀ := hxx₀
      rw [hx] at this
      rw [this, hc, smul_smul]
    obtain ⟨h1, h2⟩ := hind i j _ (mul_ne_zero hγne hc0) hxc
    have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt h1 hi
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt h2 hj
    rcases hij with h | h
    · exact h hi0
    · exact h hj0
  have hca : Commute a x₀ :=
    (((Commute.refl a).pow_right i).mul_right (hcab.pow_right j)).smul_right _
  have hcb : Commute b x₀ :=
    (((hcab.symm).pow_right i).mul_right ((Commute.refl b).pow_right j)).smul_right _
  obtain ⟨v, hv0, hv⟩ := exists_line_eigenvector hr0 hω x₀ hx₀r hns
  obtain ⟨κa, hκa⟩ := hv a hca.symm.eq
  obtain ⟨κb, hκb⟩ := hv b hcb.symm.eq
  have hακ : α = κa ^ r := unit_pow_eq_of_mulVec hv0 hκa ha
  have hβκ : β = κb ^ r := unit_pow_eq_of_mulVec hv0 hκb hb
  have hκa0 : κa ≠ 0 := by
    rintro rfl
    rw [zero_pow hr0.ne'] at hακ
    exact hα0 hακ
  have hκb0 : κb ≠ 0 := by
    rintro rfl
    rw [zero_pow hr0.ne'] at hβκ
    exact hβ0 hβκ
  have ha₀ : (κa⁻¹ • a) ^ r = 1 := by
    rw [smul_pow, ha, smul_smul, hακ, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hκa0), one_smul]
  have hb₀ : (κb⁻¹ • b) ^ r = 1 := by
    rw [smul_pow, hb, smul_smul, hβκ, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hκb0), one_smul]
  have hab₀ : (κa⁻¹ • a) * (κb⁻¹ • b) = (κb⁻¹ • b) * (κa⁻¹ • a) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hab, smul_comm]
  obtain ⟨B, da, db, hB, hBa, hBb⟩ := exists_joint_eigenbasis hr0 hω _ _ ha₀ hb₀ hab₀
  refine ⟨B, fun m => κa * da m, fun m => κb * db m, hB, ?_, ?_⟩
  · have e1 : a = κa • (κa⁻¹ • a) := by rw [smul_smul, mul_inv_cancel₀ hκa0, one_smul]
    rw [e1, Matrix.smul_mul, hBa]
    ext m n
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
    ring
  · have e1 : b = κb • (κb⁻¹ • b) := by rw [smul_smul, mul_inv_cancel₀ hκb0, one_smul]
    rw [e1, Matrix.smul_mul, hBb]
    ext m n
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
    ring

end Split

end CFSG.GH74.GLS.Stage2.OddAut
