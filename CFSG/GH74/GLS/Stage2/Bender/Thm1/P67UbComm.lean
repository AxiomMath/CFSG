module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem herm_inv_smul_left {x : SUid σ n} (u v : Fin n → K) :
    herm σ u (x⁻¹ • v) = herm σ (x • u) v := by
  conv_rhs => rw [← smul_inv_smul x v]
  rw [herm_smul_smul]

theorem comm_tv {x g : SUid σ n} {a : Fin n → K} {c : K}
    (hg : ∀ v, g • v = v + (c * herm σ a v) • a) (hxa : x • a = a) : x * g = g * x := by
  rw [← mul_inv_eq_iff_eq_mul]
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, hg, smul_add, smul_inv_smul, smul_comm x, hxa, herm_inv_smul_left, hxa,
    hg v]

theorem comm_siegel (hσ : ∀ c, σ (σ c) = c) {x g : SUid σ n} {e w : Fin n → K} {μ l l' : K}
    (hg : ∀ v, g • v = v + (μ * herm σ e v) • w - (σ μ * herm σ w v) • e)
    (hxe : x • e = l • e) (hxw : x • w = l' • w) (hll : σ l * l' = 1) : x * g = g * x := by
  have hll' : σ l' * l = 1 := by
    have := congrArg σ hll
    rw [map_mul, hσ, map_one] at this
    rw [mul_comm]
    exact this
  rw [← mul_inv_eq_iff_eq_mul]
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, hg, smul_sub, smul_add, smul_inv_smul, smul_comm x, smul_comm x, hxe,
    hxw, herm_inv_smul_left, herm_inv_smul_left, hxe, hxw, herm_smul_left, herm_smul_left,
    smul_smul, smul_smul]
  have h1 : μ * (σ l * herm σ e v) * l' = μ * herm σ e v := by
    linear_combination (μ * herm σ e v) * hll
  have h2 : σ μ * (σ l' * herm σ w v) * l = σ μ * herm σ w v := by
    linear_combination (σ μ * herm σ w v) * hll'
  rw [h1, h2, hg v]

theorem comm_eichler {x g : SUid σ n} {e y : Fin n → K} {c : K}
    (hg : ∀ v, g • v = v + herm σ e v • (y + c • e) - herm σ y v • e)
    (hxe : x • e = e) (hxy : x • y = y) : x * g = g * x := by
  rw [← mul_inv_eq_iff_eq_mul]
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, hg, smul_sub, smul_add, smul_inv_smul, smul_comm x, smul_comm x,
    smul_add, smul_comm x c e, hxe, hxy, herm_inv_smul_left, herm_inv_smul_left, hxe, hxy, hg v]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub
