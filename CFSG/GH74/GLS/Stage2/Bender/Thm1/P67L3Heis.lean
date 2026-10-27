module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3HeisCore
public import CFSG.GH74.GLS.Stage2.OddAut.HeisFrame
public import CFSG.GH74.GLS.Stage2.OddAut.HeisPair
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut

section Heis

variable {K : Type} [Field K] [Finite K]

theorem false_of_heis {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {V Z : Subgroup (MulAut (projectiveSL 3 K))} (h2 : N2Cfg (projectiveSL 3 K) 3 V Z)
    (h3 : N3Deriv (projectiveSL 3 K) V Z) (hVI : V ≤ linearAutGroup 3 K)
    (a b : GL (Fin 3) K) (u : Kˣ) (hu : u ≠ 1) (ha : conjAut 3 K a ∈ V) (hb : conjAut 3 K b ∈ V)
    (hab : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a)) : False := by
  classical
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨hr, hr2, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := id h2
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe
    exact setLike_mul_comm hx hy
  have hVp : ∀ x ∈ V, x ^ 3 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hna : ¬ ∀ A ∈ V.comap (conjAut 3 K), ∀ B ∈ V.comap (conjAut 3 K), A * B = B * A := by
    intro h
    have hc := h a ha b hb
    apply hu
    have h1 : GeneralLinearGroup.scalar (Fin 3) u * (b * a) = 1 * (b * a) := by
      rw [← hab, hc, one_mul]
    exact scalar_injective (by rw [map_one]; exact mul_right_cancel h1)
  have hBU := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.linear_projective_nonabelian_plane_coprime_centralizer_central
    (F := K) (p := 3) Nat.prime_three (by norm_num) V hVI hVab hVp hVc hna
  have hZD : ∀ z ∈ Z, z ∈ linearAutGroup 3 K → z = 1 := by
    intro z hz hzD
    have hzc : z ∈ Subgroup.centralizer (V : Set (MulAut (projectiveSL 3 K))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hcomm v hv z hz
    have hzV : z ∈ V := by
      rw [← hBU.2.2.1]
      exact ⟨hzc, hzD⟩
    have hordZ : orderOf z ∣ Nat.card ↥Z := by
      have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hZcop hordZ
      (orderOf_dvd_of_pow_eq_one (hVp z hzV)))
  obtain ⟨ua, hua⟩ := (conjAut_eq_one_iff_of_three_le (le_refl 3) (a ^ 3)).mp
    (by rw [map_pow]; exact hVp _ ha)
  obtain ⟨ub, hub⟩ := (conjAut_eq_one_iff_of_three_le (le_refl 3) (b ^ 3)).mp
    (by rw [map_pow]; exact hVp _ hb)
  obtain ⟨i, j, γ, y, ξ, hx3, hxy, hξ1, hij⟩ := exists_cube_pair a b ua ub u hua hub hab hu
  set x : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j) with hxdef
  have hxV : conjAut 3 K x ∈ V := by
    have : conjAut 3 K x = conjAut 3 K a ^ i * conjAut 3 K b ^ j := by
      rw [hxdef, map_mul, map_mul, map_pow, map_pow, conjAut_scalar, one_mul]
    rw [this]
    exact V.mul_mem (V.pow_mem ha i) (V.pow_mem hb j)
  have hξ3 : ξ ^ 3 = 1 := comm_scalar_cube hxy
  have hξ1' : (ξ : K) ≠ 1 := fun h => hξ1 (Units.ext h)
  have hξ3' : (ξ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hξ3, Units.val_one]
  have hξ0 : (ξ : K) ≠ 0 := ξ.ne_zero
  have hx3' : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  have hxy' : (x : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
      (ξ : K) • ((y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hxy
    simp only [Units.val_mul, coe_scalar_smul, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  obtain ⟨B, lam, hBu, hlam0, hB⟩ := heis_frame (ξ : K) hξ1' hξ3' (x : Matrix (Fin 3) (Fin 3) K)
    (y : Matrix (Fin 3) (Fin 3) K) hx3' y.isUnit hxy'
  set Bg : GL (Fin 3) K := hBu.unit with hBg
  have hBgmat : (Bg : Matrix (Fin 3) (Fin 3) K) = B := rfl
  have hdiag : ∀ k : Fin 3, (![1, (ξ : K), (ξ : K) ^ 2] : Fin 3 → K) k ≠ 0 := by
    intro k
    fin_cases k <;> simp [hξ0]
  have hconjD : Bg⁻¹ * x * Bg = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 lam hlam0) *
      diagGLK ![1, (ξ : K), (ξ : K) ^ 2] hdiag := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    have hdm : lam • diagonal ![1, (ξ : K), (ξ : K) ^ 2] =
        diagonal (fun i : Fin 3 => (ξ : K) ^ (i : ℕ) * lam) := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      fin_cases i <;> simp [mul_comm]
    have hD1 : ((GeneralLinearGroup.scalar (Fin 3) (Units.mk0 lam hlam0) *
        diagGLK ![1, (ξ : K), (ξ : K) ^ 2] hdiag : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun i : Fin 3 => (ξ : K) ^ (i : ℕ) * lam) := by
      rw [Units.val_mul, coe_scalar_smul, coe_diagGLK, Units.val_mk0, Matrix.smul_mul,
        Matrix.one_mul, hdm]
    rw [Units.val_mul x Bg, Units.val_mul Bg, hD1, hBgmat]
    exact hB
  set φ : MulAut (projectiveSL 3 K) := conjAut 3 K Bg⁻¹ with hφ
  have h2₁ := h2.map_mulEquiv (MulAut.congr φ)
  have h3₁ := h3.map_mulEquiv φ
  have hΔV : conjAut 3 K (diagGLK ![1, (ξ : K), (ξ : K) ^ 2] hdiag) ∈
      V.map (MulAut.congr φ).toMonoidHom := by
    refine ⟨conjAut 3 K x, hxV, ?_⟩
    show MulAut.congr φ (conjAut 3 K x) = _
    rw [congr_eq_mul_mul_inv, hφ, ← map_inv, ← map_mul, ← map_mul, inv_inv, hconjD, map_mul,
      conjAut_scalar, one_mul]
  have hZD₁ : ∀ z' ∈ Z.map (MulAut.congr φ).toMonoidHom, z' ∈ linearAutGroup 3 K → z' = 1 := by
    rintro _ ⟨z, hz, rfl⟩ hzD
    have hφD : φ ∈ linearAutGroup 3 K := conjAut_mem_linearAutGroup _
    have hz' : z ∈ linearAutGroup 3 K := by
      have : z = φ⁻¹ * (MulAut.congr φ z) * φ := by rw [congr_eq_mul_mul_inv]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hφD) hzD) hφD
    have hz1 := hZD z hz hz'
    show MulAut.congr φ z = 1
    rw [hz1, map_one]
  exact false_of_heis_frame hp hp5 hf hK h2K hξ1' hξ3' hdiag h2₁ h3₁ hΔV hZD₁

end Heis

end CFSG.GH74.GLS.Stage2.Bender.Thm1
