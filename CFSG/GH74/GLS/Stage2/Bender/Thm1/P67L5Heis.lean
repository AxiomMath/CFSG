module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L5HeisCore
public import CFSG.GH74.GLS.Stage2.OddAut.HeisFrameN
public import CFSG.GH74.GLS.Stage2.OddAut.HeisPairR
public import CFSG.GH74.GLS.Stage2.OddAut.LinNSmall
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut

section Heis5

variable {K : Type} [Field K] [Finite K]

theorem false_of_heis5 {p f : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {V Z : Subgroup (MulAut (projectiveSL 5 K))} (h2 : N2Cfg (projectiveSL 5 K) 5 V Z)
    (h3 : N3Deriv (projectiveSL 5 K) V Z) (hVI : V ≤ linearAutGroup 5 K)
    (a b : GL (Fin 5) K) (u : Kˣ) (hu : u ≠ 1) (ha : conjAut 5 K a ∈ V) (hb : conjAut 5 K b ∈ V)
    (hab : a * b = GeneralLinearGroup.scalar (Fin 5) u * (b * a)) : False := by
  classical
  obtain ⟨hr, hr2, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := id h2
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe
    exact setLike_mul_comm hx hy
  have hVp : ∀ x ∈ V, x ^ 5 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hna : ¬ ∀ A ∈ V.comap (conjAut 5 K), ∀ B ∈ V.comap (conjAut 5 K), A * B = B * A := by
    intro h
    have hc := h a ha b hb
    apply hu
    have h1 : GeneralLinearGroup.scalar (Fin 5) u * (b * a) = 1 * (b * a) := by
      rw [← hab, hc, one_mul]
    exact scalar_injective_n (n := 5) (by norm_num) (by rw [map_one]; exact mul_right_cancel h1)
  have hBU := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.linear_projective_nonabelian_plane_coprime_centralizer_central
    (F := K) (p := 5) Nat.prime_five (by norm_num) V hVI hVab hVp hVc hna
  have hZD : ∀ z ∈ Z, z ∈ linearAutGroup 5 K → z = 1 := by
    intro z hz hzD
    have hzc : z ∈ Subgroup.centralizer (V : Set (MulAut (projectiveSL 5 K))) := by
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
  obtain ⟨ua, hua⟩ := (conjAut_eq_one_iff_of_three_le (by norm_num : 3 ≤ 5) (a ^ 5)).mp
    (by rw [map_pow]; exact hVp _ ha)
  obtain ⟨ub, hub⟩ := (conjAut_eq_one_iff_of_three_le (by norm_num : 3 ≤ 5) (b ^ 5)).mp
    (by rw [map_pow]; exact hVp _ hb)
  have hu5 : u ^ 5 = 1 := comm_scalar_pow_n (by norm_num) hab hub
  obtain ⟨i, j, γ, y, ξ, hx5, hxy, hξ1, hij⟩ :=
    exists_pow_pair Nat.prime_five (by decide) a b ua ub u hua hub hab hu hu5
  set x : GL (Fin 5) K := GeneralLinearGroup.scalar (Fin 5) γ⁻¹ * (a ^ i * b ^ j) with hxdef
  have hxV : conjAut 5 K x ∈ V := by
    have : conjAut 5 K x = conjAut 5 K a ^ i * conjAut 5 K b ^ j := by
      rw [hxdef, map_mul, map_mul, map_pow, map_pow, conjAut_scalar, one_mul]
    rw [this]
    exact V.mul_mem (V.pow_mem ha i) (V.pow_mem hb j)
  have hξ5 : ξ ^ 5 = 1 := comm_scalar_pow_n_dim hxy
  have hξ1' : (ξ : K) ≠ 1 := fun h => hξ1 (Units.ext h)
  have hξ5' : (ξ : K) ^ 5 = 1 := by rw [← Units.val_pow_eq_pow_val, hξ5, Units.val_one]
  have hξ0 : (ξ : K) ≠ 0 := ξ.ne_zero
  have hx5' : (x : Matrix (Fin 5) (Fin 5) K) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx5, Units.val_one]
  have hxy' : (x : Matrix (Fin 5) (Fin 5) K) * (y : Matrix (Fin 5) (Fin 5) K) =
      (ξ : K) • ((y : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K)) := by
    have := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)) hxy
    simp only [Units.val_mul, coe_scalar_smul_n, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  have hξprim : IsPrimitiveRoot (ξ : K) 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hξ5' hξ1')
  obtain ⟨B, lam, hBu, hlam0, hB⟩ := heis_frame_r (by norm_num) (ξ : K) hξprim
    (x : Matrix (Fin 5) (Fin 5) K) (y : Matrix (Fin 5) (Fin 5) K) hx5' y.isUnit hxy'
  set Bg : GL (Fin 5) K := hBu.unit with hBg
  have hBgmat : (Bg : Matrix (Fin 5) (Fin 5) K) = B := rfl
  have hdiag : ∀ k : Fin 5, (fun i : Fin 5 => (ξ : K) ^ (i : ℕ)) k ≠ 0 := fun k => pow_ne_zero _ hξ0
  have hconjD : Bg⁻¹ * x * Bg = GeneralLinearGroup.scalar (Fin 5) (Units.mk0 lam hlam0) *
      Ln.diagGLK (fun i : Fin 5 => (ξ : K) ^ (i : ℕ)) hdiag := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    have hdm : lam • diagonal (fun i : Fin 5 => (ξ : K) ^ (i : ℕ)) =
        diagonal (fun i : Fin 5 => (ξ : K) ^ (i : ℕ) * lam) := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      simp [mul_comm]
    have hD1 : ((GeneralLinearGroup.scalar (Fin 5) (Units.mk0 lam hlam0) *
        Ln.diagGLK (fun i : Fin 5 => (ξ : K) ^ (i : ℕ)) hdiag : GL (Fin 5) K) :
          Matrix (Fin 5) (Fin 5) K) = diagonal (fun i : Fin 5 => (ξ : K) ^ (i : ℕ) * lam) := by
      rw [Units.val_mul, coe_scalar_smul_n, Ln.coe_diagGLK, Units.val_mk0, Matrix.smul_mul,
        Matrix.one_mul, hdm]
    rw [Units.val_mul x Bg, Units.val_mul Bg, hD1, hBgmat]
    exact hB
  set φ : MulAut (projectiveSL 5 K) := conjAut 5 K Bg⁻¹ with hφ
  have h2₁ := h2.map_mulEquiv (MulAut.congr φ)
  have h3₁ := h3.map_mulEquiv φ
  have hΔV : conjAut 5 K (Ln.diagGLK (fun i : Fin 5 => (ξ : K) ^ (i : ℕ)) hdiag) ∈
      V.map (MulAut.congr φ).toMonoidHom := by
    refine ⟨conjAut 5 K x, hxV, ?_⟩
    show MulAut.congr φ (conjAut 5 K x) = _
    rw [congr_eq_mul_mul_inv, hφ, ← map_inv, ← map_mul, ← map_mul, inv_inv, hconjD, map_mul,
      conjAut_scalar, one_mul]
  have hZD₁ : ∀ z' ∈ Z.map (MulAut.congr φ).toMonoidHom, z' ∈ linearAutGroup 5 K → z' = 1 := by
    rintro _ ⟨z, hz, rfl⟩ hzD
    have hφD : φ ∈ linearAutGroup 5 K := conjAut_mem_linearAutGroup _
    have hz' : z ∈ linearAutGroup 5 K := by
      have : z = φ⁻¹ * (MulAut.congr φ z) * φ := by rw [congr_eq_mul_mul_inv]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hφD) hzD) hφD
    have hz1 := hZD z hz hz'
    show MulAut.congr φ z = 1
    rw [hz1, map_one]
  exact Ln.false_of_heis5_frame hp hp7 hf hK hξ1' hξ5' hdiag h2₁ h3₁ hΔV hZD₁

theorem false_of_e1_five {p f : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (h5 : 5 ∣ Nat.card K - 1) {V Z : Subgroup (MulAut (projectiveSL 5 K))}
    (h2 : N2Cfg (projectiveSL 5 K) 5 V Z) (h3 : N3Deriv (projectiveSL 5 K) V Z)
    (hVI : V ≤ linearAutGroup 5 K) : False := by
  classical
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨hr, -, hVe, hVc, -⟩ := id h2
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe
    exact setLike_mul_comm hx hy
  have hVe' : ∀ v ∈ V, v ^ 5 = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  have hVI' : V ≤ (conjAut 5 K).range := by rw [← linearAutGroup_eq_range]; exact hVI
  rcases inner_plane_classify_n (by norm_num) Nat.prime_five (by norm_num) h5 V hVI' hVc hVe' hVab with
    ⟨B, hB⟩ | ⟨a, b, u, hu, ha, hb, hab⟩
  · exact Ln.false_of_toral_deriv (by norm_num) h2 h3 h2K B hB
  · exact false_of_heis5 hp hp7 hf hK h2 h3 hVI a b u hu ha hb hab

end Heis5

end CFSG.GH74.GLS.Stage2.Bender.Thm1
