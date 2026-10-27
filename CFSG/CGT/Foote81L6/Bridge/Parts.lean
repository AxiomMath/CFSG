module

public import CFSG.CGT.Foote81L6.Bridge.Gens
public import CFSG.CGT.Foote81L6.Bridge.DihedralLift

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Subgroup

@[expose] def toP {n : ℕ} (a : PHat n) : P n := if h : a.det = 0 then ⟨a, mem_P.2 h⟩ else 1

theorem coe_toP {n : ℕ} {a : PHat n} (h : a.det = 0) : (toP a : PHat n) = a := by
  rw [toP, dif_pos h]

theorem πT_eq_one_of_coe_eq_cz {n : ℕ} {x : P n} (h : (x : PHat n) = Gen.cz n) : πT n x = 1 := by
  rw [πT_eq_one_iff]
  right; right; right
  apply Subtype.ext
  rw [h, Subgroup.coe_mul, coe_cP, coe_zP, Gen.cz_eq]

theorem πT_eq_one_of_coe_eq_zF {n : ℕ} {x : P n} (h : (x : PHat n) = PHat.zF) : πT n x = 1 := by
  rw [πT_eq_one_iff]
  right; right; left
  exact Subtype.ext h

theorem πT_eq_of_coe_eq_mul_cz {n : ℕ} {x y : P n} (h : (x : PHat n) = (y : PHat n) * Gen.cz n) :
    πT n x = πT n y := by
  have : x = y * (y⁻¹ * x) := by group
  rw [this, map_mul, πT_eq_one_of_coe_eq_cz (x := y⁻¹ * x), mul_one]
  rw [Subgroup.coe_mul, Subgroup.coe_inv, h, inv_mul_cancel_left]

theorem πT_eq_of_coe_eq_mul_zF {n : ℕ} {x y : P n} (h : (x : PHat n) = (y : PHat n) * PHat.zF) :
    πT n x = πT n y := by
  have : x = y * (y⁻¹ * x) := by group
  rw [this, map_mul, πT_eq_one_of_coe_eq_zF (x := y⁻¹ * x), mul_one]
  rw [Subgroup.coe_mul, Subgroup.coe_inv, h, inv_mul_cancel_left]

theorem SD.det_mk {n : ℕ} (i : ZMod (2 ^ n)) (j : ZMod 2) : (⟨i, j⟩ : SD n).det = par i + j := rfl

namespace Gen

variable {n : ℕ}

theorem det_ρ₀ : (ρ₀ n).det = 0 := by
  rw [PHat.det, ρ₀]
  simp only [SD.det_mk, SD.det_one, add_zero, par_add, par_hf]
  exact CharTwo.add_self_eq_zero _

theorem det_ρ₁ : (ρ₁ n).det = 0 := by
  rw [PHat.det, ρ₁]
  simp only [SD.det_mk, SD.det_one, add_zero, par_neg]
  exact CharTwo.add_self_eq_zero _

theorem det_κ₀ : (κ₀ n).det = 0 := by
  rw [PHat.det, κ₀]
  simp only [SD.det_mk, SD.det_one, add_zero, par_neg]
  rw [show par (qr n) + 1 + (par (qr n) + 1) = (par (qr n) + 1) + (par (qr n) + 1) by ring]
  exact CharTwo.add_self_eq_zero _

theorem det_κ₁ : (κ₁ n).det = 0 := by
  rw [PHat.det, κ₁]
  simp only [SD.det_mk, SD.det_one, add_zero]
  exact CharTwo.add_self_eq_zero _

theorem det_t : (t n).det = 0 := by
  rw [PHat.det, t]
  simp only [SD.det_σ, SD.det_one, add_zero]
  exact CharTwo.add_self_eq_zero _

theorem det_s (hn : 3 ≤ n) : (s n).det = 0 := by
  rw [PHat.det, s]
  simp only [SD.det_mk, SD.det_one, add_zero, par_qr hn, par_one (by omega : 1 ≤ n), zero_add]
  exact CharTwo.add_self_eq_zero _

theorem det_rA : (rA n).det = 0 := by
  rw [PHat.det, rA]
  simp only [SD.det_mk, SD.det_one, add_zero, zero_add]
  rw [show (2 : ZMod (2 ^ n)) = 1 + 1 by norm_num, par_add]
  exact CharTwo.add_self_eq_zero _

theorem det_sA (hn : 1 ≤ n) : (sA n).det = 0 := by
  rw [PHat.det, sA]
  simp only [SD.det_mk, SD.det_one, zero_add, par_one hn]
  exact CharTwo.add_self_eq_zero _

theorem det_ωt (hn : 1 ≤ n) : (ωt n).det = 0 := by
  rw [PHat.det, ωt]
  simp only [SD.det_σ, SD.det_ω hn, SD.det_one, add_zero]
  exact CharTwo.add_self_eq_zero _

theorem det_aH (hn : 3 ≤ n) : (aH n).det = 0 := by
  rw [PHat.det, aH]
  simp only [SD.det_mk, SD.det_one, zero_add, add_zero, par_qr hn]

end Gen

section Gens

variable (n : ℕ)

@[expose] def ρ₀T : TM n := πT n (toP (Gen.ρ₀ n))

@[expose] def ρ₁T : TM n := πT n (toP (Gen.ρ₁ n))

@[expose] def κ₀T : TM n := πT n (toP (Gen.κ₀ n))

@[expose] def κ₁T : TM n := πT n (toP (Gen.κ₁ n))

@[expose] def tT : TM n := πT n (toP (Gen.t n))

@[expose] def sT : TM n := πT n (toP (Gen.s n))

@[expose] def rAT : TM n := πT n (toP (Gen.rA n))

@[expose] def sAT : TM n := πT n (toP (Gen.sA n))

@[expose] def ωtT : TM n := πT n (toP (Gen.ωt n))

@[expose] def aT : TM n := πT n (toP (Gen.aH n))

end Gens

section Relations

variable {n : ℕ} (hn : 3 ≤ n)
include hn

theorem κ₀T_mul_ρ₀T : κ₀T n * ρ₀T n = (ρ₀T n)⁻¹ * κ₀T n := by
  simp only [κ₀T, ρ₀T, ← map_mul, ← map_inv]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toP Gen.det_κ₀, coe_toP Gen.det_ρ₀]
  exact Gen.κ₀_mul_ρ₀ hn

theorem κ₀T_conj_ρ₀T : κ₀T n * ρ₀T n * (κ₀T n)⁻¹ = (ρ₀T n)⁻¹ := by
  rw [κ₀T_mul_ρ₀T hn, mul_inv_cancel_right]

theorem κ₀T_mul_κ₀T : κ₀T n * κ₀T n = 1 := by
  rw [κ₀T, ← map_mul]
  apply πT_eq_one_of_coe_eq_cz
  rw [Subgroup.coe_mul, coe_toP Gen.det_κ₀, Gen.κ₀_mul_κ₀ hn]

theorem κ₁T_mul_ρ₁T : κ₁T n * ρ₁T n = (ρ₁T n)⁻¹ * κ₁T n := by
  simp only [κ₁T, ρ₁T, ← map_mul, ← map_inv]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toP Gen.det_κ₁, coe_toP Gen.det_ρ₁]
  exact Gen.κ₁_mul_ρ₁ hn

theorem κ₁T_conj_ρ₁T : κ₁T n * ρ₁T n * (κ₁T n)⁻¹ = (ρ₁T n)⁻¹ := by
  rw [κ₁T_mul_ρ₁T hn, mul_inv_cancel_right]

theorem κ₁T_mul_κ₁T : κ₁T n * κ₁T n = 1 := by
  rw [κ₁T, ← map_mul]
  apply πT_eq_one_of_coe_eq_cz
  rw [Subgroup.coe_mul, coe_toP Gen.det_κ₁, Gen.κ₁_mul_κ₁ hn]

theorem ρ₀T_pow_hf : ρ₀T n ^ 2 ^ (n - 1) = 1 := by
  rw [ρ₀T, ← map_pow]
  apply πT_eq_one_of_coe_eq_cz
  rw [Subgroup.coe_pow, coe_toP Gen.det_ρ₀, Gen.ρ₀_pow_hf hn]

theorem ρ₁T_pow_hf : ρ₁T n ^ 2 ^ (n - 1) = 1 := by
  rw [ρ₁T, ← map_pow]
  apply πT_eq_one_of_coe_eq_cz
  rw [Subgroup.coe_pow, coe_toP Gen.det_ρ₁, Gen.ρ₁_pow_hf hn]

theorem πT_ne_one_of_x₂ {y : P n} (hy : (y : PHat n).x₂ = ⟨qr n, 0⟩) : πT n y ≠ 1 := by
  rw [Ne, πT_eq_one_iff]
  have h1 : qr n ≠ 0 := (qr_ne_zero (n := n)).resolve_right (by omega)
  have h2 : qr n ≠ hf n := qr_ne_hf (by omega)
  rintro (rfl | rfl | rfl | rfl)
  · exact h1 (congrArg SD.i hy).symm
  · exact h2 (congrArg SD.i hy).symm
  · exact h1 (congrArg SD.i hy).symm
  · apply h2
    have := congrArg SD.i hy
    simp only [Subgroup.coe_mul, coe_cP, coe_zP, PHat.c, PHat.zF, PHat.mul_x₂, PHat.sw₂_zero,
      mul_one] at this
    exact this.symm

theorem πT_ne_one_of_x₃ {y : P n} (hy : (y : PHat n).x₃ = ⟨qr n, 0⟩) : πT n y ≠ 1 := by
  rw [Ne, πT_eq_one_iff]
  have h1 : qr n ≠ 0 := (qr_ne_zero (n := n)).resolve_right (by omega)
  have h2 : qr n ≠ hf n := qr_ne_hf (by omega)
  rintro (rfl | rfl | rfl | rfl)
  · exact h1 (congrArg SD.i hy).symm
  · exact h2 (congrArg SD.i hy).symm
  · exact h2 (congrArg SD.i hy).symm
  · apply h1
    have := congrArg SD.i hy
    simp only [Subgroup.coe_mul, coe_cP, coe_zP, PHat.c, PHat.zF, PHat.mul_x₃,
      SD.z_mul_self] at this
    exact this.symm

theorem ρ₀T_pow_qr_ne_one : ρ₀T n ^ 2 ^ (n - 2) ≠ 1 := by
  rw [ρ₀T, ← map_pow]
  apply πT_ne_one_of_x₂ hn
  rw [Subgroup.coe_pow, coe_toP Gen.det_ρ₀, Gen.ρ₀_pow_qr hn]
  rfl

theorem ρ₁T_pow_qr_ne_one : ρ₁T n ^ 2 ^ (n - 2) ≠ 1 := by
  rw [ρ₁T, ← map_pow]
  apply πT_ne_one_of_x₂ hn
  rw [Subgroup.coe_pow, coe_toP Gen.det_ρ₁, Gen.ρ₁_pow_qr hn]
  rfl

theorem orderOf_ρ₀T : orderOf (ρ₀T n) = 2 ^ (n - 1) := by
  have h := orderOf_eq_prime_pow (p := 2) (n := n - 2) (ρ₀T_pow_qr_ne_one hn)
    (by rw [show n - 2 + 1 = n - 1 by omega]; exact ρ₀T_pow_hf hn)
  rwa [show n - 2 + 1 = n - 1 by omega] at h

theorem orderOf_ρ₁T : orderOf (ρ₁T n) = 2 ^ (n - 1) := by
  have h := orderOf_eq_prime_pow (p := 2) (n := n - 2) (ρ₁T_pow_qr_ne_one hn)
    (by rw [show n - 2 + 1 = n - 1 by omega]; exact ρ₁T_pow_hf hn)
  rwa [show n - 2 + 1 = n - 1 by omega] at h

theorem commute_ρ₀T_ρ₁T : Commute (ρ₀T n) (ρ₁T n) := by
  simp only [Commute, SemiconjBy, ρ₀T, ρ₁T, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_toP Gen.det_ρ₀, coe_toP Gen.det_ρ₁]
  exact Gen.ρ₀_mul_ρ₁ hn

theorem commute_κ₀T_κ₁T : Commute (κ₀T n) (κ₁T n) := by
  simp only [Commute, SemiconjBy, κ₀T, κ₁T, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_toP Gen.det_κ₀, coe_toP Gen.det_κ₁]
  exact Gen.κ₀_mul_κ₁ hn

theorem commute_ρ₀T_κ₁T : Commute (ρ₀T n) (κ₁T n) := by
  simp only [Commute, SemiconjBy, ρ₀T, κ₁T, ← map_mul]
  apply πT_eq_of_coe_eq_mul_cz
  simp only [Subgroup.coe_mul, coe_toP Gen.det_ρ₀, coe_toP Gen.det_κ₁]
  exact Gen.ρ₀_mul_κ₁ hn

theorem commute_κ₀T_ρ₁T : Commute (κ₀T n) (ρ₁T n) := by
  simp only [Commute, SemiconjBy, κ₀T, ρ₁T, ← map_mul]
  apply πT_eq_of_coe_eq_mul_cz
  simp only [Subgroup.coe_mul, coe_toP Gen.det_κ₀, coe_toP Gen.det_ρ₁]
  exact Gen.κ₀_mul_ρ₁ hn

theorem tT_mul_tT : tT n * tT n = 1 := by
  rw [tT, ← map_mul, ← map_one (πT n)]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_toP Gen.det_t, Gen.t_mul_t hn]
  rfl

theorem tT_inv : (tT n)⁻¹ = tT n := inv_eq_of_mul_eq_one_right (tT_mul_tT hn)

theorem tT_conj_ρ₀T : tT n * ρ₀T n * (tT n)⁻¹ = ρ₁T n := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [tT, ρ₀T, ρ₁T, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_toP Gen.det_t, coe_toP Gen.det_ρ₀, coe_toP Gen.det_ρ₁]
  exact Gen.t_mul_ρ₀ hn

theorem tT_conj_κ₀T : tT n * κ₀T n * (tT n)⁻¹ = κ₁T n := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [tT, κ₀T, κ₁T, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_toP Gen.det_t, coe_toP Gen.det_κ₀, coe_toP Gen.det_κ₁]
  exact Gen.t_mul_κ₀ hn

theorem tT_conj_ρ₁T : tT n * ρ₁T n * (tT n)⁻¹ = ρ₀T n := by
  rw [← tT_conj_ρ₀T hn, tT_inv hn]
  simp only [← mul_assoc]
  rw [tT_mul_tT hn, one_mul, mul_assoc, tT_mul_tT hn, mul_one]

theorem tT_conj_κ₁T : tT n * κ₁T n * (tT n)⁻¹ = κ₀T n := by
  rw [← tT_conj_κ₀T hn, tT_inv hn]
  simp only [← mul_assoc]
  rw [tT_mul_tT hn, one_mul, mul_assoc, tT_mul_tT hn, mul_one]

theorem sT_mul_sT : sT n * sT n = 1 := by
  rw [sT, ← map_mul]
  apply πT_eq_one_of_coe_eq_cz
  rw [Subgroup.coe_mul, coe_toP (Gen.det_s hn), Gen.s_mul_s hn]

theorem sT_conj_ρ₀T : sT n * ρ₀T n * (sT n)⁻¹ = ρ₁T n ^ (θ n).val := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [sT, ρ₀T, ρ₁T, ← map_mul, ← map_pow]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP (Gen.det_s hn), coe_toP Gen.det_ρ₀,
    coe_toP Gen.det_ρ₁]
  exact Gen.s_mul_ρ₀ hn

theorem sT_conj_κ₀T : sT n * κ₀T n * (sT n)⁻¹ = κ₁T n * (ρ₁T n)⁻¹ ^ (1 + (qr n).val) := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [sT, κ₀T, κ₁T, ρ₁T, ← map_mul, ← map_pow, ← map_inv]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, coe_toP (Gen.det_s hn),
    coe_toP Gen.det_κ₀, coe_toP Gen.det_κ₁, coe_toP Gen.det_ρ₁]
  exact Gen.s_mul_κ₀ hn

theorem sT_conj_ρ₁T : sT n * ρ₁T n * (sT n)⁻¹ = ρ₀T n ^ (θ n).val := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [sT, ρ₀T, ρ₁T, ← map_mul, ← map_pow]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP (Gen.det_s hn), coe_toP Gen.det_ρ₀,
    coe_toP Gen.det_ρ₁]
  exact Gen.s_mul_ρ₁ hn

theorem sT_conj_κ₁T : sT n * κ₁T n * (sT n)⁻¹ = κ₀T n * ρ₀T n ^ (2 ^ (n - 2) - 1) := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [sT, κ₀T, κ₁T, ρ₀T, ← map_mul, ← map_pow]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP (Gen.det_s hn), coe_toP Gen.det_κ₀,
    coe_toP Gen.det_κ₁, coe_toP Gen.det_ρ₀]
  exact Gen.s_mul_κ₁ hn

theorem tT_conj_sT :
    tT n * sT n * (tT n)⁻¹ = sT n * ρ₀T n ^ 2 ^ (n - 2) * ρ₁T n ^ 2 ^ (n - 2) := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [tT, sT, ρ₀T, ρ₁T, ← map_mul, ← map_pow]
  apply πT_eq_of_coe_eq_mul_cz
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP (Gen.det_s hn), coe_toP Gen.det_t,
    coe_toP Gen.det_ρ₀, coe_toP Gen.det_ρ₁, Gen.ρ₀_pow_qr hn, Gen.ρ₁_pow_qr hn]
  rw [Gen.t_mul_s hn]
  simp only [mul_assoc]
  rw [← Gen.cz_comm (Gen.t n)]

theorem sAT_conj_rAT : sAT n * rAT n * (sAT n)⁻¹ = (rAT n)⁻¹ := by
  have h : sAT n * rAT n = (rAT n)⁻¹ * sAT n := by
    simp only [sAT, rAT, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toP (Gen.det_sA (n := n) (by omega)),
      coe_toP Gen.det_rA]
    exact Gen.sA_mul_rA hn
  rw [h, mul_inv_cancel_right]

theorem sAT_mul_sAT : sAT n * sAT n = 1 := by
  rw [sAT, ← map_mul]
  apply πT_eq_one_of_coe_eq_zF
  rw [Subgroup.coe_mul, coe_toP (Gen.det_sA (n := n) (by omega)), Gen.sA_mul_sA hn]

theorem rAT_pow_qr : rAT n ^ 2 ^ (n - 2) = 1 := by
  rw [rAT, ← map_pow]
  apply πT_eq_one_of_coe_eq_zF
  rw [Subgroup.coe_pow, coe_toP Gen.det_rA, Gen.rA_pow_qr hn]

theorem rAT_pow_half : rAT n ^ 2 ^ (n - 3) = aT n := by
  rw [rAT, aT, ← map_pow]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_toP Gen.det_rA, coe_toP (Gen.det_aH hn), Gen.rA_pow_qr_half hn]

theorem aT_ne_one : aT n ≠ 1 := by
  apply πT_ne_one_of_x₃ hn
  rw [coe_toP (Gen.det_aH hn)]
  rfl

theorem orderOf_rAT : orderOf (rAT n) = 2 ^ (n - 2) := by
  have h := orderOf_eq_prime_pow (p := 2) (n := n - 3)
    (by rw [rAT_pow_half hn]; exact aT_ne_one hn)
    (by rw [show n - 3 + 1 = n - 2 by omega]; exact rAT_pow_qr hn)
  rwa [show n - 3 + 1 = n - 2 by omega] at h

theorem tT_conj_ωtT : tT n * ωtT n * (tT n)⁻¹ = (ωtT n)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [tT, ωtT, ← map_mul, ← map_inv]
  apply πT_eq_of_coe_eq_mul_zF
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toP Gen.det_t,
    coe_toP (Gen.det_ωt (n := n) (by omega))]
  rw [Gen.t_mul_ωt hn, mul_assoc, ← PHat.zF_comm (Gen.t n), ← mul_assoc]

theorem ωtT_mul_ωtT : ωtT n * ωtT n = rAT n := by
  simp only [ωtT, rAT, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_toP (Gen.det_ωt (n := n) (by omega)), coe_toP Gen.det_rA,
    Gen.ωt_mul_ωt hn]

theorem ωtT_pow_hf : ωtT n ^ 2 ^ (n - 1) = 1 := by
  rw [ωtT, ← map_pow]
  apply πT_eq_one_of_coe_eq_zF
  rw [Subgroup.coe_pow, coe_toP (Gen.det_ωt (n := n) (by omega)), Gen.ωt_pow_hf hn]

theorem ωtT_pow_qr : ωtT n ^ 2 ^ (n - 2) = aT n := by
  rw [ωtT, aT, ← map_pow]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_toP (Gen.det_ωt (n := n) (by omega)), coe_toP (Gen.det_aH hn),
    Gen.ωt_pow_qr hn]

theorem orderOf_ωtT : orderOf (ωtT n) = 2 ^ (n - 1) := by
  have h := orderOf_eq_prime_pow (p := 2) (n := n - 2)
    (by rw [ωtT_pow_qr hn]; exact aT_ne_one hn)
    (by rw [show n - 2 + 1 = n - 1 by omega]; exact ωtT_pow_hf hn)
  rwa [show n - 2 + 1 = n - 1 by omega] at h

theorem sAT_eq : sAT n = ωtT n * ωtT n * tT n * ωtT n := by
  simp only [sAT, ωtT, tT, ← map_mul]
  apply πT_eq_of_coe_eq_mul_zF
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_toP (Gen.det_sA (n := n) (by omega)), coe_toP (Gen.det_ωt (n := n) (by omega)),
    coe_toP Gen.det_t, ← Gen.sA_mul_zF hn, mul_assoc, PHat.zF_mul_zF, mul_one]

theorem tT_conj_rAT : tT n * rAT n * (tT n)⁻¹ = (rAT n)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [tT, rAT, ← map_mul, ← map_inv]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toP Gen.det_t, coe_toP Gen.det_rA]
  exact Gen.t_mul_rA hn

theorem tT_conj_sAT : tT n * sAT n * (tT n)⁻¹ = rAT n ^ (2 ^ (n - 2) - 1) * sAT n := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [tT, rAT, sAT, ← map_mul, ← map_pow]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_toP Gen.det_t, coe_toP Gen.det_rA,
    coe_toP (Gen.det_sA (n := n) (by omega))]
  exact Gen.t_mul_sA hn

end Relations

section Invariants

variable {n : ℕ}

theorem eT_ρ₀T : eT n (ρ₀T n) = 1 := by rw [ρ₀T, eT_πT, coe_toP Gen.det_ρ₀]; rfl

theorem eT_ρ₁T : eT n (ρ₁T n) = 1 := by rw [ρ₁T, eT_πT, coe_toP Gen.det_ρ₁]; rfl

theorem eT_κ₀T : eT n (κ₀T n) = Multiplicative.ofAdd 1 := by
  rw [κ₀T, eT_πT, coe_toP Gen.det_κ₀]; rfl

theorem eT_κ₁T : eT n (κ₁T n) = Multiplicative.ofAdd 1 := by
  rw [κ₁T, eT_πT, coe_toP Gen.det_κ₁]; rfl

theorem j3T_rAT : j3T n (rAT n) = 1 := by rw [rAT, j3T_πT, coe_toP Gen.det_rA]; rfl

theorem j3T_sAT (hn : 1 ≤ n) : j3T n (sAT n) = Multiplicative.ofAdd 1 := by
  rw [sAT, j3T_πT, coe_toP (Gen.det_sA hn)]; rfl

theorem j3T_ωtT (hn : 1 ≤ n) : j3T n (ωtT n) = 1 := by
  rw [ωtT, j3T_πT, coe_toP (Gen.det_ωt hn)]; rfl

theorem j3T_tT : j3T n (tT n) = Multiplicative.ofAdd 1 := by rw [tT, j3T_πT, coe_toP Gen.det_t]; rfl

theorem jT_ρ₀T : jT n (ρ₀T n) = 1 := by rw [ρ₀T, jT_πT, coe_toP Gen.det_ρ₀]; rfl

theorem jT_ρ₁T : jT n (ρ₁T n) = 1 := by rw [ρ₁T, jT_πT, coe_toP Gen.det_ρ₁]; rfl

theorem jT_κ₀T : jT n (κ₀T n) = 1 := by
  rw [κ₀T, jT_πT, coe_toP Gen.det_κ₀]
  show Multiplicative.ofAdd ((1 : ZMod 2) + 1) = 1
  rw [PHat.one_add_one_zmod_two]
  rfl

theorem jT_κ₁T : jT n (κ₁T n) = 1 := by rw [κ₁T, jT_πT, coe_toP Gen.det_κ₁]; rfl

theorem jT_sT (hn : 3 ≤ n) : jT n (sT n) = Multiplicative.ofAdd 1 := by
  rw [sT, jT_πT, coe_toP (Gen.det_s hn)]; rfl

theorem d3T_tT : d3T n (tT n) = Multiplicative.ofAdd 1 := by
  rw [tT, d3T_πT, coe_toP Gen.det_t]; exact congrArg _ SD.det_σ

theorem ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := fun h =>
  (one_ne_zero : (1 : ZMod 2) ≠ 0) (congrArg Multiplicative.toAdd h)

theorem mul_pow_ne_one_of_parity {M : Type*} [Group M] (φ : M →* Multiplicative (ZMod 2))
    {u w : M} (hu : φ u = 1) (hw : φ w = Multiplicative.ofAdd 1) (k : ℕ) : w * u ^ k ≠ 1 := by
  intro h
  have := congrArg φ h
  rw [map_one, map_mul, map_pow, hu, one_pow, mul_one, hw] at this
  exact ofAdd_one_ne_one this

end Invariants

section Subgroups

variable {n : ℕ} (hn : 3 ≤ n)

instance neZero_two_pow (k : ℕ) : NeZero (2 ^ k) := ⟨by positivity⟩

@[expose] noncomputable def f₀ : DihedralGroup (2 ^ (n - 1)) →* TM n :=
  dihedralLift _ (ρ₀T n) (κ₀T n) (ρ₀T_pow_hf hn) (κ₀T_mul_κ₀T hn) (κ₀T_conj_ρ₀T hn)

@[expose] noncomputable def f₁ : DihedralGroup (2 ^ (n - 1)) →* TM n :=
  dihedralLift _ (ρ₁T n) (κ₁T n) (ρ₁T_pow_hf hn) (κ₁T_mul_κ₁T hn) (κ₁T_conj_ρ₁T hn)

@[expose] noncomputable def fA : DihedralGroup (2 ^ (n - 2)) →* TM n :=
  dihedralLift _ (rAT n) (sAT n) (rAT_pow_qr hn) (sAT_mul_sAT hn) (sAT_conj_rAT hn)

@[expose] noncomputable def fAt : DihedralGroup (2 ^ (n - 1)) →* TM n :=
  dihedralLift _ (ωtT n) (tT n) (ωtT_pow_hf hn) (tT_mul_tT hn) (tT_conj_ωtT hn)

theorem f₀_injective : Function.Injective (f₀ hn) :=
  dihedralLift_injective _ _ _ _ _ _ (orderOf_ρ₀T hn)
    (mul_pow_ne_one_of_parity (eT n) eT_ρ₀T eT_κ₀T)

theorem f₁_injective : Function.Injective (f₁ hn) :=
  dihedralLift_injective _ _ _ _ _ _ (orderOf_ρ₁T hn)
    (mul_pow_ne_one_of_parity (eT n) eT_ρ₁T eT_κ₁T)

theorem fA_injective : Function.Injective (fA hn) :=
  dihedralLift_injective _ _ _ _ _ _ (orderOf_rAT hn)
    (mul_pow_ne_one_of_parity (j3T n) j3T_rAT (j3T_sAT (by omega)))

theorem fAt_injective : Function.Injective (fAt hn) :=
  dihedralLift_injective _ _ _ _ _ _ (orderOf_ωtT hn)
    (mul_pow_ne_one_of_parity (j3T n) (j3T_ωtT (by omega)) j3T_tT)

@[expose] noncomputable def B₀T : Subgroup (TM n) := (f₀ hn).range

@[expose] noncomputable def B₁T : Subgroup (TM n) := (f₁ hn).range

@[expose] noncomputable def AT : Subgroup (TM n) := (fA hn).range

@[expose] noncomputable def AtT : Subgroup (TM n) := (fAt hn).range

@[expose] noncomputable def BT : Subgroup (TM n) := B₀T hn ⊔ B₁T hn ⊔ zpowers (sT n)

@[expose] noncomputable def b₀T : TM n := f₀ hn (CFSG.CGT.Foote81L6.zc (n - 1))

@[expose] noncomputable def b₁T : TM n := f₁ hn (CFSG.CGT.Foote81L6.zc (n - 1))

theorem b₀T_eq : b₀T hn = ρ₀T n ^ 2 ^ (n - 2) := by
  rw [b₀T, zc_eq (by omega), f₀, dihedralLift_r, ZMod.val_natCast, Nat.mod_eq_of_lt
    (Nat.pow_lt_pow_right (by norm_num) (by omega)), show n - 1 - 1 = n - 2 by omega]

theorem b₁T_eq : b₁T hn = ρ₁T n ^ 2 ^ (n - 2) := by
  rw [b₁T, zc_eq (by omega), f₁, dihedralLift_r, ZMod.val_natCast, Nat.mod_eq_of_lt
    (Nat.pow_lt_pow_right (by norm_num) (by omega)), show n - 1 - 1 = n - 2 by omega]

theorem aT_eq_fAt : aT n = fAt hn (CFSG.CGT.Foote81L6.zc (n - 1)) := by
  rw [zc_eq (by omega), fAt, dihedralLift_r, ZMod.val_natCast, Nat.mod_eq_of_lt
    (Nat.pow_lt_pow_right (by norm_num) (by omega)), show n - 1 - 1 = n - 2 by omega,
    ωtT_pow_qr hn]

theorem aT_eq_fA : aT n = fA hn (CFSG.CGT.Foote81L6.zc (n - 2)) := by
  rw [zc_eq (by omega), fA, dihedralLift_r, ZMod.val_natCast, Nat.mod_eq_of_lt
    (Nat.pow_lt_pow_right (by norm_num) (by omega)), show n - 2 - 1 = n - 3 by omega,
    rAT_pow_half hn]

theorem ρ₀T_mem_B₀T : ρ₀T n ∈ B₀T hn := u_mem_dihedralLift_range _ _ _ _ _ _

theorem κ₀T_mem_B₀T : κ₀T n ∈ B₀T hn := w_mem_dihedralLift_range _ _ _ _ _ _

theorem ρ₁T_mem_B₁T : ρ₁T n ∈ B₁T hn := u_mem_dihedralLift_range _ _ _ _ _ _

theorem κ₁T_mem_B₁T : κ₁T n ∈ B₁T hn := w_mem_dihedralLift_range _ _ _ _ _ _

theorem rAT_mem_AT : rAT n ∈ AT hn := u_mem_dihedralLift_range _ _ _ _ _ _

theorem sAT_mem_AT : sAT n ∈ AT hn := w_mem_dihedralLift_range _ _ _ _ _ _

theorem ωtT_mem_AtT : ωtT n ∈ AtT hn := u_mem_dihedralLift_range _ _ _ _ _ _

theorem tT_mem_AtT : tT n ∈ AtT hn := w_mem_dihedralLift_range _ _ _ _ _ _

theorem sT_mem_BT : sT n ∈ BT hn := mem_sup_right (mem_zpowers _)

theorem B₀T_le_BT : B₀T hn ≤ BT hn := le_sup_left.trans le_sup_left

theorem B₁T_le_BT : B₁T hn ≤ BT hn := le_sup_right.trans le_sup_left

end Subgroups

end CFSG.CGT.Foote81L6.Bridge
