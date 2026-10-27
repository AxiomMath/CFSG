module

import all CFSG.Fischer.F4
public import CFSG.LargeExtraspecial.Asc611IChain
public import CFSG.LargeExtraspecial.Asc611IStepE1

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m}

theorem actsBy_hp_of {q₀ q₁ n s : Fin m → K} (hN0 : invN e q₀ = n + s) (hN1 : invN e q₁ = s)
    {u₀ : SUid frob m}
    (hu : ∀ x, u₀ • x = x + herm frob s x • n + herm frob n x • s + (1 * herm frob n x) • n) :
    ActsBy e ![q₀, q₁] ((hpF 2).map eF4) u₀ := fun x => by
  rw [hu, frameMap_hp2, hN0, hN1, herm_add_left]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp [two_eq_zero]

theorem actsBy_m0_of {q₀ q₁ n s : Fin m → K} (hN0 : invN e q₀ = n + ω • s)
    (hN1 : invN e q₁ = n + (ω * ω) • s) {u₀ : SUid frob m}
    (hu : ∀ x, u₀ • x = x + herm frob s x • n + herm frob n x • s + (1 * herm frob n x) • n) :
    ActsBy e ![q₀, q₁] ((m0F 2).map eF4) u₀ := fun x => by
  rw [hu, frameMap_m02, hN0, hN1]
  simp only [herm_add_left, herm_smul_left, map_mul, frob_omega]
  set X := herm frob n x
  set Y := herm frob s x
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-X * n i - X * s i - Y * n i + ω * X * s i - 2 * ω * Y * n i -
    ω ^ 2 * X * s i - ω ^ 2 * Y * s i - ω ^ 3 * Y * s i) * AS35N.omega_sq_add +
    (X * n i + X * s i + Y * n i + ω * Y * n i) * two_eq_zero

theorem chainF_r2_k : stepF !![1, 1; 1, 0] ![1, wF] = rk1F ![1, wF] := by decide

theorem rk1F_01 : rk1F ![(0 : F4), 1] = !![0, 0; 0, 1] := by decide

variable {U : Subgroup (PG m)}

theorem herm_shift_symm {k : SUid frob m} (hkN : ∀ x, invN e (k • x) = invN e x)
    (hperp : ∀ x b, invN e b = 0 → herm frob (k • x + x) b = 0) (x y : Fin m → K) :
    herm frob x (k • y + y) = herm frob (k • x + x) y := by
  have hkN' : ∀ x, invN e (k • x + x) = 0 := fun x => by rw [invN_add, hkN, vec_add_self]
  have h1 : herm frob (k • x) (k • y) = herm frob x y := herm_smul_smul frob k x y
  have hS : herm frob (k • x + x) (k • y + y) = 0 :=
    herm_eq_zero_comm frob frob_frob (hperp y _ (hkN' x))
  set Sx := k • x + x with hSx
  set Sy := k • y + y with hSy
  have hkx : k • x = x + Sx := by
    rw [hSx, add_comm (k • x) x, ← add_assoc, vec_add_self, zero_add]
  have hky : k • y = y + Sy := by
    rw [hSy, add_comm (k • y) y, ← add_assoc, vec_add_self, zero_add]
  clear_value Sx Sy
  rw [hkx, hky, herm_add_left, herm_add_right, herm_add_right, hS, add_zero] at h1
  linear_combination h1 - herm frob Sx y * two_eq_zero

theorem false_of_rank_two_hp (S : Setup e U) {k : SUid frob m}
    (hk : (QuotientGroup.mk k : PG m) ∈ U) (hkN : ∀ x, invN e (k • x) = invN e x)
    (hker : ∀ v, invN e v = 0 → k • v = v)
    (hperp : ∀ x b, invN e b = 0 → herm frob (k • x + x) b = 0) {q₀ q₁ a : Fin m → K}
    (F2 : IsFrame e ![q₀, q₁])
    (hno : ∀ z, (∀ i, herm frob (![q₀, q₁] i) (invN e z) = 0) → herm frob z (invN e z) = 0)
    (ha_eq : invN e (q₀ + q₁) = invN e a)
    (hBa : ∀ y, herm frob a (k • y + y) = herm frob q₁ (invN e y)) : False := by
  have he := S.invol
  have hact := actsBy_of_maximal he F2 hno hker hperp
  have hB0 : ∀ v y, invN e v = 0 → herm frob v (k • y + y) = 0 := fun v y hv =>
    herm_eq_zero_comm frob frob_frob (hperp y v hv)
  have hsa := herm_shift_symm hkN hperp
  have hq01 : ∀ y : Fin m → K, herm frob (q₀ + q₁) (k • y + y) = herm frob q₁ (invN e y) := by
    intro y
    have hv : invN e (q₀ + q₁ + a) = 0 := by rw [invN_add, ha_eq, vec_add_self]
    have : q₀ + q₁ = a + (q₀ + q₁ + a) := by
      rw [add_comm a, add_assoc, vec_add_self, add_zero]
    rw [this, herm_add_left, hB0 _ _ hv, add_zero, hBa]
  have h0 := hq01 q₀
  have h1 := hq01 q₁
  rw [herm_add_left] at h0 h1
  rw [show herm frob q₁ (invN e q₀) = 0 from F2.orth 1 0] at h0
  rw [show herm frob q₁ (invN e q₁) = 1 from F2.orth 1 1] at h1
  set b00 := herm frob q₀ (k • q₀ + q₀) with hb00
  set b01 := herm frob q₀ (k • q₁ + q₁) with hb01
  set b10 := herm frob q₁ (k • q₀ + q₀) with hb10
  set b11 := herm frob q₁ (k • q₁ + q₁) with hb11
  have hc10 : b10 = frob b01 := by rw [hb10, hb01, hsa, herm_conj frob frob_frob]
  have hc00 : frob b00 = b00 := by
    rw [hb00]
    conv_lhs => rw [hsa q₀ q₀]
    rw [← herm_conj frob frob_frob (k • q₀ + q₀) q₀]
  have e10 : b10 = b00 := by linear_combination h0 - b00 * two_eq_zero
  have e01 : b01 = b00 := by
    have := congrArg frob hc10
    rw [frob_frob, e10, hc00] at this
    exact this.symm
  have e11 : b11 = 1 + b00 := by linear_combination h1 - e01 - b00 * two_eq_zero
  have hentry : ∀ j i : Fin 2, herm frob (![q₀, q₁] i) (k • ![q₀, q₁] j + ![q₀, q₁] j) =
      !![b00, b10; b01, b11] j i := by
    intro j i
    fin_cases j <;> fin_cases i <;> rfl
  have hact' : ActsBy e ![q₀, q₁] !![b00, b10; b01, b11] k := by
    have hfun : (fun j i => herm frob (![q₀, q₁] i) (k • ![q₀, q₁] j + ![q₀, q₁] j)) =
        !![b00, b10; b01, b11] := by
      ext j i
      exact hentry j i
    rw [← hfun]
    exact hact
  rcases (frob_eq_self_iff _).1 hc00 with h | h
  ·
    have hM : !![b00, b10; b01, b11] = (rk1F ![(0 : F4), 1]).map eF4 := by
      rw [rk1F_01, e10, e01, e11, h]
      ext j i
      fin_cases j <;> fin_cases i <;> simp
    rw [hM] at hact'
    exact false_of_rank_one S F2 hk (by decide) hact'
  ·
    have hM : !![b00, b10; b01, b11] = (!![(1 : F4), 1; 1, 0]).map eF4 := by
      rw [e10, e01, e11, h]
      ext j i
      fin_cases j <;> fin_cases i <;> simp [add_self_K]
    rw [hM] at hact'
    obtain ⟨hu₁, ha₁⟩ := step_mem S F2 hk hact' (c := ![1, wF]) (by decide)
    rw [chainF_r2_k] at ha₁
    exact false_of_rank_one S F2 hu₁ (by decide) ha₁

end CFSG.LargeExtraspecial.Asc611I
