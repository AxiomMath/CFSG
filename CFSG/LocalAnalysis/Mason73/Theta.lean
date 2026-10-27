module

public import CFSG.LocalAnalysis.Mason73.TableIII
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

@[expose] def thetaK (π : Fin81.R0) : ℕ :=
  if (π : Perm (Fin 4)) = 1 ∨ (π : Perm (Fin 4)) = swap 0 2 * swap 1 3 then 0
  else if (π : Perm (Fin 4)) = swap 0 1 * swap 2 3 ∨ (π : Perm (Fin 4)) = swap 0 3 * swap 1 2
    then 2
  else 1

@[expose] def thetaChi (π : Fin81.R0) : Fin 4 → ℕ :=
  if (π : Perm (Fin 4)) = swap 2 3 ∨ (π : Perm (Fin 4)) = swap 2 3 * (swap 0 2 * swap 1 3) then
    ![1, 0, 0, 0]
  else if (π : Perm (Fin 4)) = swap 0 1 ∨ (π : Perm (Fin 4)) = swap 0 2 * swap 1 3 * swap 2 3 then
    ![0, 0, 1, 0]
  else if (π : Perm (Fin 4)) = swap 0 1 * swap 2 3 then ![0, 1, 1, 0]
  else if (π : Perm (Fin 4)) = swap 0 3 * swap 1 2 then ![1, 0, 0, 1]
  else ![0, 0, 0, 0]

@[expose] def thetaVec (n : ℕ) (π : Fin81.R0) : Fin 4 → ZMod (2 ^ n) :=
  fun i => (thetaK π : ZMod (2 ^ n)) * ss n + hh n * (thetaChi π i : ZMod (2 ^ n))

theorem thetaK_add_thetaChi_even : ∀ π : Fin81.R0,
    (thetaK π + (thetaChi π 0 + thetaChi π 1 + thetaChi π 2 + thetaChi π 3)) % 2 = 0 := by
  decide

theorem sum_thetaVec (hn : 3 ≤ n) (π : Fin81.R0) : ∑ i, thetaVec n π i = 0 := by
  have h4 := four_mul_ss hn
  have key := (hh_mul_natCast_eq_iff (n := n) (by omega)
    (thetaK π + (thetaChi π 0 + thetaChi π 1 + thetaChi π 2 + thetaChi π 3)) 0).2
    (by rw [thetaK_add_thetaChi_even π])
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add] at key
  rw [Fin.sum_univ_four]
  simp only [thetaVec]
  linear_combination (thetaK π : ZMod (2 ^ n)) * h4 + key

theorem detSum_thetaVec (hn : 3 ≤ n) (π : Fin81.R0) : detSum (thetaVec n π) 1 :=
  detSum_one_iff.2 (sum_thetaVec hn π)

theorem detSum_add_thetaVec (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) : detSum (d + thetaVec n π) π := by
  rw [detSum] at h ⊢
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, sum_thetaVec hn π, add_zero]
  exact h

theorem isConst_const_add {a : ZMod (2 ^ n)} {v : Fin 4 → ZMod (2 ^ n)} :
    IsConst ((fun _ => a) + v) ↔ IsConst v := by
  constructor
  · intro h i j
    have := h i j
    simp only [Pi.add_apply] at this
    exact add_left_cancel this
  · intro h i j
    simp only [Pi.add_apply]
    rw [h i j]

theorem thetaChi_cocycle : ∀ π σ : Fin81.R0, ∀ i j : Fin 4,
    ((thetaChi π i + thetaChi σ ((π : Perm (Fin 4))⁻¹ i)) + thetaChi (π * σ) j) % 2 =
      ((thetaChi π j + thetaChi σ ((π : Perm (Fin 4))⁻¹ j)) + thetaChi (π * σ) i) % 2 := by
  decide

theorem isConst_thetaVec_cocycle (hn : 1 ≤ n) (π σ : Fin81.R0) :
    IsConst (thetaVec n π + pv (π : Perm (Fin 4)) (thetaVec n σ) - thetaVec n (π * σ)) := by
  have heq : thetaVec n π + pv (π : Perm (Fin 4)) (thetaVec n σ) - thetaVec n (π * σ) =
      (fun _ => ((thetaK π : ZMod (2 ^ n)) + thetaK σ - thetaK (π * σ)) * ss n) +
        (hv n (thetaChi π + fun i => thetaChi σ ((π : Perm (Fin 4))⁻¹ i)) -
          hv n (thetaChi (π * σ))) := by
    funext i
    simp only [thetaVec, Pi.add_apply, Pi.sub_apply, pv, hv, Nat.cast_add]
    ring
  rw [heq, isConst_const_add, hv_sub_hv_isConst_iff hn]
  exact fun i j => thetaChi_cocycle π σ i j

@[expose] def thetaFun (hn : 3 ≤ n) (g : L4Model n) : L4Model n :=
  g * el (pv ((piT g : Perm (Fin 4))⁻¹) (thetaVec n (piT g))) 1
    (detSum_pv _ (detSum_thetaVec hn _))

theorem thetaFun_el (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) :
    thetaFun hn (el d π h) = el (d + thetaVec n π) π (detSum_add_thetaVec hn h) := by
  rw [thetaFun, el_mul]
  refine el_congr _ _ ?_ (mul_one π)
  show d + pv (π : Perm (Fin 4)) (pv (π : Perm (Fin 4))⁻¹ (thetaVec n π)) = d + thetaVec n π
  rw [← pv_mul, mul_inv_cancel, pv_one]

theorem thetaFun_mul (hn : 3 ≤ n) (g g' : L4Model n) :
    thetaFun hn (g * g') = thetaFun hn g * thetaFun hn g' := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  obtain ⟨e, σ, h', rfl⟩ := exists_eq_el g'
  rw [el_mul, thetaFun_el, thetaFun_el, thetaFun_el, el_mul, el_eq_el_iff (by omega)]
  refine ⟨rfl, ?_⟩
  have hc := isConst_thetaVec_cocycle (n := n) (by omega) π σ
  have heq : d + thetaVec n π + pv (π : Perm (Fin 4)) (e + thetaVec n σ) -
      (d + pv (π : Perm (Fin 4)) e + thetaVec n (π * σ)) =
      thetaVec n π + pv (π : Perm (Fin 4)) (thetaVec n σ) - thetaVec n (π * σ) := by
    rw [pv_add]
    abel
  rw [heq]
  exact hc

theorem thetaFun_thetaFun (hn : 3 ≤ n) (g : L4Model n) : thetaFun hn (thetaFun hn g) = g := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [thetaFun_el, thetaFun_el, el_eq_el_iff (by omega)]
  refine ⟨rfl, ?_⟩
  have h2 := two_mul_hh (n := n) (by omega)
  refine isConst_of_forall_eq (-(2 * ((thetaK π : ZMod (2 ^ n)) * ss n))) fun i => ?_
  simp only [Pi.sub_apply, Pi.add_apply, thetaVec]
  linear_combination -((thetaChi π i : ℕ) : ZMod (2 ^ n)) * h2

theorem thetaVec_one : thetaVec n 1 = 0 := by
  funext i
  have hk : thetaK (1 : Fin81.R0) = 0 := by decide
  have hχ : thetaChi (1 : Fin81.R0) = ![0, 0, 0, 0] := by decide
  simp only [thetaVec, hk, hχ, Pi.zero_apply]
  fin_cases i <;> simp

theorem thetaFun_of_mem_A (hn : 3 ≤ n) {g : L4Model n} (hg : g ∈ A n) : thetaFun hn g = g := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [el_mem_A] at hg
  subst hg
  rw [thetaFun_el]
  exact el_congr _ _ (by rw [thetaVec_one, add_zero]) rfl

theorem thetaFun_uT (hn : 3 ≤ n) : thetaFun hn (uT (n := n) (by omega)) = uw1T hn := by
  rw [uT, thetaFun_el, uw1T, el_eq_el_iff (by omega)]
  refine ⟨rfl, ?_⟩
  have hk : thetaK s23 = 1 := by decide
  have hχ : thetaChi s23 = ![1, 0, 0, 0] := by decide
  have h2 := two_mul_hh (n := n) (by omega)
  refine isConst_of_forall_eq 0 fun i => ?_
  simp only [Pi.sub_apply, Pi.add_apply, thetaVec, hk, hχ, hv, Nat.cast_one, one_mul]
  linear_combination -(((![1, 0, 0, 0] : Fin 4 → ℕ) i : ℕ) : ZMod (2 ^ n)) * h2

theorem thetaFun_tT (hn : 3 ≤ n) : thetaFun hn (tT (n := n) (by omega)) = tT (by omega) := by
  rw [tT, thetaFun_el]
  have hk : thetaK tP = 0 := by decide
  have hχ : thetaChi tP = ![0, 0, 0, 0] := by decide
  refine el_congr _ _ ?_ rfl
  funext i
  simp only [Pi.add_apply, thetaVec, hk, hχ]
  fin_cases i <;> simp

@[expose] def thetaAut (hn : 3 ≤ n) : L4Model n ≃* L4Model n where
  toFun := thetaFun hn
  invFun := thetaFun hn
  left_inv := thetaFun_thetaFun hn
  right_inv := thetaFun_thetaFun hn
  map_mul' := thetaFun_mul hn

theorem thetaAut_apply (hn : 3 ≤ n) (g : L4Model n) : thetaAut hn g = thetaFun hn g := rfl

theorem thetaAut_of_mem_A (hn : 3 ≤ n) {g : L4Model n} (hg : g ∈ A n) : thetaAut hn g = g :=
  thetaFun_of_mem_A hn hg

theorem thetaAut_uT (hn : 3 ≤ n) : thetaAut hn (uT (n := n) (by omega)) = uw1T hn :=
  thetaFun_uT hn

theorem thetaAut_tT (hn : 3 ≤ n) : thetaAut hn (tT (n := n) (by omega)) = tT (by omega) :=
  thetaFun_tT hn

theorem thetaAut_uw1T (hn : 3 ≤ n) : thetaAut hn (uw1T hn) = uT (by omega) := by
  rw [← thetaAut_uT hn, thetaAut_apply, thetaAut_apply, thetaFun_thetaFun]

end CFSG.LocalAnalysis.Mason73
