module

import all CFSG.Fischer.F4
public import CFSG.LargeExtraspecial.Asc611IFrameB
public import CFSG.LargeExtraspecial.Asc611IMatF4
public import CFSG.LargeExtraspecial.Asc611IRange

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m} {r : ℕ} {q : Fin r → Fin m → K}

theorem IsFrame.snoc (he : e * e = 1) (F : IsFrame e q) {z : Fin m → K}
    (hz : herm frob z (invN e z) = 1) (hqz : ∀ i, herm frob (q i) (invN e z) = 0)
    (hzz : herm frob z z = 0) (hqz' : ∀ i, herm frob (q i) z = 0) :
    IsFrame e (Fin.snoc q z : Fin (r + 1) → Fin m → K) where
  orth i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, ite_eq_left rfl]; exact hz
      | cast j =>
        rw [Fin.snoc_last, Fin.snoc_castSucc, herm_invN_swap he, hqz, map_zero,
          ite_eq_right (Fin.castSucc_ne_last j).symm]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_castSucc, hqz, ite_eq_right (Fin.castSucc_ne_last i)]
      | cast j => simp only [Fin.snoc_castSucc, F.orth, Fin.castSucc_inj]
  iso i j := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hzz
      | cast j => rw [Fin.snoc_last, Fin.snoc_castSucc, herm_eq_zero_comm frob frob_frob (hqz' j)]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_castSucc, hqz']
      | cast j => simp only [Fin.snoc_castSucc, F.iso]

theorem isFrame_two (he : e * e = 1) {q₀ q₁ : Fin m → K} (h0 : herm frob q₀ (invN e q₀) = 1)
    (h1 : herm frob q₁ (invN e q₁) = 1) (h01 : herm frob q₀ (invN e q₁) = 0)
    (i0 : herm frob q₀ q₀ = 0) (i1 : herm frob q₁ q₁ = 0) (i01 : herm frob q₀ q₁ = 0) :
    IsFrame e ![q₀, q₁] where
  orth i j := by
    have h10 : herm frob q₁ (invN e q₀) = 0 := by rw [herm_invN_swap he, h01, map_zero]
    fin_cases i <;> fin_cases j
    · exact h0
    · exact h01
    · exact h10
    · exact h1
  iso i j := by
    have i10 : herm frob q₁ q₀ = 0 := herm_eq_zero_comm frob frob_frob i01
    fin_cases i <;> fin_cases j
    · exact i0
    · exact i01
    · exact i10
    · exact i1

theorem frameMap_snoc {z : Fin m → K} {M : Matrix (Fin r) (Fin r) K}
    {M' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hM : ∀ i j, M' (Fin.castSucc i) (Fin.castSucc j) = M i j)
    (hl : ∀ j, M' (Fin.last r) j = 0) (hr : ∀ i, M' i (Fin.last r) = 0) (x : Fin m → K) :
    frameMap e (Fin.snoc q z : Fin (r + 1) → Fin m → K) M' x = frameMap e q M x := by
  unfold frameMap
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, hM, hl, hr, zero_mul, zero_smul,
    Finset.sum_const_zero, add_zero]

theorem hpF_snoc (hr : 2 ≤ r) :
    (∀ i j : Fin r, ((hpF (r + 1)).map eF4) (Fin.castSucc i) (Fin.castSucc j) =
      ((hpF r).map eF4) i j) ∧ (∀ j, ((hpF (r + 1)).map eF4) (Fin.last r) j = 0) ∧
      ∀ i, ((hpF (r + 1)).map eF4) i (Fin.last r) = 0 := by
  refine ⟨fun i j => ?_, fun j => ?_, fun i => ?_⟩
  · simp only [Matrix.map_apply, hpF, Fin.castSucc_inj, Fin.val_castSucc]
  · simp only [Matrix.map_apply, hpF, Fin.val_last]
    rw [ite_eq_right (by omega), map_zero]
  · simp only [Matrix.map_apply, hpF]
    rw [ite_eq_right (fun h => by have := h.2; rw [h.1, Fin.val_last] at this; omega),
      map_zero]

theorem m0F_snoc (hr : 2 ≤ r) :
    (∀ i j : Fin r, ((m0F (r + 1)).map eF4) (Fin.castSucc i) (Fin.castSucc j) =
      ((m0F r).map eF4) i j) ∧ (∀ j, ((m0F (r + 1)).map eF4) (Fin.last r) j = 0) ∧
      ∀ i, ((m0F (r + 1)).map eF4) i (Fin.last r) = 0 := by
  refine ⟨fun i j => ?_, fun j => ?_, fun i => ?_⟩
  · simp only [Matrix.map_apply, m0F, Fin.val_castSucc]
  · simp only [Matrix.map_apply, m0F, Fin.val_last]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), map_zero]
  · simp only [Matrix.map_apply, m0F, Fin.val_last]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), map_zero]

theorem eF4_wF : eF4 wF = ω := rfl

theorem eF4_w2F : eF4 w2F = ω * ω := by
  rw [show w2F = F4.ω * F4.ω by decide, map_mul]
  rfl

theorem frameMap_hp2 {q₀ q₁ : Fin m → K} (x : Fin m → K) :
    frameMap e ![q₀, q₁] ((hpF 2).map eF4) x =
      herm frob (invN e q₀) x • invN e q₀ + herm frob (invN e q₁) x • invN e q₁ := by
  unfold frameMap
  simp only [Fin.sum_univ_two, Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show hpF 2 0 0 = 1 by decide, show hpF 2 0 1 = 0 by decide, show hpF 2 1 0 = 0 by decide,
    show hpF 2 1 1 = 1 by decide]
  simp only [map_one, map_zero, one_mul, zero_mul, zero_smul, add_zero, zero_add]

theorem frameMap_m02 {q₀ q₁ : Fin m → K} (x : Fin m → K) :
    frameMap e ![q₀, q₁] ((m0F 2).map eF4) x =
      (ω * ω * herm frob (invN e q₀) x) • invN e q₁ +
        (ω * herm frob (invN e q₁) x) • invN e q₀ := by
  unfold frameMap
  simp only [Fin.sum_univ_two, Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show m0F 2 0 0 = 0 by decide, show m0F 2 0 1 = w2F by decide,
    show m0F 2 1 0 = wF by decide, show m0F 2 1 1 = 0 by decide, eF4_w2F, eF4_wF]
  simp only [map_zero, zero_mul, zero_smul, add_zero, zero_add]

theorem actsBy_of_maximal (he : e * e = 1) (F : IsFrame e q)
    (hno : ∀ z, (∀ i, herm frob (q i) (invN e z) = 0) → herm frob z (invN e z) = 0)
    {g : SUid frob m} (hker : ∀ v, invN e v = 0 → g • v = v)
    (hperp : ∀ x b, invN e b = 0 → herm frob (g • x + x) b = 0) :
    ActsBy e q (fun j i => herm frob (q i) (g • q j + q j)) g := by
  have hS : ∀ x, g • x + x = ∑ l, herm frob (q l) (g • x + x) • invN e (q l) := by
    intro x
    obtain ⟨c, hc⟩ := exists_invN_eq_of_perp he (hperp x)
    have h1 := invN_eq_sum_of_frame he F hno c
    rw [hc] at h1
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h1, F.herm_q_sum]
  intro x
  set v := x + ∑ j, herm frob (invN e (q j)) x • q j with hv
  have hv0 : invN e v = 0 := by
    rw [hv, invN_add, invN_sum]
    simp only [invN_smul]
    rw [← invN_eq_sum_of_frame he F hno x, vec_add_self]
  have hx : x = v + ∑ j, herm frob (invN e (q j)) x • q j := by
    rw [hv, add_assoc, vec_add_self, add_zero]
  have hgx : g • x + x = ∑ j, herm frob (invN e (q j)) x • (g • q j + q j) := by
    conv_lhs => rw [hx]
    rw [smul_add, hker v hv0, Finset.smul_sum]
    simp only [smul_comm g]
    rw [show v + ∑ j, herm frob (invN e (q j)) x • g • q j +
          (v + ∑ j, herm frob (invN e (q j)) x • q j) =
        (v + v) + ∑ j, (herm frob (invN e (q j)) x • g • q j +
          herm frob (invN e (q j)) x • q j) by
      rw [Finset.sum_add_distrib]; abel, vec_add_self, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_add]
  have hgx' : g • x = x + (g • x + x) := by rw [add_comm x, add_assoc, vec_add_self, add_zero]
  rw [hgx', hgx]
  congr 1
  unfold frameMap
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hS (q j), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

end CFSG.LargeExtraspecial.Asc611I
