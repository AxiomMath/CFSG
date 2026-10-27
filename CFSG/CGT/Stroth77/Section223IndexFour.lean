module

public import CFSG.CGT.Stroth77.Extension210Four

public section

namespace CFSG.CGT.Stroth77

section Coordinates

variable {m : ℕ}

theorem rho_apply_gens_t200 (i j l : ℤ) :
    (StrothTypeIndex.t200 m).action.φρ
        (i • gen (StrothTypeIndex.t200 m).k 0 + j • gen (StrothTypeIndex.t200 m).k 1 +
          l • gen (StrothTypeIndex.t200 m).k 2) =
      (i - l) • gen (StrothTypeIndex.t200 m).k 0 +
        (-l) • gen (StrothTypeIndex.t200 m).k 1 +
          (j - l) • gen (StrothTypeIndex.t200 m).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type200.action, SigmaFourAction.ofMatEq, Type200.ρM, ofCols_apply,
    sub_eq_add_neg]

theorem rho_apply_gens_t201 (i j l : ℤ) :
    (StrothTypeIndex.t201 m).action.φρ
        (i • gen (StrothTypeIndex.t201 m).k 0 + j • gen (StrothTypeIndex.t201 m).k 1 +
          l • gen (StrothTypeIndex.t201 m).k 2) =
      (i - l) • gen (StrothTypeIndex.t201 m).k 0 +
        (-l) • gen (StrothTypeIndex.t201 m).k 1 +
          (j - l) • gen (StrothTypeIndex.t201 m).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type201.action, SigmaFourAction.ofMatEq, Type201.ρM, ofCols_apply,
    sub_eq_add_neg]

theorem rho_apply_gens_t220 {s : ℕ} (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t220 s hs).action.φρ
        (i • gen (StrothTypeIndex.t220 s hs).k 0 + j • gen (StrothTypeIndex.t220 s hs).k 1 +
          l • gen (StrothTypeIndex.t220 s hs).k 2) =
      (i - l) • gen (StrothTypeIndex.t220 s hs).k 0 +
        (-l) • gen (StrothTypeIndex.t220 s hs).k 1 +
          (j - l) • gen (StrothTypeIndex.t220 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type220.actionPaper, Type220.action, SigmaFourAction.ofMatEq,
    Type220.ρM, ofCols_apply, sub_eq_add_neg]

theorem t_apply_gens_t200 (i j l : ℤ) :
    (StrothTypeIndex.t200 m).action.φt
        (i • gen (StrothTypeIndex.t200 m).k 0 + j • gen (StrothTypeIndex.t200 m).k 1 +
          l • gen (StrothTypeIndex.t200 m).k 2) =
      (i - l) • gen (StrothTypeIndex.t200 m).k 0 +
        (4 * i - j - 2 * l) • gen (StrothTypeIndex.t200 m).k 1 +
          (-l) • gen (StrothTypeIndex.t200 m).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type200.action, SigmaFourAction.ofMatEq, Type200.tM,
    Type200.uvA, Type200.ρM, ofCols_apply]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;> congr 1 <;>
    simp [-mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

theorem t_apply_gens_t201 (i j l : ℤ) :
    (StrothTypeIndex.t201 m).action.φt
        (i • gen (StrothTypeIndex.t201 m).k 0 + j • gen (StrothTypeIndex.t201 m).k 1 +
          l • gen (StrothTypeIndex.t201 m).k 2) =
      (i + (-1 - 2 ^ (m + 1)) * l) • gen (StrothTypeIndex.t201 m).k 0 +
        (4 * i + (-1 + 2 ^ (m + 1)) * j + (-2 - 2 ^ (m + 1)) * l) •
          gen (StrothTypeIndex.t201 m).k 1 +
        ((-1 - 2 ^ (m + 1)) * l) • gen (StrothTypeIndex.t201 m).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type201.action, SigmaFourAction.ofMatEq, Type201.tM,
    Type201.uvA, Type201.ρM, ofCols_apply]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;> congr 1 <;>
    simp [-mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

theorem t_apply_gens_t220 {s : ℕ} (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t220 s hs).action.φt
        (i • gen (StrothTypeIndex.t220 s hs).k 0 + j • gen (StrothTypeIndex.t220 s hs).k 1 +
          l • gen (StrothTypeIndex.t220 s hs).k 2) =
      ((4 - Type120.iV (s + 4)) * i + 2 * Type120.GV (s + 4) * Type120.iV (s + 4) * j +
          (Type120.FV (s + 4) * Type120.iV (s + 4) - 2 * Type120.iV (s + 4)) * l) •
          gen (StrothTypeIndex.t220 s hs).k 0 +
        (4 * i - 7 * Type120.iV (s + 4) * j - 2 * Type120.iV (s + 4) * l) •
          gen (StrothTypeIndex.t220 s hs).k 1 +
        (8 * i - 8 * Type120.iV (s + 4) * j - 7 * Type120.iV (s + 4) * l) •
          gen (StrothTypeIndex.t220 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type220.actionPaper, Type220.action, SigmaFourAction.ofMatEq,
    Type220.tM, Type220.uvA, Type220.ρM, ofCols_apply]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;> congr 1 <;>
    simp [-mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

theorem parityTorus_rho_t200 (hk : ∀ i, 1 ≤ (StrothTypeIndex.t200 m).k i)
    (y : Torus (StrothTypeIndex.t200 m).k) :
    parityTorus _ hk ((StrothTypeIndex.t200 m).action.φρ y) = rhoBar230 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t200, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_rho_t201 (hk : ∀ i, 1 ≤ (StrothTypeIndex.t201 m).k i)
    (y : Torus (StrothTypeIndex.t201 m).k) :
    parityTorus _ hk ((StrothTypeIndex.t201 m).action.φρ y) = rhoBar230 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t201, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_rho_t220 {s : ℕ} (hs : 1 ≤ s)
    (hk : ∀ i, 1 ≤ (StrothTypeIndex.t220 s hs).k i) (y : Torus (StrothTypeIndex.t220 s hs).k) :
    parityTorus _ hk ((StrothTypeIndex.t220 s hs).action.φρ y) =
      rhoBar230 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t220, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t200 (hk : ∀ i, 1 ≤ (StrothTypeIndex.t200 m).k i)
    (y : Torus (StrothTypeIndex.t200 m).k) :
    parityTorus _ hk ((StrothTypeIndex.t200 m).action.φt y) = tBar230 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t200, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [tBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, h2, h4, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t201 (hk : ∀ i, 1 ≤ (StrothTypeIndex.t201 m).k i)
    (y : Torus (StrothTypeIndex.t201 m).k) :
    parityTorus _ hk ((StrothTypeIndex.t201 m).action.φt y) = tBar230 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t201, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h2m : (2 : ZMod 2) ^ (m + 1) = 0 := by rw [h2, zero_pow (Nat.succ_ne_zero m)]
  funext r
  fin_cases r
  · simp [tBar230, h2m, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, h2, h4, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, h2m, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t220 {s : ℕ} (hs : 1 ≤ s)
    (hk : ∀ i, 1 ≤ (StrothTypeIndex.t220 s hs).k i) (y : Torus (StrothTypeIndex.t220 s hs).k) :
    parityTorus _ hk ((StrothTypeIndex.t220 s hs).action.φt y) =
      tBar230 (parityTorus _ hk y) := by
  obtain ⟨hI, hF, hG⟩ := odd_iV_FV_GV_t230 s
  have hI2 : ((Type120.iV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hI
  have hF2 : ((Type120.FV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hF
  have hG2 : ((Type120.GV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hG
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t220, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h7 : (7 : ZMod 2) = 1 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [tBar230, hI2, hF2, hG2, h2, h4, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, hI2, h2, h4, h7, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, hI2, h7, h8, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

end Coordinates

section Fixed

variable {S : Type*} [Group S] [Finite S] {B : Subgroup S} {m : ℕ}

theorem fixed_rho_t_t200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t200 m).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t200 m).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t200 m).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t200 m).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t200] at hρ'
  rw [hy, t_apply_gens_t200] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (m + 2) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (m + 2)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (m + 2) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (m + 2) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (m + 2) ∣ 4 * i := by
    have := dvd_sub (dvd_add (dvd_mul_of_dvd_right hj 2) (dvd_mul_of_dvd_right hl 2)) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ m ∣ i := by
    have h16 : (2 : ℤ) ^ (m + 2) = 4 * 2 ^ m := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t200 m).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ m ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

theorem fixed_rho_t_t201 (D : StrothTypeData B (StrothTypeIndex.t201 m)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t201 m).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t201 m).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t201 m).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t201 m).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t201] at hρ'
  rw [hy, t_apply_gens_t201] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (m + 2) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (m + 2)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (m + 2) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (m + 2) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (m + 2) ∣ 4 * i := by
    have := dvd_sub (dvd_add (dvd_mul_of_dvd_right hj (2 - 2 ^ (m + 1)))
      (dvd_mul_of_dvd_right hl (2 + 2 ^ (m + 1)))) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ m ∣ i := by
    have h16 : (2 : ℤ) ^ (m + 2) = 4 * 2 ^ m := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t201 m).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ m ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

theorem fixed_rho_t_t220 {s : ℕ} {hs : 1 ≤ s} (D : StrothTypeData B (StrothTypeIndex.t220 s hs))
    {y : B} (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t220 s hs).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t220 s hs).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t220 s hs).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t220 s hs).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t220] at hρ'
  rw [hy, t_apply_gens_t220] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (s + 4) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (s + 4)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (s + 4) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (s + 4) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (s + 4) ∣ 4 * i := by
    have := dvd_sub (dvd_add (dvd_mul_of_dvd_right hj (1 + 7 * Type120.iV (s + 4)))
      (dvd_mul_of_dvd_right hl (2 * Type120.iV (s + 4)))) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ (s + 2) ∣ i := by
    have h16 : (2 : ℤ) ^ (s + 4) = 4 * 2 ^ (s + 2) := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t220 s hs).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ (s + 2) ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

end Fixed

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem false_of_index_four_t200_of_data {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t200 m))
    (hk : ∀ i, 1 ≤ (StrothTypeIndex.t200 m).k i) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hexp : ∀ x ∈ C, x * x ∈ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  exact false_of_index_four_of_planes_t230 D hk (parityTorus_rho_t200 hk) (parityTorus_t_t200 hk)
    (fun _ hρ ht => fixed_rho_t_t200 D hρ ht) hBC hC hrel hL hH hcS
    (not_isCyclic_quotient_of_sq_mem_Idx4R hBC hC hrel hexp)

theorem false_of_index_four_t201_of_data {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t201 m))
    (hk : ∀ i, 1 ≤ (StrothTypeIndex.t201 m).k i) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hexp : ∀ x ∈ C, x * x ∈ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  exact false_of_index_four_of_planes_t230 D hk (parityTorus_rho_t201 hk) (parityTorus_t_t201 hk)
    (fun _ hρ ht => fixed_rho_t_t201 D hρ ht) hBC hC hrel hL hH hcS
    (not_isCyclic_quotient_of_sq_mem_Idx4R hBC hC hrel hexp)

theorem false_of_index_four_t220_of_data {s : ℕ} {hs : 1 ≤ s}
    (D : StrothTypeData B (StrothTypeIndex.t220 s hs))
    (hk : ∀ i, 1 ≤ (StrothTypeIndex.t220 s hs).k i) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hexp : ∀ x ∈ C, x * x ∈ B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  exact false_of_index_four_of_planes_t230 D hk (parityTorus_rho_t220 hs hk)
    (parityTorus_t_t220 hs hk) (fun _ hρ ht => fixed_rho_t_t220 D hρ ht) hBC hC hrel hL hH hcS
    (not_isCyclic_quotient_of_sq_mem_Idx4R hBC hC hrel hexp)

end CFSG.CGT.Stroth77
