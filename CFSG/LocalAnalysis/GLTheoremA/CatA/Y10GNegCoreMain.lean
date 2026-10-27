module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegMat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegCore

open Matrix CFSG.LocalAnalysis.GLTheoremA.SFM12

variable {F : Type} [Field F] [CharP F 2]

section Eigen

@[expose] def Pj (B : Matrix (Fin 6) (Fin 6) F) (ζ : F) (j : ℕ) : Matrix (Fin 6) (Fin 6) F :=
  ∑ k ∈ Finset.range 5, (ζ ^ (4 * j * k)) • (B ^ k)

theorem Pj_mulVec (B : Matrix (Fin 6) (Fin 6) F) (ζ : F) (j : ℕ) (v : Fin 6 → F) :
    Pj B ζ j *ᵥ v = pr B ζ j v := by
  unfold Pj pr
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]

theorem pr_fix {B : Matrix (Fin 6) (Fin 6) F} {ζ : F} (hζ5 : ζ ^ 5 = 1) (j : ℕ) {w : Fin 6 → F}
    (hw : B *ᵥ w = (ζ ^ j) • w) : pr B ζ j w = w := by
  have hk : ∀ k : ℕ, (B ^ k) *ᵥ w = ((ζ ^ j) ^ k) • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hw, smul_smul, ← pow_succ]
  unfold pr
  have hcoef : ∀ k ∈ Finset.range 5, (ζ ^ (4 * j * k)) • ((B ^ k) *ᵥ w) = w := by
    intro k _
    rw [hk k, smul_smul, ← pow_mul, mul_comm j k]
    have h1 : ζ ^ (4 * k * j) * ζ ^ (k * j) = 1 := by
      rw [← pow_add, show 4 * k * j + k * j = 5 * (k * j) by ring, pow_mul, hζ5, one_pow]
    rw [show 4 * j * k = 4 * k * j by ring, h1, one_smul]
  rw [Finset.sum_congr rfl hcoef]
  rw [Finset.sum_const, Finset.card_range]
  have h5 : (5 : ℕ) • w = w := by
    rw [← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, five_eq_one, one_smul]
  exact h5

theorem Pj_idem {B : Matrix (Fin 6) (Fin 6) F} {ζ : F} (hζ5 : ζ ^ 5 = 1) (hB5 : B ^ 5 = 1) (j : ℕ)
    (v : Fin 6 → F) : Pj B ζ j *ᵥ (Pj B ζ j *ᵥ v) = Pj B ζ j *ᵥ v := by
  rw [Pj_mulVec, Pj_mulVec]
  exact pr_fix hζ5 j (pr_eigen B hζ5 hB5 j v)

theorem Pj_selfadj {B : Matrix (Fin 6) (Fin 6) F} {ζ : F} (hU : (B.map (fun x : F => x ^ 4))ᵀ * B = 1)
    (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (hB5 : B ^ 5 = 1) (j : ℕ) (hj : j < 5) (a b : Fin 6 → F) :
    herm (Pj B ζ j *ᵥ a) b = herm a (Pj B ζ j *ᵥ b) := by
  have hcross : ∀ m ∈ Finset.range 5, m ≠ j → ∀ x y : Fin 6 → F, herm (pr B ζ j x) (pr B ζ m y) = 0 := by
    intro m hm hmj x y
    have hm5 : m < 5 := Finset.mem_range.1 hm
    refine herm_eigen_zeta hU hζ5 hζ1 ?_ (pr_eigen B hζ5 hB5 j x) (pr_eigen B hζ5 hB5 m y)
    omega
  have hcross' : ∀ m ∈ Finset.range 5, m ≠ j → ∀ x y : Fin 6 → F, herm (pr B ζ m x) (pr B ζ j y) = 0 := by
    intro m hm hmj x y
    have hm5 : m < 5 := Finset.mem_range.1 hm
    refine herm_eigen_zeta hU hζ5 hζ1 ?_ (pr_eigen B hζ5 hB5 m x) (pr_eigen B hζ5 hB5 j y)
    omega
  have hj' : j ∈ Finset.range 5 := Finset.mem_range.2 hj
  rw [Pj_mulVec, Pj_mulVec]
  have hbexp : herm (pr B ζ j a) b = herm (pr B ζ j a) (pr B ζ j b) := by
    conv_lhs => rw [← pr_sum B hζ5 hζ1 b]
    rw [herm_sum_right, Finset.sum_eq_single j]
    · intro m hm hmj
      exact hcross m hm hmj a b
    · intro h
      exact absurd hj' h
  have haexp : herm a (pr B ζ j b) = herm (pr B ζ j a) (pr B ζ j b) := by
    conv_lhs => rw [← pr_sum B hζ5 hζ1 a]
    rw [herm_sum_left, Finset.sum_eq_single j]
    · intro m hm hmj
      exact hcross' m hm hmj a b
    · intro h
      exact absurd hj' h
  rw [hbexp, haexp]

theorem Pj_comm {B Y : Matrix (Fin 6) (Fin 6) F} (hYB : Commute Y B) (ζ : F) (j : ℕ) :
    Commute Y (Pj B ζ j) := by
  unfold Pj
  refine Commute.sum_right _ _ _ fun k _ => ?_
  exact Commute.smul_right (hYB.pow_right k) _

theorem Pj_exists_ne {B : Matrix (Fin 6) (Fin 6) F} {ζ : F} (hζ5 : ζ ^ 5 = 1)
    (hB5 : B ^ 5 = 1) (hBns : ¬ ∃ c : F, B = c • 1) (j : ℕ) :
    ∃ t : Fin 6 → F, t ≠ 0 ∧ Pj B ζ j *ᵥ t = 0 := by
  have hnot : ∃ v : Fin 6 → F, Pj B ζ j *ᵥ v ≠ v := by
    by_contra hcon
    apply hBns
    have hfix : ∀ v : Fin 6 → F, Pj B ζ j *ᵥ v = v := fun v => by
      by_contra hne
      exact hcon ⟨v, hne⟩
    refine ⟨ζ ^ j, Matrix.ext_iff_mulVec.2 fun v => ?_⟩
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 := pr_eigen B hζ5 hB5 j v
    rw [← Pj_mulVec, hfix v] at h1
    exact h1
  obtain ⟨v, hv⟩ := hnot
  refine ⟨v - Pj B ζ j *ᵥ v, ?_, ?_⟩
  · intro h
    exact hv (sub_eq_zero.1 h).symm
  · rw [Matrix.mulVec_sub, Pj_idem hζ5 hB5 j v, sub_self]

end Eigen

section KeyLemma

theorem isometry_pow {Y : Matrix (Fin 6) (Fin 6) F}
    (hY : ∀ a b : Fin 6 → F, herm (Y *ᵥ a) (Y *ᵥ b) = herm a b) (k : ℕ) (a b : Fin 6 → F) :
    herm ((Y ^ k) *ᵥ a) ((Y ^ k) *ᵥ b) = herm a b := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hY, ih]

theorem key_lemma {Y P : Matrix (Fin 6) (Fin 6) F} (hF16 : ∀ x : F, x ^ 16 = x)
    (hf3 : ∀ x : F, x ^ 3 + x + 1 ≠ 0)
    (hY : ∀ a b : Fin 6 → F, herm (Y *ᵥ a) (Y *ᵥ b) = herm a b) (hY7 : Y ^ 7 = 1)
    (hYP : Commute Y P) (hPs : ∀ a b : Fin 6 → F, herm (P *ᵥ a) b = herm a (P *ᵥ b))
    (hP2 : ∀ v : Fin 6 → F, P *ᵥ (P *ᵥ v) = P *ᵥ v)
    {t : Fin 6 → F} (ht0 : t ≠ 0) (hPt : P *ᵥ t = 0) (v : Fin 6 → F) :
    Y *ᵥ (P *ᵥ v) = P *ᵥ v := by
  set x : Fin 6 → F := P *ᵥ v
  have hx : P *ᵥ x = x := hP2 v
  have hPY : ∀ w : Fin 6 → F, P *ᵥ (Y *ᵥ w) = Y *ᵥ (P *ᵥ w) := fun w => mulVec_mulVec_comm hYP.symm w
  set z : Fin 6 → F := (Y + 1) *ᵥ x with hzdef
  have hPz : P *ᵥ z = z := by
    rw [hzdef, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, hPY, hx]
  have hcomm_q : Commute P (Y ^ 3 + Y ^ 2 + 1) :=
    ((hYP.symm.pow_right 3).add_right (hYP.symm.pow_right 2)).add_right (Commute.one_right P)
  have hPq : ∀ w : Fin 6 → F, P *ᵥ ((Y ^ 3 + Y ^ 2 + 1) *ᵥ w) = (Y ^ 3 + Y ^ 2 + 1) *ᵥ (P *ᵥ w) :=
    fun w => mulVec_mulVec_comm hcomm_q w
  set z' : Fin 6 → F := (Y ^ 3 + Y ^ 2 + 1) *ᵥ z with hz'def
  have hPz' : P *ᵥ z' = z' := by
    rw [hz'def, hPq, hPz]
  have hfz' : (Y ^ 3 + Y + 1) *ᵥ z' = 0 := by
    rw [hz'def, hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, matI1 hY7, Matrix.zero_mulVec]
  have hz'0 : z' = 0 := fixed_no_kernel hF16 hf3 hY hY7 hYP.symm hPs ht0 hPt hPz' hfz'
  have hfz6 : ((Y ^ 6) ^ 3 + Y ^ 6 + 1) *ᵥ z = 0 := by
    rw [matI3 hY7, ← Matrix.mulVec_mulVec, ← hz'def, hz'0, Matrix.mulVec_zero]
  have hZ7 : (Y ^ 6) ^ 7 = 1 := by
    rw [← pow_mul, show 6 * 7 = 7 * 6 by norm_num, pow_mul, hY7, one_pow]
  have hz0 : z = 0 :=
    fixed_no_kernel hF16 hf3 (isometry_pow hY 6) hZ7 (hYP.symm.pow_right 6) hPs ht0 hPt hPz hfz6
  rw [hzdef, Matrix.add_mulVec, Matrix.one_mulVec] at hz0
  have hxx : x + x = 0 := by
    rw [← two_smul F x, two_eq_zero' (F := F), zero_smul]
  calc Y *ᵥ x = Y *ᵥ x + (x + x) := by rw [hxx, add_zero]
    _ = (Y *ᵥ x + x) + x := by abel
    _ = x := by rw [hz0, zero_add]

end KeyLemma

section Conclusion

theorem matrix_eq_one_of_isometry [Finite F] {B Y : Matrix (Fin 6) (Fin 6) F} (hF : Nat.card F = 16)
    (hF16 : ∀ x : F, x ^ 16 = x)
    (hU : (B.map (fun x : F => x ^ 4))ᵀ * B = 1) (hB5 : B ^ 5 = 1) (hBns : ¬ ∃ c : F, B = c • 1)
    (hY : ∀ a b : Fin 6 → F, herm (Y *ᵥ a) (Y *ᵥ b) = herm a b) (hY7 : Y ^ 7 = 1)
    (hYB : Commute Y B) : Y = 1 := by
  obtain ⟨ζ, hζ5, hζ1⟩ := exists_zeta hF
  have hf3 : ∀ x : F, x ^ 3 + x + 1 ≠ 0 := fun x => root_free_f hF x
  have hkey : ∀ j, j < 5 → ∀ v : Fin 6 → F, Y *ᵥ (Pj B ζ j *ᵥ v) = Pj B ζ j *ᵥ v := by
    intro j hj v
    obtain ⟨t, ht0, hPt⟩ := Pj_exists_ne (ζ := ζ) hζ5 hB5 hBns j
    exact key_lemma hF16 hf3 hY hY7 (Pj_comm hYB ζ j) (Pj_selfadj hU hζ5 hζ1 hB5 j hj)
      (Pj_idem hζ5 hB5 j) ht0 hPt v
  have hsum : ∀ v : Fin 6 → F, Y *ᵥ v = v := by
    intro v
    have hv : ∑ j ∈ Finset.range 5, Pj B ζ j *ᵥ v = v := by
      simp only [Pj_mulVec]
      exact pr_sum B hζ5 hζ1 v
    calc Y *ᵥ v = Y *ᵥ (∑ j ∈ Finset.range 5, Pj B ζ j *ᵥ v) := by rw [hv]
      _ = ∑ j ∈ Finset.range 5, Y *ᵥ (Pj B ζ j *ᵥ v) := Matrix.mulVec_sum _ _ _
      _ = ∑ j ∈ Finset.range 5, Pj B ζ j *ᵥ v :=
          Finset.sum_congr rfl fun j hj => hkey j (Finset.mem_range.1 hj) v
      _ = v := hv
  exact Matrix.ext_iff_mulVec.2 fun v => by rw [Matrix.one_mulVec]; exact hsum v

end Conclusion

theorem U6Core_holds : CFSG.LocalAnalysis.GLTheoremA.Y10GNeg.U6Core := by
  intro F _ _ _ _ hF B hB hB5 hBns y hy hyo hcomm
  have hF' : Nat.card F = 16 := by rw [hF]; norm_num
  have hmem := (mem_SU_iff hF y).1 hy
  have hYU : ((y : Matrix (Fin 6) (Fin 6) F).map (fun x : F => x ^ 4))ᵀ * (y : Matrix (Fin 6) (Fin 6) F) = 1 := by
    have h2 := hmem.2
    rw [map_frob4] at h2
    exact h2
  have hY := herm_unitary hYU
  have hy7 : y ^ 7 = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  have hY7 : (y : Matrix (Fin 6) (Fin 6) F) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy7, Units.val_one]
  have hB5' : (B : Matrix (Fin 6) (Fin 6) F) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hB5, Units.val_one]
  have hYB : Commute (y : Matrix (Fin 6) (Fin 6) F) (B : Matrix (Fin 6) (Fin 6) F) := by
    have h := congrArg Units.val hcomm
    rw [Units.val_mul, Units.val_mul] at h
    exact h.symm
  have hY1 := matrix_eq_one_of_isometry hF' (fun x => pow16_eq hF' x) hB hB5' hBns hY hY7 hYB
  have hy1 : y = 1 := Units.ext (by rw [Units.val_one]; exact hY1)
  rw [hy1, orderOf_one] at hyo
  norm_num at hyo

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegCore

