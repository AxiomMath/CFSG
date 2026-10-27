module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutRoot
public import CFSG.ClassicalInvolution.Models.LinearFrames.Chart

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LinearAut

open Matrix.SpecialLinearGroup (transvection)
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] {n : ℕ}

@[expose] def pr (i j : Fin n) (hij : i ≠ j) : Pair n := ⟨{i, j}, Finset.card_pair hij⟩

theorem mem_pr {i j k : Fin n} (hij : i ≠ j) : k ∈ (pr i j hij).1 ↔ k = i ∨ k = j := by
  simp [pr]

theorem Lc_apply_of_not_mem (h2 : (2 : F) ≠ 0) {T : Pair n} {x : SL(n, F)} (hx : x ∈ Lc F T)
    {a b : Fin n} (hab : ¬ (a ∈ T.1 ∧ b ∈ T.1)) :
    (x : Matrix (Fin n) (Fin n) F) a b = if a = b then 1 else 0 := by
  obtain ⟨hcomm, hfix⟩ := mem_Lc.mp hx
  by_cases hb : b ∈ T.1
  · have ha : a ∉ T.1 := fun ha => hab ⟨ha, hb⟩
    have h1 := congrFun (congrFun hcomm a) b
    rw [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    simp only [ha, hb, ↓reduceIte] at h1
    have hne : a ≠ b := fun e => ha (e ▸ hb)
    have : (2 : F) * (x : Matrix (Fin n) (Fin n) F) a b = 0 := by linear_combination -h1
    simp only [hne, ↓reduceIte]
    exact (mul_eq_zero.mp this).resolve_left h2
  · have h1 := congrFun (congrFun hfix a) b
    rw [zMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.one_apply] at h1
    simp only [hb, ↓reduceIte, Matrix.diagonal_apply] at h1
    by_cases hab' : a = b
    · subst hab'
      simp only [↓reduceIte, hb] at h1 ⊢
      have : (2 : F) * (x : Matrix (Fin n) (Fin n) F) a a = 2 * 1 := by linear_combination h1
      exact mul_left_cancel₀ h2 this
    · simp only [hab', ↓reduceIte, add_zero] at h1 ⊢
      have : (2 : F) * (x : Matrix (Fin n) (Fin n) F) a b = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_left h2

theorem transvection_mem_Lc {i j : Fin n} (hij : i ≠ j) (s : F) :
    transvection hij s ∈ Lc F (pr i j hij) := by
  rw [mem_Lc, coe_transvection_eq hij]
  have hi : i ∈ (pr i j hij).1 := (mem_pr hij).2 (Or.inl rfl)
  have hj : j ∈ (pr i j hij).1 := (mem_pr hij).2 (Or.inr rfl)
  refine ⟨?_, ?_⟩
  · refine Matrix.ext fun a b => ?_
    simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    by_cases hc : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hc
      simp [hij, hi, hj]
    · by_cases hab : a = b
      · subst hab
        simp [hc]
      · simp [hc, hab]
  · refine Matrix.ext fun a b => ?_
    simp only [zMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply]
    by_cases hc : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hc
      simp [hij, hj]
    · by_cases hab : a = b
      · subst hab
        by_cases ha : a ∈ (pr i j hij).1 <;> simp [hc, ha]
      · simp [hc, hab]

theorem coe_zElt_conj (T : Pair n) (x : SL(n, F)) :
    ((zElt F T * x * (zElt F T)⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      zMat F n T.1 * (x : Matrix (Fin n) (Fin n) F) * zMat F n T.1 := by
  rw [inv_eq_of_mul_eq_one_right (zElt_mul_self T), Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_zElt]

theorem zElt_conj_transvection {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s : F) :
    zElt F (pr j k hjk) * transvection hij s * (zElt F (pr j k hjk))⁻¹ =
      transvection hij (-s) := by
  refine Subtype.ext ?_
  rw [coe_zElt_conj, coe_transvection_eq, coe_transvection_eq]
  refine Matrix.ext fun a b => ?_
  simp only [pr, zMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hc : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hc
    simp [hij, hik, hjk]
  · by_cases hab : a = b
    · subst hab
      by_cases ha : a = j ∨ a = k <;> simp [hc, ha]
    · simp [hc, hab]

theorem transvection_pow {i j : Fin n} (hij : i ≠ j) (c : F) (m : ℕ) :
    transvection hij c ^ m = transvection hij (m • c) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add, succ_nsmul]

theorem transvection_pow_ringChar {i j : Fin n} (hij : i ≠ j) (c : F) :
    transvection hij c ^ ringChar F = 1 := by
  rw [transvection_pow, nsmul_eq_mul, CharP.cast_eq_zero F (ringChar F), zero_mul,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

section Unipotent

variable [Finite F]

theorem trace_sub_one_of_pow_eq_one (hn : 0 < n) {g : SL(n, F)} (hg : g ^ ringChar F = 1) :
    Matrix.trace ((g : Matrix (Fin n) (Fin n) F) - 1) = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have hW : (g : Matrix (Fin n) (Fin n) F) ^ ringChar F = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hg, Matrix.SpecialLinearGroup.coe_one]
  have hM : ((g : Matrix (Fin n) (Fin n) F) - 1) ^ ringChar F = 0 := by
    rw [sub_pow_char_of_commute (ringChar F) (Commute.one_right _), hW, one_pow, sub_self]
  exact (Matrix.isNilpotent_trace_of_isNilpotent ⟨ringChar F, hM⟩).eq_zero

end Unipotent

theorem eq_transvection_of_block (h2 : (2 : F) ≠ 0) {i j : Fin n} (hij : i ≠ j) {w : SL(n, F)}
    (hw : w ∈ Lc F (pr i j hij)) (hii : (w : Matrix (Fin n) (Fin n) F) i i = 1)
    (hjj : (w : Matrix (Fin n) (Fin n) F) j j = 1) (hji : (w : Matrix (Fin n) (Fin n) F) j i = 0) :
    w = transvection hij ((w : Matrix (Fin n) (Fin n) F) i j) := by
  refine Subtype.ext (Matrix.ext fun x y => ?_)
  rw [coe_transvection_eq]
  by_cases hxy : x ∈ (pr i j hij).1 ∧ y ∈ (pr i j hij).1
  · obtain ⟨hx, hy⟩ := hxy
    rcases (mem_pr hij).1 hx with rfl | rfl <;> rcases (mem_pr hij).1 hy with rfl | rfl
    · simp [Matrix.add_apply, hii, hij.symm]
    · simp [Matrix.add_apply, hij]
    · simp [Matrix.add_apply, hji, hij, hij.symm]
    · simp [Matrix.add_apply, hjj, hij]
  · rw [Lc_apply_of_not_mem h2 hw hxy]
    have : ¬ (i = x ∧ j = y) := fun h => hxy ⟨h.1 ▸ (mem_pr hij).2 (Or.inl rfl),
      h.2 ▸ (mem_pr hij).2 (Or.inr rfl)⟩
    simp [Matrix.one_apply, this]

theorem eq_transvection_of_block' (h2 : (2 : F) ≠ 0) {i j : Fin n} (hij : i ≠ j) {w : SL(n, F)}
    (hw : w ∈ Lc F (pr i j hij)) (hii : (w : Matrix (Fin n) (Fin n) F) i i = 1)
    (hjj : (w : Matrix (Fin n) (Fin n) F) j j = 1) (hij0 : (w : Matrix (Fin n) (Fin n) F) i j = 0) :
    w = transvection hij.symm ((w : Matrix (Fin n) (Fin n) F) j i) := by
  refine Subtype.ext (Matrix.ext fun x y => ?_)
  rw [coe_transvection_eq]
  by_cases hxy : x ∈ (pr i j hij).1 ∧ y ∈ (pr i j hij).1
  · obtain ⟨hx, hy⟩ := hxy
    rcases (mem_pr hij).1 hx with rfl | rfl <;> rcases (mem_pr hij).1 hy with rfl | rfl
    · simp [Matrix.add_apply, hii, hij.symm]
    · simp [Matrix.add_apply, hij0, hij, hij.symm]
    · simp [Matrix.add_apply, hij.symm]
    · simp [Matrix.add_apply, hjj, hij]
  · rw [Lc_apply_of_not_mem h2 hw hxy]
    have : ¬ (j = x ∧ i = y) := fun h => hxy ⟨h.1 ▸ (mem_pr hij).2 (Or.inr rfl),
      h.2 ▸ (mem_pr hij).2 (Or.inl rfl)⟩
    simp [Matrix.one_apply, this]

section Image

variable [Finite F]

theorem exists_transvection_of_fixes_signs (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n)
    (α : SL(n, F) →* SL(n, F)) (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) {i j : Fin n} (hij : i ≠ j) (s : F) :
    (∃ b, α (transvection hij s) = transvection hij b) ∨
      ∃ c, α (transvection hij s) = transvection hij.symm c := by
  obtain ⟨k, hki, hkj⟩ := exists_third hn i j
  have hjk : j ≠ k := hkj.symm
  have hik : i ≠ k := hki.symm
  set w := α (transvection hij s) with hw
  have hwL : w ∈ Lc F (pr i j hij) := hL _ _ (transvection_mem_Lc hij s)
  have hwL' : w⁻¹ ∈ Lc F (pr i j hij) := inv_mem hwL
  have hconj : zElt F (pr j k hjk) * w * (zElt F (pr j k hjk))⁻¹ = w⁻¹ := by
    have h1 := congrArg α (zElt_conj_transvection hij hjk hik s)
    rw [map_mul, map_mul, map_inv, hz] at h1
    rw [← Matrix.SpecialLinearGroup.transvection_inv, map_inv] at h1
    exact h1
  set W : Matrix (Fin n) (Fin n) F := (w : Matrix (Fin n) (Fin n) F) with hWdef
  set W' : Matrix (Fin n) (Fin n) F := ((w⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) with hW'def
  have hWW : W * W' = 1 := by
    rw [hWdef, hW'def, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hconjM : zMat F n (pr j k hjk).1 * W * zMat F n (pr j k hjk).1 = W' := by
    have := congrArg Subtype.val hconj
    rwa [coe_zElt_conj] at this
  have hzi : (if i ∈ (pr j k hjk).1 then (-1 : F) else 1) = 1 := by
    have : i ∉ (pr j k hjk).1 := fun h => by
      rcases (mem_pr hjk).1 h with e | e
      · exact hij e
      · exact hik e
    simp [this]
  have hzj : (if j ∈ (pr j k hjk).1 then (-1 : F) else 1) = -1 := by
    have : j ∈ (pr j k hjk).1 := (mem_pr hjk).2 (Or.inl rfl)
    simp [this]
  have hentry : ∀ x y : Fin n, W' x y = (if x ∈ (pr j k hjk).1 then (-1 : F) else 1) * W x y *
      (if y ∈ (pr j k hjk).1 then (-1 : F) else 1) := by
    intro x y
    have := congrFun (congrFun hconjM x) y
    rw [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this.symm
  have hii' : W' i i = W i i := by rw [hentry, hzi]; ring
  have hij' : W' i j = - W i j := by rw [hentry, hzi, hzj]; ring
  have hji' : W' j i = - W j i := by rw [hentry, hzi, hzj]; ring
  have hjj' : W' j j = W j j := by rw [hentry, hzj]; ring
  have hbl : ∀ (M : SL(n, F)), M ∈ Lc F (pr i j hij) → ∀ c : Fin n, c ≠ i → c ≠ j →
      (M : Matrix (Fin n) (Fin n) F) i c = 0 ∧ (M : Matrix (Fin n) (Fin n) F) j c = 0 ∧
        (M : Matrix (Fin n) (Fin n) F) c i = 0 ∧ (M : Matrix (Fin n) (Fin n) F) c j = 0 := by
    intro M hM c hci hcj
    have hcT : c ∉ (pr i j hij).1 := fun h => by
      rcases (mem_pr hij).1 h with e | e
      · exact hci e
      · exact hcj e
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Lc_apply_of_not_mem h2 hM (fun h => hcT h.2)]
      simp [hci.symm]
    · rw [Lc_apply_of_not_mem h2 hM (fun h => hcT h.2)]
      simp [hcj.symm]
    · rw [Lc_apply_of_not_mem h2 hM (fun h => hcT h.1)]
      simp [hci]
    · rw [Lc_apply_of_not_mem h2 hM (fun h => hcT h.1)]
      simp [hcj]
  have hbW : ∀ c : Fin n, c ≠ i → c ≠ j → W i c = 0 ∧ W j c = 0 := fun c hci hcj =>
    ⟨(hbl w hwL c hci hcj).1, (hbl w hwL c hci hcj).2.1⟩
  have hsum : ∀ x y : Fin n, (x = i ∨ x = j) →
      (W * W') x y = W x i * W' i y + W x j * W' j y := by
    intro x y hx
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j hij]
    rintro c ⟨hci, hcj⟩
    rcases hx with rfl | rfl
    · rw [(hbW c hci hcj).1, zero_mul]
    · rw [(hbW c hci hcj).2, zero_mul]
  have hE1 : W i i * W i i + W i j * (- W j i) = 1 := by
    have h1 := hsum i i (Or.inl rfl)
    rw [hWW, hii', hji'] at h1
    simpa using h1.symm
  have hE2 : W j i * (- W i j) + W j j * W j j = 1 := by
    have h1 := hsum j j (Or.inr rfl)
    rw [hWW, hij', hjj'] at h1
    simpa using h1.symm
  have hp : w ^ ringChar F = 1 := by
    rw [hw, ← map_pow, transvection_pow_ringChar, map_one]
  have htr := trace_sub_one_of_pow_eq_one (by omega : 0 < n) hp
  have htr2 : (W i i - 1) + (W j j - 1) = 0 := by
    rw [← htr]
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.sub_apply, Matrix.one_apply_eq]
    rw [Fintype.sum_eq_add i j hij]
    rintro c ⟨hci, hcj⟩
    have hcT : c ∉ (pr i j hij).1 := fun h => by
      rcases (mem_pr hij).1 h with e | e
      · exact hci e
      · exact hcj e
    rw [Lc_apply_of_not_mem h2 hwL (fun h => hcT h.1)]
    simp
  have htr3 : W i i + W j j - 2 = 0 := by linear_combination htr2
  have had : W i i = W j j := by
    have h3 : (W i i - W j j) * 2 = 0 := by
      linear_combination (hE1 - hE2) - (W i i - W j j) * htr3
    have := (mul_eq_zero.mp h3).resolve_right h2
    exact sub_eq_zero.mp this
  have ha1 : W i i = 1 := by
    have h3 : (W i i - 1) * 2 = 0 := by linear_combination htr3 + had
    have := (mul_eq_zero.mp h3).resolve_right h2
    exact sub_eq_zero.mp this
  have hd1 : W j j = 1 := by rw [← had, ha1]
  have hbc : W i j * W j i = 0 := by
    rw [ha1] at hE1
    linear_combination -hE1
  rcases mul_eq_zero.mp hbc with hb0 | hc0
  · right
    exact ⟨W j i, eq_transvection_of_block' h2 hij hwL ha1 hd1 hb0⟩
  · left
    exact ⟨W i j, eq_transvection_of_block h2 hij hwL ha1 hd1 hc0⟩

end Image

end CFSG.ClassicalInvolution.ModelFacts.LinearAut
