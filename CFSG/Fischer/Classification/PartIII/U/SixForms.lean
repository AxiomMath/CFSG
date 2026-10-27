module

public import CFSG.Fischer.Classification.PartIII.U.MinusFive

public section

namespace CFSG.Fischer.Classification.LocalU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification LocalR3 F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem NormOneCompl.of_isometry {f' : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) (he : ∀ x y, f x y = f' (e x) (e y))
    (h : NormOneCompl f') : NormOneCompl f := by
  intro w w' z hw hw' hww' hz0 hzz hzw hzw'
  rw [he] at hw hw' hww' hzz hzw hzw'
  obtain ⟨y, hyy, hyw, hyw', hyz⟩ := h (e w) (e w') (e z) hw hw' hww'
    ((LinearEquiv.map_ne_zero_iff e).2 hz0) hzz hzw hzw'
  refine ⟨e.symm y, ?_, ?_, ?_, ?_⟩ <;> rw [he, e.apply_symm_apply]
  exacts [hyy, hyw, hyw', hyz]

theorem prod_diagF3Entry {n : ℕ} (hn : 1 ≤ n) (δ : ZMod 3) : ∏ i, diagF3Entry n δ i = δ := by
  rw [Finset.prod_eq_single (⟨n - 1, by omega⟩ : Fin n) (fun i _ hi => ?_)
    (fun h => absurd (Finset.mem_univ _) h)]
  · have h : n - 1 + 1 = n := by omega
    simp [diagF3Entry, h]
  · have h : (i : ℕ) + 1 ≠ n := fun h => hi (Fin.ext (by simp only; omega))
    simp [diagF3Entry, h]

theorem diagF3_single {n : ℕ} (δ : ZMod 3) (i j : Fin n) :
    diagF3 n δ (Pi.single i 1) (Pi.single j 1) = if i = j then diagF3Entry n δ i else 0 := by
  rw [diagF3_apply]
  by_cases hij : i = j
  · subst hij
    simp [Pi.single_apply]
  · simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, hij]
    exact Finset.sum_eq_zero fun k _ => by
      by_cases hk : k = i
      · subst hk; simp [hij]
      · simp [hk]

theorem sq_eq_one_of_ne_zero {a : ZMod 3} (ha : a ≠ 0) : a ^ 2 = 1 := by
  rw [sq]
  exact mul_self_of_ne_zero ha

theorem exists_isometry_restrict_diagF3 {n : ℕ} (hn : 1 ≤ n) {δ : ZMod 3} (hδ : δ ≠ 0)
    {v : Fin (n + 1) → ZMod 3} (hv : diagF3 (n + 1) δ v v = 1)
    {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)} (hf' : IsF3Form f')
    (e : perpOne (diagF3 (n + 1) δ) v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (he : ∀ a b : perpOne (diagF3 (n + 1) δ) v, f' (e a) (e b) = diagF3 (n + 1) δ a b) :
    ∃ e' : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3), ∀ x y,
      f' x y = diagF3 n δ (e' x) (e' y) := by
  obtain ⟨δ', e', hδ', he'⟩ := exists_linearEquiv_diagF3 hn hf'
  have hδ'0 : δ' ≠ 0 := by rcases hδ' with rfl | rfl <;> decide
  set b : Fin n → Fin (n + 1) → ZMod 3 := fun i => (e.symm (e'.symm (Pi.single i 1)) : _)
    with hb
  have hbv : ∀ i, diagF3 (n + 1) δ (b i) v = 0 := fun i => mem_perpOne.1 (e.symm _).2
  have hbb : ∀ i j, diagF3 (n + 1) δ (b i) (b j) = if i = j then diagF3Entry n δ' i else 0 := by
    intro i j
    rw [hb, ← he, e.apply_symm_apply, e.apply_symm_apply, he', e'.apply_symm_apply,
      e'.apply_symm_apply, diagF3_single]
  set B : Fin (n + 1) → Fin (n + 1) → ZMod 3 := Fin.cons v b with hB
  have hG : (Matrix.of fun i j => diagF3 (n + 1) δ (B i) (B j)) =
      Matrix.diagonal (Fin.cons 1 (diagF3Entry n δ')) := by
    ext i j
    rw [Matrix.of_apply, Matrix.diagonal_apply]
    have hvb : ∀ j, diagF3 (n + 1) δ v (b j) = 0 := fun j => by
      rw [(isF3Form_diagF3 hδ).symm]; exact hbv j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB, hv]
    · simp [hB, hvb, (Fin.succ_ne_zero _).symm]
    · simp [hB, hbv, Fin.succ_ne_zero]
    · simp [hB, hbb, Fin.succ_inj]
  have hdet := det_gram_diagF3 δ B
  rw [hG, Matrix.det_diagonal, Fin.prod_univ_succ, Fin.cons_zero, one_mul] at hdet
  simp only [Fin.cons_succ] at hdet
  rw [prod_diagF3Entry hn, prod_diagF3Entry (by omega)] at hdet
  have hP : (Matrix.of fun i j => B j i).det ≠ 0 := fun h => hδ'0 (by rw [hdet, h]; ring)
  rw [sq_eq_one_of_ne_zero hP, one_mul] at hdet
  exact ⟨e', fun x y => by rw [he', hdet]⟩

theorem exists_norm_perp_of_dual (hf : IsF3Form f) {k : ℕ} (hk : k + 1 < m)
    {b b' : Fin k → Fin m → ZMod 3} (h : ∀ i j, f (b i) (b' j) = if i = j then 1 else 0)
    (hbb' : ∀ x, (∀ i, f x (b' i) = 0) → ∀ i, f x (b i) = 0) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ y, f y y = c ∧ ∀ i, f y (b' i) = 0 := by
  set P : (Fin m → ZMod 3) → Fin m → ZMod 3 := fun a => a - ∑ i, f a (b' i) • b i with hP
  have hpU : ∀ a, P a ∈ perpSub f b' := fun a => mem_perpSub.2 fun j => by
    simp only [hP, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sum_left,
      LinearMap.BilinForm.smul_left, h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]
  have hp : ∀ x ∈ perpSub f b', ∀ a, f x (P a) = f x a := fun x hx a => by
    have hxb := hbb' x (mem_perpSub.1 hx)
    simp only [hP, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sum_right,
      LinearMap.BilinForm.smul_right, hxb, mul_zero, Finset.sum_const_zero, sub_zero]
  obtain ⟨y, hy, hyy⟩ := exists_mem_norm_eq hf (nondegOn_of_proj hf P hpU hp)
    (perpSub_twoDim hf hk b') hc
  exact ⟨y, hyy, mem_perpSub.1 hy⟩

theorem exists_hyp_partner_of_dual (hf : IsF3Form f) {k : ℕ} {b b' : Fin k → Fin m → ZMod 3}
    (h : ∀ i j, f (b i) (b' j) = if i = j then 1 else 0)
    (hbb' : ∀ x, (∀ i, f x (b' i) = 0) → ∀ i, f x (b i) = 0) {z : Fin m → ZMod 3}
    (hz0 : z ≠ 0) (hzz : f z z = 0) (hzb : ∀ i, f z (b' i) = 0) :
    ∃ y, f y y = 0 ∧ f z y = 1 ∧ ∀ i, f y (b' i) = 0 := by
  set P : (Fin m → ZMod 3) → Fin m → ZMod 3 := fun a => a - ∑ i, f a (b' i) • b i with hP
  have hpU : ∀ a, P a ∈ perpSub f b' := fun a => mem_perpSub.2 fun j => by
    simp only [hP, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sum_left,
      LinearMap.BilinForm.smul_left, h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]
  have hp : ∀ x ∈ perpSub f b', ∀ a, f x (P a) = f x a := fun x hx a => by
    have hxb := hbb' x (mem_perpSub.1 hx)
    simp only [hP, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sum_right,
      LinearMap.BilinForm.smul_right, hxb, mul_zero, Finset.sum_const_zero, sub_zero]
  obtain ⟨y', hy'U, hzy'⟩ := nondegOn_of_proj hf P hpU hp z (mem_perpSub.2 hzb) hz0
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = (f z y')⁻¹ • y' := ⟨_, rfl⟩
  have hy₁b : ∀ i, f y₁ (b' i) = 0 := fun i => by
    rw [hy₁, LinearMap.BilinForm.smul_left, mem_perpSub.1 hy'U i, mul_zero]
  have hzy₁ : f z y₁ = 1 := by rw [hy₁, LinearMap.BilinForm.smul_right, inv_mul_cancel₀ hzy']
  have hy₁z : f y₁ z = 1 := by rw [hf.symm]; exact hzy₁
  refine ⟨y₁ + f y₁ y₁ • z, ?_, ?_, fun i => ?_⟩
  · rw [norm_add_smul hf, hy₁z, hzz]
    linear_combination (f y₁ y₁) * three_eq_zero
  · rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hzy₁, hzz, mul_zero,
      add_zero]
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hy₁b, hzb, mul_zero,
      add_zero]

set_option maxRecDepth 100000 in
theorem det_six_minus_aux : ∀ c d : ZMod 3,
    (!![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, c] : Matrix (Fin 6) (Fin 6) (ZMod 3)).det = d ^ 2 * 2 → c = 1 ∨ d = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem det_six_plus_aux : ∀ c d : ZMod 3,
    (!![1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, c] : Matrix (Fin 6) (Fin 6) (ZMod 3)).det = d ^ 2 * 1 → c = 1 ∨ d = 0 := by
  decide

theorem eq_zero_of_sum_eq_zero_six {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    {b b' : Fin 6 → Fin 6 → ZMod 3} (h : ∀ i j, j ≠ 5 → f (b i) (b' j) = if i = j then 1 else 0)
    (hy0 : b 5 ≠ 0) {g : Fin 6 → ZMod 3}
    (hg : ∑ i, g i • b i = 0) : g = 0 := by
  have hj : ∀ j, j ≠ 5 → g j = 0 := fun j hj => by
    have := congrArg (fun v => f v (b' j)) hg
    simpa [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, h _ _ hj] using this
  have h5' : g 5 = 0 := by
    rw [Fin.sum_univ_six, hj 0 (by decide), hj 1 (by decide), hj 2 (by decide), hj 3 (by decide),
      hj 4 (by decide)] at hg
    simp only [zero_smul, zero_add] at hg
    exact (smul_eq_zero.1 hg).resolve_right hy0
  funext i
  by_cases hi : i = 5
  · rw [hi, h5']; rfl
  · exact hj i hi

theorem normOneCompl₃_diagF3_six_two {w w' w'' z : Fin 6 → ZMod 3}
    (hw : diagF3 6 2 w w = 1) (hw' : diagF3 6 2 w' w' = 1) (hw'' : diagF3 6 2 w'' w'' = 1)
    (hww' : diagF3 6 2 w w' = 0) (hww'' : diagF3 6 2 w w'' = 0) (hw'w'' : diagF3 6 2 w' w'' = 0)
    (hz0 : z ≠ 0) (hzz : diagF3 6 2 z z = 0) (hzw : diagF3 6 2 z w = 0)
    (hzw' : diagF3 6 2 z w' = 0) (hzw'' : diagF3 6 2 z w'' = 0) :
    ∃ y, diagF3 6 2 y y = 1 ∧ diagF3 6 2 y w = 0 ∧ diagF3 6 2 y w' = 0 ∧
      diagF3 6 2 y w'' = 0 ∧ diagF3 6 2 y z = 0 := by
  have hf : IsF3Form (diagF3 6 2) := isF3Form_diagF3 (by decide)
  set f := diagF3 6 2 with hfdef
  have hw'w : f w' w = 0 := by rw [hf.symm]; exact hww'
  have hw''w : f w'' w = 0 := by rw [hf.symm]; exact hww''
  have hw''w' : f w'' w' = 0 := by rw [hf.symm]; exact hw'w''
  obtain ⟨z', hz'z', hzz', hz'u⟩ := exists_hyp_partner_perp hf (u := ![w, w', w''])
    (fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hw, hw', hw'', hww', hww'', hw'w'', hw'w, hw''w,
        hw''w'])
    hz0 hzz (fun i => by fin_cases i <;> simp [hzw, hzw', hzw''])
  have hz'w : f z' w = 0 := hz'u 0
  have hz'w' : f z' w' = 0 := hz'u 1
  have hz'w'' : f z' w'' = 0 := hz'u 2
  obtain ⟨y, hy0, hyp⟩ := exists_ne_zero_perp (f := f) (by norm_num : 5 < 6) ![w, w', w'', z, z']
  have hyw : f y w = 0 := hyp 0
  have hyw' : f y w' = 0 := hyp 1
  have hyw'' : f y w'' = 0 := hyp 2
  have hyz : f y z = 0 := hyp 3
  have hyz' : f y z' = 0 := hyp 4
  have hsymm : ∀ {a b : Fin 6 → ZMod 3}, f a b = 0 → f b a = 0 := fun h => by
    rw [hf.symm]; exact h
  have hz'z : f z' z = 1 := by rw [hf.symm]; exact hzz'
  set b : Fin 6 → Fin 6 → ZMod 3 := ![w, w', w'', z, z', y] with hb
  have hG : (Matrix.of fun i j => f (b i) (b j)) =
      !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
        0, 0, 0, 0, 0, f y y] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hw, hw', hw'', hww', hww'', hw'w'', hw'w, hw''w, hw''w', hzz, hzz', hz'z, hz'z',
        hzw, hzw', hzw'', hz'w, hz'w', hz'w'', hyw, hyw', hyw'', hyz, hyz', hsymm hzw,
        hsymm hzw', hsymm hzw'', hsymm hz'w, hsymm hz'w', hsymm hz'w'', hsymm hyw, hsymm hyw',
        hsymm hyw'', hsymm hyz, hsymm hyz']
  have hdet := det_gram_diagF3 2 b
  rw [hG, prod_diagF3Entry (by norm_num)] at hdet
  rcases det_six_minus_aux _ _ hdet with h1 | h0
  · exact ⟨y, h1, hyw, hyw', hyw'', hyz⟩
  · exfalso
    obtain ⟨g, hg0, hg₀⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [mulVec_of_eq_sum] at hg₀
    refine hg0 (eq_zero_of_sum_eq_zero_six (f := f) (b' := ![w, w', w'', z', z, y]) ?_ ?_ hg₀)
    · intro i j hj
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd rfl hj
        | simp [hb, hw, hw', hw'', hww', hww'', hw'w'', hw'w, hw''w, hw''w', hzz, hzz', hz'z,
            hz'z', hzw, hzw', hzw'', hz'w, hz'w', hz'w'', hyw, hyw', hyw'', hyz, hyz',
            hsymm hzw, hsymm hzw', hsymm hzw'', hsymm hz'w, hsymm hz'w', hsymm hz'w'']
    · exact hy0

theorem exists_norm_one_perp_iso_two_six {w z n : Fin 6 → ZMod 3} (hw : diagF3 6 1 w w = 1)
    (hz0 : z ≠ 0) (hzz : diagF3 6 1 z z = 0) (hzw : diagF3 6 1 z w = 0)
    (hnn : diagF3 6 1 n n = 0) (hnw : diagF3 6 1 n w = 0) (hzn : diagF3 6 1 z n = 0)
    (hind : ∀ a : ZMod 3, n ≠ a • z) :
    ∃ t, diagF3 6 1 t t = 1 ∧ diagF3 6 1 t w = 0 ∧ diagF3 6 1 t z = 0 ∧
      diagF3 6 1 t n = 0 := by
  have hf : IsF3Form (diagF3 6 1) := isF3Form_diagF3 (by decide)
  set f := diagF3 6 1 with hfdef
  have hsymm : ∀ {a b : Fin 6 → ZMod 3}, f a b = 0 → f b a = 0 := fun h => by
    rw [hf.symm]; exact h
  have hn0 : n ≠ 0 := by simpa using hind 0
  obtain ⟨p, hpp, hpw, hpz, hpn⟩ := exists_isotropic_pairings hf hw hz0 hzz hzw hnw hzn hind 0
  have hzp : f z p = 1 := by rw [hf.symm]; exact hpz
  have hnz : f n z = 0 := hsymm hzn
  obtain ⟨q, hqq, hnq, hqb⟩ := exists_hyp_partner_of_dual hf (b := ![w, z, p])
    (b' := ![w, p, z])
    (fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hw, hzz, hpp, hzp, hpz, hpw, hzw, hsymm hpw,
        hsymm hzw])
    (fun x hx i => by
      have h0 := hx 0
      have h1 := hx 1
      have h2 := hx 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
      fin_cases i <;> simp [h0, h1, h2])
    hn0 hnn (fun i => by fin_cases i <;> simp [hnw, hsymm hpn, hnz])
  have hqw : f q w = 0 := hqb 0
  have hqp : f q p = 0 := hqb 1
  have hqz : f q z = 0 := hqb 2
  have hqn : f q n = 1 := by rw [hf.symm]; exact hnq
  obtain ⟨t, ht0, htp⟩ := exists_ne_zero_perp (f := f) (by norm_num : 5 < 6) ![w, z, p, n, q]
  have htw : f t w = 0 := htp 0
  have htz : f t z = 0 := htp 1
  have htpp : f t p = 0 := htp 2
  have htn : f t n = 0 := htp 3
  have htq : f t q = 0 := htp 4
  set b : Fin 6 → Fin 6 → ZMod 3 := ![w, z, p, n, q, t] with hb
  have hG : (Matrix.of fun i j => f (b i) (b j)) =
      !![1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0;
        0, 0, 0, 0, 0, f t t] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hw, hzz, hpp, hnn, hqq, hzp, hpz, hnq, hqn, hzw, hpw, hnw, hqw, htw, hpn, hzn,
        hqp, hqz, htz, htpp, htn, htq, hsymm hzw, hsymm hpw, hsymm hnw, hsymm hqw, hsymm htw,
        hsymm hpn, hsymm hzn, hsymm hqp, hsymm hqz, hsymm htz, hsymm htpp, hsymm htn, hsymm htq]
  have hdet := det_gram_diagF3 1 b
  rw [hG, prod_diagF3Entry (by norm_num)] at hdet
  rcases det_six_plus_aux _ _ hdet with h1 | h0
  · exact ⟨t, h1, htw, htz, htn⟩
  · exfalso
    obtain ⟨g, hg0, hg₀⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [mulVec_of_eq_sum] at hg₀
    refine hg0 (eq_zero_of_sum_eq_zero_six (f := f) (b' := ![w, p, z, q, n, t]) ?_ ht0 hg₀)
    intro i j hj
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hj
      | simp [hb, hw, hzz, hpp, hnn, hqq, hzp, hpz, hnq, hqn, hzw, hpw, hnw, hqw, htw, hpn, hzn,
          hqp, hqz, htz, htpp, htn, htq, hsymm hzw, hsymm hpw, hsymm hnw, hsymm hqw,
          hsymm hpn, hsymm hzn, hsymm hqp, hsymm hqz]

end CFSG.Fischer.Classification.LocalU
