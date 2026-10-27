module

public import CFSG.Fischer.Classification.Orthogonal3.Local

public section

namespace CFSG.Fischer.Classification.LocalR3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem exists_norm_one_perp_hyp (hf : IsF3Form f) (hm : 5 ≤ m) {v z y : Fin m → ZMod 3}
    (hv : f v v = 1) (hzz : f z z = 0) (hzv : f z v = 0) (hyy : f y y = 0) (hyz : f y z = 1)
    (hyv : f y v = 0) : ∃ w, f w w = 1 ∧ f w v = 0 ∧ f w z = 0 ∧ f w y = 0 := by
  obtain ⟨hpU, hp⟩ := nondegOn_perp_hyp hf hv hzz hzv hyy hyz hyv
  obtain ⟨w, hw, hww⟩ := exists_mem_norm_eq hf (nondegOn_of_proj hf _ hpU hp)
    (perpSub_twoDim hf (k := 3) (by omega) _) (c := 1) one_ne_zero
  obtain ⟨h1, h2, h3⟩ := mem_perpSub_three.1 hw
  exact ⟨w, hww, h1, h2, h3⟩

theorem exists_norm_one_perp_of_ne_zero (hf : IsF3Form f) (hm : 5 ≤ m) {w n z : Fin m → ZMod 3}
    (hw : f w w = 1) (hnn : f n n = 0) (hnw : f n w = 0) (hzz : f z z = 0) (hzw : f z w = 0)
    (hnz : f n z ≠ 0) : ∃ t, f t t = 1 ∧ f t w = 0 ∧ f t n = 0 ∧ f t z = 0 := by
  obtain ⟨t, htt, htw, htz, hty⟩ := exists_norm_one_perp_hyp hf hm hw hzz hzw
    (y := (f n z)⁻¹ • n) (by rw [norm_smul, hnn, mul_zero])
    (by rw [LinearMap.BilinForm.smul_left, inv_mul_cancel₀ hnz])
    (by rw [LinearMap.BilinForm.smul_left, hnw, mul_zero])
  refine ⟨t, htt, htw, ?_, htz⟩
  rw [LinearMap.BilinForm.smul_right] at hty
  exact (mul_eq_zero.1 hty).resolve_left (inv_ne_zero hnz)

theorem exists_norm_one_perp_iso_two (hf : IsF3Form f) (hm : 7 ≤ m) {w z n : Fin m → ZMod 3}
    (hw : f w w = 1) (hz0 : z ≠ 0) (hzz : f z z = 0) (hzw : f z w = 0) (hnn : f n n = 0)
    (hnw : f n w = 0) (hzn : f z n = 0) (hind : ∀ a : ZMod 3, n ≠ a • z) :
    ∃ t, f t t = 1 ∧ f t w = 0 ∧ f t z = 0 ∧ f t n = 0 := by
  have hn0 : n ≠ 0 := by simpa using hind 0
  obtain ⟨p, hpp, hpw, hpz, hpn⟩ :=
    exists_isotropic_pairings hf hw hz0 hzz hzw hnw hzn hind 0
  have hwz : f w z = 0 := by rw [hf.symm]; exact hzw
  have hwn : f w n = 0 := by rw [hf.symm]; exact hnw
  have hwp : f w p = 0 := by rw [hf.symm]; exact hpw
  have hzp : f z p = 1 := by rw [hf.symm]; exact hpz
  have hnz : f n z = 0 := by rw [hf.symm]; exact hzn
  have hnp : f n p = 0 := by rw [hf.symm]; exact hpn
  have hli : LinearIndependent (ZMod 3) ![w, z, p, n] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at hg
    have h0 : g 0 = 0 := by
      have := congrArg (fun x => f x w) hg
      simpa [hw, hzw, hpw, hnw] using this
    have h2 : g 2 = 0 := by
      have := congrArg (fun x => f x z) hg
      simpa [hwz, hzz, hpz, hnz] using this
    have h1 : g 1 = 0 := by
      have := congrArg (fun x => f x p) hg
      simpa [hwp, hzp, hpp, hnp] using this
    have h3 : g 3 = 0 := by
      rw [h0, h1, h2, zero_smul, zero_smul, zero_smul, zero_add, zero_add, zero_add] at hg
      exact (smul_eq_zero.1 hg).resolve_right hn0
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  obtain ⟨x, hx⟩ := exists_pairings hf hli ![0, 0, 0, 1]
  have hxw : f x w = 0 := by simpa using hx 0
  have hxz : f x z = 0 := by simpa using hx 1
  have hxp : f x p = 0 := by simpa using hx 2
  have hxn : f x n = 1 := by simpa using hx 3
  obtain ⟨c, hc⟩ := exists_norm_add_smul_eq hf (x := x) hnn (by rw [hxn]; exact one_ne_zero) 0
  set q := x + c • n with hq
  have hqq : f q q = 0 := hc
  have hqw : f q w = 0 := by
    rw [hq, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxw, hnw]; ring
  have hqz : f q z = 0 := by
    rw [hq, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxz, hnz]; ring
  have hqp : f q p = 0 := by
    rw [hq, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxp, hnp]; ring
  have hqn : f q n = 1 := by
    rw [hq, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxn, hnn]; ring
  have hwq : f w q = 0 := by rw [hf.symm]; exact hqw
  have hzq : f z q = 0 := by rw [hf.symm]; exact hqz
  have hpq : f p q = 0 := by rw [hf.symm]; exact hqp
  have hnq : f n q = 1 := by rw [hf.symm]; exact hqn
  have hmem : ∀ x, x ∈ perpSub f ![w, z, p, n, q] ↔
      f x w = 0 ∧ f x z = 0 ∧ f x p = 0 ∧ f x n = 0 ∧ f x q = 0 := fun x => by
    simp [mem_perpSub, Fin.forall_fin_succ]
  set P : (Fin m → ZMod 3) → Fin m → ZMod 3 := fun a =>
    a - f a w • w - f a p • z - f a z • p - f a q • n - f a n • q with hP
  have hPU : ∀ a, P a ∈ perpSub f ![w, z, p, n, q] := fun a => by
    refine (hmem _).2 ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hP, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hw, hzw, hpw,
        hnw, hqw, hwz, hzz, hpz, hnz, hqz, hwp, hzp, hpp, hnp, hqp, hwn, hzn, hpn, hnn, hqn, hwq,
        hzq, hpq, hnq, hqq]
      ring
  have hPx : ∀ x ∈ perpSub f ![w, z, p, n, q], ∀ a, f x (P a) = f x a := by
    intro x hx a
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hmem x).1 hx
    simp only [hP, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, h1, h2, h3, h4,
      h5]
    ring
  obtain ⟨t, ht, htt⟩ := exists_mem_norm_eq hf (nondegOn_of_proj hf P hPU hPx)
    (perpSub_twoDim hf (k := 5) (by omega) _) (c := 1) one_ne_zero
  obtain ⟨h1, h2, -, h4, -⟩ := (hmem t).1 ht
  exact ⟨t, htt, h1, h2, h4⟩

theorem exists_smul_eq_of_perp_two (hf : IsF3Form f) (hm : 6 ≤ m) {w w' z s : Fin m → ZMod 3}
    (hw : f w w = 1) (hw' : f w' w' = 1) (hw'w : f w' w = 0) (hz0 : z ≠ 0) (hzz : f z z = 0)
    (hzw : f z w = 0) (hzw' : f z w' = 0) (hsw : f s w = 0) (hsw' : f s w' = 0)
    (hs : ∀ y, f y y = 1 → f y w = 0 → f y w' = 0 → f y z = 0 → f s y = 0)
    (hss : f s s = 0 ∨ f s s = 1) : ∃ γ : ZMod 3, s = γ • z := by
  let e : perpOne f w ≃ₗ[ZMod 3] (Fin (m - 1) → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_perpOne hw, Module.finrank_fin_fun])
  have hf' := isF3Form_restrictForm hf hw e
  have happ := restrictForm_apply (f := f) e
  set W : perpOne f w := ⟨w', mem_perpOne.2 hw'w⟩
  set Z : perpOne f w := ⟨z, mem_perpOne.2 hzw⟩
  set S : perpOne f w := ⟨s, mem_perpOne.2 hsw⟩
  have hZ0 : e Z ≠ 0 := fun h => hz0 (congrArg Subtype.val
    ((LinearEquiv.map_eq_zero_iff e).1 h))
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_perp hf' (by omega) (v := e W) (z := e Z) (s := e S)
    (by rw [happ]; exact hw') hZ0 (by rw [happ]; exact hzz) (by rw [happ]; exact hzw')
    (by rw [happ]; exact hsw')
    (fun y hyy hyv hyz => by
      have hy := e.apply_symm_apply y
      rw [← hy, happ] at hyy hyv hyz ⊢
      exact hs _ hyy (mem_perpOne.1 (e.symm y).2) hyv hyz)
    (by rw [happ]; exact hss)
  refine ⟨γ, ?_⟩
  have := congrArg Subtype.val (e.injective (hγ.trans (e.map_smul γ Z).symm))
  exact this

end CFSG.Fischer.Classification.LocalR3
