module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62PhiMat

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem u62lb_phi_pow_scalar (s : gramSU h (idGram K 6)) :
    ∃ c : Kˣ, ((s : GL (Fin 6) K)) ^ (orderOf (s : primeFormP h (idGram K 6))) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  have h1 : ((s ^ orderOf (s : primeFormP h (idGram K 6)) : gramSU h (idGram K 6)) :
      primeFormP h (idGram K 6)) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  rw [QuotientGroup.eq_one_iff, mem_normOneScalars_iff h] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, by rw [← hc, Subgroup.coe_pow]⟩

theorem u62lb_phi_lift_comm (s : gramSU h (idGram K 6)) (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1)
    (hk : Nat.Coprime 3 (orderOf (s : primeFormP h (idGram K 6))))
    (hcomm : diagP h μ hμ * (s : primeFormP h (idGram K 6)) =
      (s : primeFormP h (idGram K 6)) * diagP h μ hμ) :
    (dmat μ : GL (Fin 6) K) * (s : GL (Fin 6) K) = (s : GL (Fin 6) K) * dmat μ := by
  have hd : diagP h μ hμ =
      ((dmatS h μ hμ : gramSU h (idGram K 6)) : primeFormP h (idGram K 6)) := rfl
  rw [hd, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    mem_normOneScalars_iff h] at hcomm
  obtain ⟨c, hc⟩ := hcomm
  have hc' : (s : GL (Fin 6) K)⁻¹ * (dmat μ : GL (Fin 6) K)⁻¹ *
      ((s : GL (Fin 6) K) * dmat μ) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← hc]
    rfl
  set z : GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6) c with hzdef
  have hz : (dmat μ : GL (Fin 6) K)⁻¹ * (s : GL (Fin 6) K) * dmat μ = (s : GL (Fin 6) K) * z := by
    rw [← hc']
    group
  obtain ⟨c', hc'0⟩ := u62lb_phi_pow_scalar h s
  set k := orderOf (s : primeFormP h (idGram K 6)) with hkdef
  have hcomm_sz : Commute (s : GL (Fin 6) K) z := commute_scalar c _
  have h1 : ((dmat μ : GL (Fin 6) K)⁻¹ * (s : GL (Fin 6) K) * (dmat μ : GL (Fin 6) K)) ^ k =
      (dmat μ : GL (Fin 6) K)⁻¹ * (s : GL (Fin 6) K) ^ k * dmat μ := by
    have := conj_pow (a := (dmat μ : GL (Fin 6) K)⁻¹) (b := (s : GL (Fin 6) K)) (i := k)
    rwa [inv_inv] at this
  have h2 : (dmat μ : GL (Fin 6) K)⁻¹ * (s : GL (Fin 6) K) ^ k * dmat μ =
      (s : GL (Fin 6) K) ^ k := by
    rw [hc'0, mul_assoc, ← (commute_scalar c' (dmat μ : GL (Fin 6) K)).eq, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have h3 : (s : GL (Fin 6) K) ^ k * z ^ k = (s : GL (Fin 6) K) ^ k := by
    rw [← hcomm_sz.mul_pow, ← hz, h1, h2]
  have h4 : z ^ k = 1 := by
    have : (s : GL (Fin 6) K) ^ k * z ^ k = (s : GL (Fin 6) K) ^ k * 1 := by
      rw [mul_one]
      exact h3
    exact mul_left_cancel this
  have h5 : z ^ 3 = 1 := by
    rw [hzdef, ← map_pow, u62lb_units_pow_three h, map_one]
  have h6 : z = 1 := by
    have := (pow_gcd_eq_one (a := z) (m := 3) (n := k)).2 ⟨h5, h4⟩
    rw [hk, pow_one] at this
    exact this
  rw [h6, mul_one, mul_assoc] at hz
  exact (inv_mul_eq_iff_eq_mul.1 hz).symm

theorem u62lb_phi_entry_comm (M : Matrix (Fin 6) (Fin 6) K) (μ : Fin 6 → Kˣ)
    (hcomm : (dmat μ : GL (Fin 6) K).1 * M = M * (dmat μ : GL (Fin 6) K).1) (a b : Fin 6) :
    M a b ≠ 0 → μ a = μ b := by
  intro hne
  have := congrFun (congrFun hcomm a) b
  rw [coe_dmat, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have h2 : (μ a : K) * M a b = (μ b : K) * M a b := by
    rw [this, mul_comm]
  exact Units.ext (mul_right_cancel₀ hne h2)

theorem u62lb_phi_det_one (s : gramSU h (idGram K 6)) :
    ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
  (mem_gramSU.1 s.2).2

theorem u62lb_phi_unitary_entries (s : gramSU h (idGram K 6)) (i j : Fin 6) :
    ∑ k, h.bar (((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) k i) *
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) k j = if i = j then 1 else 0 := by
  have h1 := (mem_gramSU.1 s.2).1
  have h2 := congrFun (congrFun h1 i) j
  change ((((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ *
    ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) i j =
    ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j at h2
  rw [Units.val_one, Matrix.mul_one, Matrix.mul_apply, Matrix.one_apply] at h2
  simpa [Matrix.transpose_apply, Matrix.map_apply] using h2

theorem u62lb_phi_diag_entries (s : gramSU h (idGram K 6))
    (hk : Nat.Coprime 3 (orderOf (s : primeFormP h (idGram K 6))))
    (hdiag : ∀ a b, a ≠ b → ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a b = 0)
    (a b : Fin 6) :
    ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a a =
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) b b := by
  obtain ⟨c', hc'⟩ := u62lb_phi_pow_scalar h s
  set M : Matrix (Fin 6) (Fin 6) K := ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hM
  have hMd : M = diagonal fun a => M a a := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hxy]
      exact hdiag x y hxy
  have hdet : ∏ a, M a a = 1 := by
    have := u62lb_phi_det_one h s
    rw [← hM, hMd, det_diagonal] at this
    exact this
  have hne : ∀ a, M a a ≠ 0 := by
    intro a ha
    have : ∏ a, M a a = 0 := Finset.prod_eq_zero (Finset.mem_univ a) ha
    rw [hdet] at this
    exact one_ne_zero this
  have hpow : ∀ a, (M a a) ^ (orderOf (s : primeFormP h (idGram K 6))) = (c' : K) := by
    intro a
    have e1 : M ^ (orderOf (s : primeFormP h (idGram K 6))) =
        Matrix.scalar (Fin 6) (c' : K) := by
      rw [hM, ← Units.val_pow_eq_pow_val, hc', Matrix.GeneralLinearGroup.coe_scalar]
    rw [hMd, diagonal_pow, scalar_apply] at e1
    have := congrFun (congrFun e1 a) a
    rwa [diagonal_apply_eq, diagonal_apply_eq] at this
  have hab : Units.mk0 (M a a) (hne a) ^ (orderOf (s : primeFormP h (idGram K 6))) =
      Units.mk0 (M b b) (hne b) ^ (orderOf (s : primeFormP h (idGram K 6))) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0,
      hpow a, hpow b]
  have := u62lb_phi_pow_inj h hk hab
  exact congrArg (fun u : Kˣ => (u : K)) this

theorem u62lb_phi_exists_offdiag (s : gramSU h (idGram K 6))
    (hk : Nat.Coprime 3 (orderOf (s : primeFormP h (idGram K 6))))
    (hne : (s : primeFormP h (idGram K 6)) ≠ 1) :
    ∃ u v : Fin 6, u ≠ v ∧ ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) u v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hall := u62lb_phi_diag_entries h s hk hcon
  set M : Matrix (Fin 6) (Fin 6) K := ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hM
  have hMd : M = diagonal fun a => M a a := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hxy]
      exact hcon x y hxy
  have hdet : ∏ a, M a a = 1 := by
    have := u62lb_phi_det_one h s
    rw [← hM, hMd, det_diagonal] at this
    exact this
  have hc0 : M 0 0 ≠ 0 := by
    intro ha
    have : ∏ a, M a a = 0 := Finset.prod_eq_zero (Finset.mem_univ 0) ha
    rw [hdet] at this
    exact one_ne_zero this
  rw [QuotientGroup.eq_one_iff, mem_normOneScalars_iff h]
  refine ⟨Units.mk0 (M 0 0) hc0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply]
  ext x y
  rw [diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    exact hall x 0
  · rw [if_neg hxy]
    exact hcon x y hxy

end CFSG.HardMathSupport.Dickson.Bal207

end
