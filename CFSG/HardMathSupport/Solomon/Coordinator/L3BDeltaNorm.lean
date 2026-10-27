module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusPSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def starM (h : UnitaryFieldData p f K) (M : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K :=
  (M.map h.bar)ᵀ

theorem starM_mul (h : UnitaryFieldData p f K) (M N : Matrix (Fin 3) (Fin 3) K) :
    starM h (M * N) = starM h N * starM h M := by
  simp [starM, Matrix.map_mul, Matrix.transpose_mul]

theorem starM_starM (h : UnitaryFieldData p f K) (M : Matrix (Fin 3) (Fin 3) K) :
    starM h (starM h M) = M := by
  ext i j
  simp [starM, UnitaryFieldData.bar_bar]

theorem starM_one (h : UnitaryFieldData p f K) : starM h (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp [starM, Matrix.map_one]

theorem starM_smul (h : UnitaryFieldData p f K) (c : K) (M : Matrix (Fin 3) (Fin 3) K) :
    starM h (c • M) = h.bar c • starM h M := by
  ext i j
  simp [starM]

theorem commute_starM_mul_of_normalizes (h : UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ Subgroup.normalizer (unitarySU p f K 3 : Set (GL (Fin 3) K)))
    {x : GL (Fin 3) K} (hx : x ∈ unitarySU p f K 3) :
    (starM h (g : Matrix (Fin 3) (Fin 3) K) * g) * (x : Matrix (Fin 3) (Fin 3) K) =
      (x : Matrix (Fin 3) (Fin 3) K) * (starM h (g : Matrix (Fin 3) (Fin 3) K) * g) := by
  set M : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  set N : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hN
  set X : Matrix (Fin 3) (Fin 3) K := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hX
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hx' := (mem_unitarySU_iff h).1 hx
  have hXX : starM h X * X = 1 := hx'.2
  have hXX' : X * starM h X = 1 := mul_eq_one_comm.1 hXX
  have hy : g * x * g⁻¹ ∈ unitarySU p f K 3 := (Subgroup.mem_normalizer_iff.1 hg x).1 hx
  have hy' := ((mem_unitarySU_iff h).1 hy).2
  rw [Units.val_mul, Units.val_mul] at hy'
  change starM h (M * X * N) * (M * X * N) = 1 at hy'
  rw [starM_mul, starM_mul] at hy'
  have hab : starM h M * starM h N = 1 := by rw [← starM_mul, hNM, starM_one]
  have h3 : starM h X * (starM h M * M) * X = starM h M * M := by
    calc starM h X * (starM h M * M) * X
        = (starM h M * starM h N) * starM h X * (starM h M * M) * X * (N * M) := by
          rw [hab, hNM]; simp [Matrix.mul_assoc]
      _ = starM h M * (starM h N * starM h X * starM h M * (M * X * N)) * M := by
          simp only [Matrix.mul_assoc]
      _ = starM h M * M := by
          rw [show starM h N * starM h X * starM h M * (M * X * N) = 1 from by
            simpa [Matrix.mul_assoc] using hy']
          simp
  calc starM h M * M * X = (X * starM h X) * (starM h M * M) * X := by rw [hXX', one_mul]
    _ = X * (starM h X * (starM h M * M) * X) := by simp only [Matrix.mul_assoc]
    _ = X * (starM h M * M) := by rw [h3]

theorem exists_normOne_sq_ne_one (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    ∃ a ∈ normOneUnits h, a ^ 2 ≠ 1 := by
  have := h.finite
  by_contra hcon
  push Not at hcon
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := normOneUnits h)
  have h1 : orderOf γ ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hcon γ γ.2))
  have h2 : Nat.card (normOneUnits h) = orderOf γ :=
    (orderOf_eq_card_of_forall_mem_zpowers hγ).symm
  have h3 := (card_unitaryIsom3_normOne h).2
  have := Nat.le_of_dvd (by norm_num) h1
  omega

theorem det_permGL_finRotate (K : Type) [Field K] :
    ((permGL K (finRotate 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_permGL, Matrix.det_permutation]
  have : Equiv.Perm.sign (finRotate 3)⁻¹ = 1 := by
    rw [map_inv]
    have := sign_finRotate 2
    simp
  simp [this]

theorem permGL_finRotate_mem_unitarySU (h : UnitaryFieldData p f K) :
    permGL K (finRotate 3) ∈ unitarySU p f K 3 :=
  (mem_unitarySU_iff h).2 ⟨det_permGL_finRotate K,
    monomialGroup_le_unitaryIsom3 h (Subgroup.mem_sup_right ⟨_, rfl⟩)⟩

theorem diagHom_mem_unitarySU_of_mem (h : UnitaryFieldData p f K) {a : Kˣ}
    (ha : a ∈ normOneUnits h) : diagHom 3 K ![a, a⁻¹, 1] ∈ unitarySU p f K 3 := by
  have hd : ∀ i, (![a, a⁻¹, 1] : Fin 3 → Kˣ) i ∈ normOneUnits h := by
    intro i
    fin_cases i
    · exact ha
    · exact (normOneUnits h).inv_mem ha
    · exact (normOneUnits h).one_mem
  refine (mem_unitarySU_iff h).2 ⟨?_, diagHom_mem_unitaryIsom3 h hd⟩
  rw [coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem exists_scalar_of_commute_unitarySU (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {S : Matrix (Fin 3) (Fin 3) K}
    (hS : ∀ x ∈ unitarySU p f K 3, S * (x : Matrix (Fin 3) (Fin 3) K) = x * S) :
    ∃ c : K, S = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨a, ha, ha2⟩ := exists_normOne_sq_ne_one h hq
  have h1 : (a : K) ≠ 1 := by
    intro h1
    apply ha2
    have : a = 1 := Units.ext h1
    rw [this, one_pow]
  have h2 : (a : K) ≠ (a : K)⁻¹ := by
    intro h2
    apply ha2
    have : a = a⁻¹ := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h2)
    rw [pow_two]
    nth_rewrite 1 [this]
    exact inv_mul_cancel a
  have h3 : (a : K)⁻¹ ≠ 1 := by
    intro h3
    apply h1
    simpa using h3
  have hdiag := hS _ (diagHom_mem_unitarySU_of_mem h ha)
  rw [coe_diagHom] at hdiag
  have hoff : ∀ i j : Fin 3, i ≠ j → S i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hdiag i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    have hne : ((![a, a⁻¹, 1] : Fin 3 → Kˣ) j : K) - ((![a, a⁻¹, 1] : Fin 3 → Kˣ) i : K) ≠ 0 := by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
        first
        | exact sub_ne_zero.2 (Ne.symm h1)
        | exact sub_ne_zero.2 h1
        | exact sub_ne_zero.2 h2
        | exact sub_ne_zero.2 (Ne.symm h2)
        | exact sub_ne_zero.2 h3
        | exact sub_ne_zero.2 (Ne.symm h3)
    have : S i j * (((![a, a⁻¹, 1] : Fin 3 → Kˣ) j : K) - ((![a, a⁻¹, 1] : Fin 3 → Kˣ) i : K)) =
        0 := by
      rw [mul_sub]
      rw [mul_comm (S i j)] at e ⊢
      linear_combination e
    exact (mul_eq_zero.1 this).resolve_right hne
  have hSd : S = Matrix.diagonal (fun i => S i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hP := hS _ (permGL_finRotate_mem_unitarySU h)
  rw [hSd] at hP
  have e02 := congrFun (congrFun hP 0) 2
  have e10 := congrFun (congrFun hP 1) 0
  simp [coe_permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at e02 e10
  have hm1 : (-1 : Fin 3) = 2 := by decide
  simp only [hm1, ↓reduceIte] at e02
  refine ⟨S 0 0, ?_⟩
  rw [hSd]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [e02, e10]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem exists_unit_pow_eq (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) {c : Kˣ}
    (hc : c ^ (p ^ f - 1) = 1) : ∃ l : Kˣ, l ^ (p ^ f + 1) = c := by
  have := h.finite
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (p ^ f - 1) * (p ^ f + 1) := by
    rw [Nat.card_units, h.card, show 2 * f = f * 2 from mul_comm _ _, pow_mul]
    zify [hq1, hq2]
    ring
  have hord : orderOf γ = (p ^ f - 1) * (p ^ f + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hcard]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, γ ^ m = c :=
    (mem_powers_iff_mem_zpowers).2 (hγ c)
  have h1 : orderOf γ ∣ m * (p ^ f - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul, hm]
    exact hc
  have hpos : 0 < p ^ f - 1 := by omega
  have h2 : (p ^ f + 1) ∣ m := by
    refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
    rw [hord, mul_comm m] at h1
    exact h1
  obtain ⟨k, hk⟩ := h2
  exact ⟨γ ^ k, by rw [← pow_mul, mul_comm, ← hk, hm]⟩

theorem exists_scalar_mul_mem_unitaryIsom3 (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {g : GL (Fin 3) K}
    (hg : g ∈ Subgroup.normalizer (unitarySU p f K 3 : Set (GL (Fin 3) K))) :
    ∃ l : Kˣ, GeneralLinearGroup.scalar (Fin 3) l * g ∈ unitaryIsom3 h := by
  set M : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  set N : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_unitarySU h hq (S := starM h M * M)
    fun x hx => commute_starM_mul_of_normalizes h hg hx
  have hab : starM h M * starM h N = 1 := by rw [← starM_mul, hNM, starM_one]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : (starM h M * M) * (N * starM h N) = 1 := by
      calc (starM h M * M) * (N * starM h N) = starM h M * (M * N) * starM h N := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hMN, Matrix.mul_one, hab]
    rw [hc, h0, zero_smul, zero_mul] at h1
    exact zero_ne_one h1
  have hbar : h.bar c = c := by
    have h1 : starM h (starM h M * M) = starM h M * M := by
      rw [starM_mul, starM_starM]
    rw [hc, starM_smul, starM_one] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this
  have hcp : c ^ (p ^ f - 1) = 1 := by
    have h1 : c ^ (p ^ f) = c := by rw [← UnitaryFieldData.bar_apply]; exact hbar
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
    have h2 : c ^ (p ^ f - 1) * c = 1 * c := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, h1, one_mul]
    exact mul_right_cancel₀ hc0 h2
  have hu : (Units.mk0 c hc0)⁻¹ ^ (p ^ f - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hcp,
      inv_one, Units.val_one]
  obtain ⟨l, hl⟩ := exists_unit_pow_eq h hq hu
  have hl' : (l : K) ^ (p ^ f + 1) = c⁻¹ := by
    have := congrArg Units.val hl
    rwa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at this
  refine ⟨l, ?_⟩
  have hval : ((GeneralLinearGroup.scalar (Fin 3) l * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (l : K) • M := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  rw [mem_unitaryIsom3]
  change starM h _ * _ = 1
  rw [hval, starM_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, smul_smul]
  have : h.bar l * l * c = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, hl']
    exact inv_mul_cancel₀ hc0
  rw [this, one_smul]

end CFSG.HardMathSupport.Solomon.Coordinator
