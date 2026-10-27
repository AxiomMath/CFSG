module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Even

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Matrix CFSG.Open

theorem threeTwoWitness_statedProj_commuting_mod {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Finite K] {H : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (g x : Matrix.GeneralLinearGroup ι K) (hg : g ∈ H) (hx : x ∈ H) (hgg : g * g = 1)
    (hgns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ g)
    (hx3 : ∃ u : Kˣ, x ^ 3 = Matrix.GeneralLinearGroup.scalar ι u)
    (hxns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ x) (hc : Commute g x) :
    ThreeTwoWitness (StatedProj H) := by
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  let a : H := ⟨g, hg⟩
  let c' : H := ⟨x, hx⟩
  have hmem : ∀ y : H, π y = 1 →
      ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u = (y : Matrix.GeneralLinearGroup ι K) :=
    fun y hy => (QuotientGroup.eq_one_iff y).1 hy
  have haa : a * a = 1 := Subtype.ext hgg
  obtain ⟨u3, hu3⟩ := hx3
  have hc3 : π (c' ^ 3) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨u3, hu3.symm⟩
  refine ThreeTwoWitness.of_commuting (g := π a) (x := π c') ?_ ?_ ?_ ?_
  · rw [pow_two, ← map_mul, haa, map_one]
  · intro h
    obtain ⟨u, hu⟩ := hmem a h
    exact hgns u hu
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      exact hc3
    · intro h
      obtain ⟨u, hu⟩ := hmem c' h
      exact hxns u hu
  · exact Commute.map (show Commute a c' from Subtype.ext hc) π

theorem exists_units_orderOf_eq {K : Type} [Field K] [Finite K] {d : ℕ} (hd : d ∣ Nat.card Kˣ) :
    ∃ g : Kˣ, orderOf g = d := by
  have : IsCyclic Kˣ := inferInstance
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hN : orderOf γ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨m, hm⟩ := hd
  have hpos : 0 < Nat.card Kˣ := Nat.card_pos
  have hm0 : m ≠ 0 := by
    intro h
    rw [hm, h] at hpos
    simp at hpos
  refine ⟨γ ^ m, ?_⟩
  rw [orderOf_pow_of_dvd hm0 (by rw [hN, hm]; exact dvd_mul_left _ _), hN, hm]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)

section Torus

variable {K : Type} [Field K] {ε : K} {q : ℕ}

@[expose] def uT (ε : K) : Matrix (Fin 3) (Fin 3) K :=
  !![ε ^ 7, ε + ε ^ 7, ε + ε ^ 7; ε + ε ^ 7, ε ^ 7, ε + ε ^ 7; ε + ε ^ 7, ε + ε ^ 7, ε ^ 7]

@[expose] def uTc (ε : K) : Matrix (Fin 3) (Fin 3) K :=
  !![ε ^ 56, ε ^ 8 + ε ^ 56, ε ^ 8 + ε ^ 56; ε ^ 8 + ε ^ 56, ε ^ 56, ε ^ 8 + ε ^ 56;
    ε ^ 8 + ε ^ 56, ε ^ 8 + ε ^ 56, ε ^ 56]

theorem uT_cubed (h2 : (2 : K) = 0) (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0) :
    uT ε * uT ε * uT ε = Matrix.diagonal (fun _ => ε ^ 3) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-4) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-3) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-3) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-3) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-4) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-3) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-3) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-3) * ε ^ 3) * h2
  · simp [uT, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (3) * ε ^ 3 + (-9) * ε ^ 6 + (18) * ε ^ 9 + (-9) * ε ^ 12 +
      (9) * ε ^ 15) * hΦ + ((-3) + (-4) * ε ^ 3) * h2

theorem uT_unitary (h2 : (2 : K) = 0) (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0) :
    (uTc ε)ᵀ * uT ε = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-3) + (3) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-3) + (3) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2
  · simp [uT, uTc, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-3) + (3) * ε ^ 3 + (-1) * ε ^ 9 + (1) * ε ^ 12 + (2) * ε ^ 15 +
      (-3) * ε ^ 18 + (1) * ε ^ 21 + (2) * ε ^ 24 + (-3) * ε ^ 27 + (1) * ε ^ 30 + (2) * ε ^ 33 +
      (-3) * ε ^ 36 + (1) * ε ^ 39 + (2) * ε ^ 42 + (-3) * ε ^ 45 + (1) * ε ^ 48 + (2) * ε ^ 51 +
      (-3) * ε ^ 54 + (3) * ε ^ 57) * hΦ + ((1)) * h2

theorem uD1_uT_comm (h2 : (2 : K) = 0) (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0) :
    uD1 * uT ε = uT ε * uD1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD1, uT, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_uT (h2 : (2 : K) = 0) (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0) :
    (uT ε).det = 1 := by
  simp [uT, det_fin_three]
  linear_combination ((-3) + (3) * ε ^ 3) * hΦ + ((1) + (1) * ε ^ 3) * h2

theorem hΦ_pow9 (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0) : ε ^ 9 = 1 := by
  linear_combination (ε ^ 3 - 1) * hΦ

theorem smul_diag_eq_one (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0) :
    ε ^ 6 • (Matrix.diagonal (fun _ : Fin 3 => ε ^ 3)) = (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h9 := hΦ_pow9 hΦ
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [← pow_add, show 6 + 3 = 9 from rfl, h9]
  · simp [Matrix.diagonal_apply, hij, Matrix.one_apply]

@[expose] def glT (h2 : (2 : K) = 0) (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0) : GL (Fin 3) K :=
  ⟨uT ε, ε ^ 6 • (uT ε * uT ε), by
    rw [Matrix.mul_smul, ← mul_assoc, uT_cubed h2 hΦ]
    exact smul_diag_eq_one hΦ, by
    rw [Matrix.smul_mul, mul_assoc, ← mul_assoc, uT_cubed h2 hΦ]
    exact smul_diag_eq_one hΦ⟩

theorem map_uT (hfrob : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q) (hq9 : ε ^ q = ε ^ 8) :
    (uT ε).map (· ^ q) = uTc ε := by
  have h7 : (ε ^ 7) ^ q = ε ^ 56 := by
    rw [← pow_mul, mul_comm, pow_mul, hq9, ← pow_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT, uTc, hfrob, h7, hq9]

theorem glT_mem_su (h2 : (2 : K) = 0) (hΦ : ε ^ 6 + ε ^ 3 + 1 = 0)
    (hfrob : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q) (hq9 : ε ^ q = ε ^ 8) :
    (glT h2 hΦ : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨det_uT h2 hΦ, ?_⟩
  show ((uT ε).map (· ^ q))ᵀ * uT ε = 1
  rw [map_uT hfrob hq9]
  exact uT_unitary h2 hΦ

theorem det_uD1_of_two (h2 : (2 : K) = 0) : (uD1 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [uD1, det_fin_three]
  linear_combination (-1) * h2

theorem glU1_mem_su_of_two (h2 : (2 : K) = 0) (hq : q ≠ 0) :
    (glU1 : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨det_uD1_of_two h2, ?_⟩
  show ((uD1 : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * uD1 = 1
  have : (uD1 : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = uD1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uD1, zero_pow hq]
  rw [this, uD1_transpose]
  exact uD1_mul_self

theorem uT_ne_zero (h2 : (2 : K) = 0) (h0 : ε ≠ 0) (h6 : ε ^ 6 ≠ 1) : ε + ε ^ 7 ≠ 0 := by
  intro h
  apply h6
  have : ε * (1 + ε ^ 6) = 0 := by linear_combination h
  have h1 := (mul_eq_zero.1 this).resolve_left h0
  linear_combination h1 - h2

end Torus

theorem threeTwoWitness_psu_three_cube {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hfo : Odd f) (h3f : 3 ∣ f) :
    ThreeTwoWitness (StatedProj (StatedSU 3 (2 ^ f) K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hfrob : ∀ x y : K, (x + y) ^ (2 ^ f) = x ^ (2 ^ f) + y ^ (2 ^ f) :=
    fun x y => add_pow_char_pow x y 2 f
  obtain ⟨j, hj⟩ := hfo
  obtain ⟨k, hk⟩ := h3f
  have hmod : 2 ^ f % 9 = 8 := by
    have hk' : k = 2 * (k / 2) + 1 := by omega
    have : f = 3 * (2 * (k / 2) + 1) := by omega
    rw [this, pow_mul, pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hN : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  have h9 : 9 ∣ Nat.card Kˣ := by
    rw [hN]
    exact Dvd.dvd.mul_right (by omega) _
  obtain ⟨g, hg⟩ := exists_units_orderOf_eq h9
  have hg9 : g ^ 9 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg3 : g ^ 3 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hg] at this
    omega
  have hg6 : g ^ 6 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hg] at this
    omega
  set ε : K := (g : K) with hε
  have hε9 : ε ^ 9 = 1 := by rw [hε, ← Units.val_pow_eq_pow_val, hg9, Units.val_one]
  have hε3 : ε ^ 3 ≠ 1 := fun h => hg3 (Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h))
  have hε6 : ε ^ 6 ≠ 1 := fun h => hg6 (Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h))
  have hΦ : ε ^ 6 + ε ^ 3 + 1 = 0 := by
    have h : (ε ^ 3 - 1) * (ε ^ 6 + ε ^ 3 + 1) = 0 := by linear_combination hε9
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hε3)
  have hq9 : ε ^ (2 ^ f) = ε ^ 8 := by
    have hd : 2 ^ f = 9 * (2 ^ f / 9) + 8 := by omega
    rw [hd, pow_add, pow_mul, hε9, one_pow, one_mul]
  have hq : 2 ^ f ≠ 0 := by positivity
  refine threeTwoWitness_statedProj_commuting_mod glU1 (glT h2 hΦ) (glU1_mem_su_of_two h2 hq)
    (glT_mem_su h2 hΦ hfrob hq9) (Units.ext uD1_mul_self) ?_ ⟨g ^ 3, ?_⟩ ?_ ?_
  · intro u hu
    have e := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hu
    simp [glU1, uD1, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
  · refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val]
    show uT ε ^ 3 = ((Matrix.GeneralLinearGroup.scalar (Fin 3) (g ^ 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)
    rw [pow_succ, pow_two, uT_cubed h2 hΦ, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Units.val_pow_eq_pow_val]
  · intro u hu
    have e := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hu
    simp [glT, uT, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
    exact uT_ne_zero h2 g.ne_zero hε6 (by first | exact e | exact e.symm)
  · exact Units.ext (uD1_uT_comm h2 hΦ)

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
