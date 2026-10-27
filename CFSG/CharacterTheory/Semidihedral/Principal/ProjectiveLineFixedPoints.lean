module

public import CFSG.CharacterTheory.Semidihedral.Principal.ProjectiveLinearTwoPrincipalCharacters

public section

namespace CFSG.Semidihedral.Principal

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter

universe u

variable {F : Type u} [Field F]

section Matrices

theorem coordinateGLAction_eq_one_of_mem_center {A : Matrix.GeneralLinearGroup (Fin 2) F}
    (hA : A ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F)) :
    coordinateGLAction F A = 1 := by
  change coordinatePGLAction F (Matrix.ProjGenLinGroup.mk A) = 1
  rw [Matrix.ProjGenLinGroup.mk_eq_one.mpr hA, map_one]

theorem coordinateGLAction_scalar (c : Fˣ) :
    coordinateGLAction F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
  change coordinatePGLAction F (Matrix.ProjGenLinGroup.mk _) = 1
  rw [Matrix.ProjGenLinGroup.mk_scalar, map_one]

theorem coordinateGLAction_toGL (X : Matrix.SpecialLinearGroup (Fin 2) F) :
    coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) =
      coordinatePSLAction F (psl2QuotientMap F X) := by
  change coordinatePGLAction F (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL X)) = _
  rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL]
  rfl

theorem exists_coordinateGLAction_eq {d : Equiv.Perm (Omega F)} (hd : d ∈ coordinateD F) :
    ∃ A : Matrix.GeneralLinearGroup (Fin 2) F, coordinateGLAction F A = d := by
  rw [← coordinateGLAction_range] at hd
  exact hd

theorem mul_self_mem_coordinateG {d : Equiv.Perm (Omega F)} (hd : d ∈ coordinateD F) :
    d * d ∈ coordinateG F := by
  obtain ⟨A, rfl⟩ := exists_coordinateGLAction_eq hd
  have hsq : Matrix.ProjGenLinGroup.mk (A * A) ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, map_mul, Units.val_mul]
    exact ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := hsq
  rw [← map_mul, ← coordinatePSLAction_range_eq_G]
  refine ⟨g, ?_⟩
  change coordinatePSLAction F g = coordinatePGLAction F (Matrix.ProjGenLinGroup.mk (A * A))
  rw [← hg, coordinatePGLAction_toPGL]

theorem exists_coordinateG_infinity_zero {x y : Omega F} (hxy : x ≠ y) :
    ∃ g ∈ coordinateG F, g none = x ∧ g (some 0) = y := by
  obtain ⟨g, hg⟩ := coordinateG_orbit_infinity F x
  obtain ⟨b, hb⟩ : ∃ b, (g : Equiv.Perm (Omega F))⁻¹ y = some b := by
    cases h : (g : Equiv.Perm (Omega F))⁻¹ y with
    | none => exact absurd (hg.symm.trans (Equiv.Perm.inv_eq_iff_eq.mp h).symm) hxy
    | some b => exact ⟨b, rfl⟩
  refine ⟨g * translation F b, (coordinateG F).mul_mem g.2
    (Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, translation_none, hg]
  · rw [Equiv.Perm.mul_apply, translation_some, zero_add]
    exact (Equiv.Perm.inv_eq_iff_eq.mp hb).symm

theorem sq_eq_one_of_swap {d : Equiv.Perm (Omega F)} (hd : d ∈ coordinateD F)
    {x y : Omega F} (hxy : x ≠ y) (hdx : d x = y) (hdy : d y = x) : d * d = 1 := by
  obtain ⟨g, hg, hg0, hg1⟩ := exists_coordinateG_infinity_zero hxy
  have hd' : g⁻¹ * d * g ∈ coordinateD F :=
    (coordinateD F).mul_mem ((coordinateD F).mul_mem
      ((coordinateD F).inv_mem (coordinateG_le_D F hg)) hd) (coordinateG_le_D F hg)
  obtain ⟨A, hA⟩ := exists_coordinateGLAction_eq hd'
  have hinf : coordinateGLAction F A none = some 0 := by
    rw [hA, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg0, hdx]
    exact Equiv.Perm.inv_eq_iff_eq.mpr hg1.symm
  have hzero : coordinateGLAction F A (some 0) = none := by
    rw [hA, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg1, hdy]
    exact Equiv.Perm.inv_eq_iff_eq.mpr hg0.symm
  have h10 : A.val 1 0 ≠ 0 := by
    intro h
    rw [coordinateGLAction_infinity_lower_left_zero F A h] at hinf
    simp at hinf
  have h00 : A.val 0 0 = 0 := by
    rw [coordinateGLAction_infinity F A h10, Option.some.injEq, div_eq_zero_iff] at hinf
    exact hinf.resolve_right h10
  have h11 : A.val 1 1 = 0 := by
    by_contra h
    rw [coordinateGLAction_finite F A 0 (by simpa using h)] at hzero
    simp at hzero
  have hcen : A * A ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨A.val 0 1 * A.val 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11, mul_comm]
  have h2 : (g⁻¹ * d * g) * (g⁻¹ * d * g) = 1 := by
    rw [← hA, ← map_mul, coordinateGLAction_eq_one_of_mem_center hcen]
  calc d * d = g * ((g⁻¹ * d * g) * (g⁻¹ * d * g)) * g⁻¹ := by group
    _ = 1 := by rw [h2, mul_one, mul_inv_cancel]

theorem sl_mem_center_of_mul_self_eq_one (hF : ringChar F ≠ 2)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (hX : (X : Matrix (Fin 2) (Fin 2) F) * X = 1) :
    X ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) F).det = 1 := X.2
  rw [Matrix.det_fin_two] at hdet
  have h00 := congrFun (congrFun hX 0) 0
  have h01 := congrFun (congrFun hX 0) 1
  have h10 := congrFun (congrFun hX 1) 0
  have h11 := congrFun (congrFun hX 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  set a := (X : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (X : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (X : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (X : Matrix (Fin 2) (Fin 2) F) 1 1
  have hs : a + d ≠ 0 := by
    intro h
    exact Ring.neg_one_ne_one_of_char_ne_two hF (by linear_combination h00 + hdet - a * h)
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hs
  have had : d = a := by
    have : (a - d) * (a + d) = 0 := by
      rw [hb, hc] at h00 h11
      linear_combination h00 - h11
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)).symm
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨a, ?_, ?_⟩
  · rw [Fintype.card_fin, sq]
    rw [hb] at h00
    linear_combination h00
  · ext i j
    fin_cases i <;> fin_cases j
    exacts [rfl, hb.symm, hc.symm, had.symm]

theorem exists_sl_sq_neg_one_of_involution (hF : ringChar F ≠ 2) {t : Equiv.Perm (Omega F)}
    (ht : t ∈ coordinateG F) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ X : Matrix.SpecialLinearGroup (Fin 2) F, (X : Matrix (Fin 2) (Fin 2) F) * X = -1 ∧
      t = coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) := by
  rw [← coordinatePSLAction_range_eq_G] at ht
  obtain ⟨g, rfl⟩ := ht
  obtain ⟨X, rfl⟩ := psl2QuotientMap_surjective g
  refine ⟨X, ?_, (coordinateGLAction_toGL X).symm⟩
  have hcen : X * X ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have h : psl2QuotientMap F (X * X) = 1 := by
      apply coordinatePSLAction_injective F
      rw [map_mul, map_mul, ht2, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨s, hs, hsX⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  rw [Fintype.card_fin, sq] at hs
  rcases mul_self_eq_one_iff.mp hs with rfl | rfl
  · refine absurd ?_ ht1
    have hX : X ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      sl_mem_center_of_mul_self_eq_one hF X (by
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← hsX, map_one])
    have h1 : psl2QuotientMap F X = 1 := (QuotientGroup.eq_one_iff X).mpr hX
    rw [h1, map_one]
  · rw [← Matrix.SpecialLinearGroup.coe_mul, ← hsX, map_neg, map_one]

end Matrices

section Rotations

theorem exists_pow_eq_pow_half {G : Type*} [Monoid G] {r : G} {M : ℕ} (hM : ∃ m, M = 2 ^ m)
    (hrM : orderOf r = M) {j : ℕ} (hj : r ^ j ≠ 1) : ∃ n, (r ^ j) ^ n = r ^ (M / 2) := by
  obtain ⟨m, rfl⟩ := hM
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj (pow_zero r)
  obtain ⟨a, u, ⟨v, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hj0
  have ham : a < m := by
    by_contra h
    apply hj
    rw [← orderOf_dvd_iff_pow_eq_one, hrM]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (not_lt.mp h)) _
  obtain ⟨k, rfl⟩ : ∃ k, m = a + k + 1 := ⟨m - a - 1, by omega⟩
  refine ⟨2 ^ k, ?_⟩
  have hhalf : 2 ^ (a + k + 1) / 2 = 2 ^ (a + k) := by
    rw [pow_succ, Nat.mul_div_cancel _ two_pos]
  have hexp : 2 ^ a * (2 * v + 1) * 2 ^ k = 2 ^ (a + k + 1) * v + 2 ^ (a + k) := by ring
  rw [hhalf, ← pow_mul, hexp, pow_add, pow_mul, ← hrM, pow_orderOf_eq_one, one_pow, one_mul]

theorem apply_eq_self_of_pow_half_apply_eq_self [Finite F] (hF : ringChar F ≠ 2)
    {r : Equiv.Perm (Omega F)} (hr : r ∈ coordinateD F) {M : ℕ} (hM : ∃ m, M = 2 ^ m)
    (hM4 : 4 ≤ M) (hrM : orderOf r = M) {x : Omega F} (hx : (r ^ (M / 2)) x = x) :
    r x = x := by
  have : Fintype F := Fintype.ofFinite F
  have h4 : 4 ∣ M := by
    obtain ⟨m, rfl⟩ := hM
    have hm : 2 ≤ m := by
      by_contra h
      have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos (by omega)
      omega
    exact pow_dvd_pow 2 hm
  have htG : r ^ (M / 2) ∈ coordinateG F := by
    rw [show M / 2 = M / 4 + M / 4 by omega, pow_add]
    exact mul_self_mem_coordinateG (pow_mem hr _)
  have ht2 : r ^ (M / 2) * r ^ (M / 2) = 1 := by
    rw [← pow_add, show M / 2 + M / 2 = M by omega, ← hrM, pow_orderOf_eq_one]
  have ht1 : r ^ (M / 2) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  obtain ⟨X, hX, htX⟩ := exists_sl_sq_neg_one_of_involution hF htG ht2 ht1
  have hcard := card_fixed_sl_sq_neg_one hF X hX
  rw [← htX] at hcard
  have hpos : 0 < Nat.card {z // (r ^ (M / 2)) z = z} := by
    have : Nonempty {z // (r ^ (M / 2)) z = z} := ⟨⟨x, hx⟩⟩
    exact Nat.card_pos
  have hcard2 : Nat.card {z // (r ^ (M / 2)) z = z} = 2 := by
    rw [hcard] at hpos ⊢
    split_ifs at hpos ⊢ <;> omega
  have hcomm : ∀ z, (r ^ (M / 2)) z = z → (r ^ (M / 2)) (r z) = r z := by
    intro z hz
    rw [← Equiv.Perm.mul_apply, ← (Commute.self_pow r (M / 2)).eq, Equiv.Perm.mul_apply, hz]
  by_contra hrx
  have hy := hcomm x hx
  have hry := hcomm _ hy
  have hrrx : r (r x) = x := by
    by_contra hne
    obtain ⟨w, -, hw⟩ :=
      (Nat.card_eq_two_iff' (⟨x, hx⟩ : {z // (r ^ (M / 2)) z = z})).mp hcard2
    have h1 := hw ⟨r x, hy⟩ fun h => hrx (congrArg Subtype.val h)
    have h2 := hw ⟨r (r x), hry⟩ fun h => hne (congrArg Subtype.val h)
    exact hrx (r.injective (congrArg Subtype.val (h2.trans h1.symm)))
  have hsq := sq_eq_one_of_swap hr (Ne.symm hrx) rfl hrrx
  have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  rw [hrM] at hdvd
  have := Nat.le_of_dvd two_pos hdvd
  omega

theorem fixed_iff_of_two_power_order_of_pow_ne_one [Finite F] (hF : ringChar F ≠ 2)
    {r : Equiv.Perm (Omega F)} (hr : r ∈ coordinateD F) {M : ℕ} (hM : ∃ m, M = 2 ^ m)
    (hrM : orderOf r = M) {j : ℕ} (hj : r ^ j ≠ 1) (x : Omega F) :
    (r ^ j) x = x ↔ (r ^ (M / 2)) x = x := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_pow_eq_pow_half hM hrM hj
    rw [← hn]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h n
  · intro h
    by_cases hM4 : 4 ≤ M
    · exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
        (apply_eq_self_of_pow_half_apply_eq_self hF hr hM hM4 hrM h) j
    · obtain ⟨m, rfl⟩ := hM
      have hm : m ≤ 1 := by
        by_contra hm
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (by omega)
        omega
      interval_cases m
      · rw [pow_zero, orderOf_eq_one_iff] at hrM
        exact absurd (by rw [hrM, one_pow]) hj
      · exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (by simpa using h) j

theorem fixed_iff_of_two_power_order [Finite F] (hF : ringChar F ≠ 2)
    {r : Equiv.Perm (Omega F)} (hr : r ∈ coordinateD F) {M : ℕ} (hM : ∃ m, M = 2 ^ m)
    (hM4 : 4 ≤ M) (hrM : orderOf r = M) (j : ℕ) (hj1 : 1 ≤ j) (hjM : j < M) (x : Omega F) :
    (r ^ j) x = x ↔ (r ^ (M / 2)) x = x :=
  ⟨(fixed_iff_of_two_power_order_of_pow_ne_one hF hr hM hrM
      (pow_ne_one_of_lt_orderOf (by omega) (hrM ▸ hjM)) x).mp,
    fun h => Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
      (apply_eq_self_of_pow_half_apply_eq_self hF hr hM hM4 hrM h) j⟩

theorem card_fixed_pow_eq_of_two_power_order [Finite F] (hF : ringChar F ≠ 2)
    {r : Equiv.Perm (Omega F)} (hr : r ∈ coordinateD F) {M : ℕ} (hM : ∃ m, M = 2 ^ m)
    (hM4 : 4 ≤ M) (hrM : orderOf r = M) (j : ℕ) (hj1 : 1 ≤ j) (hjM : j < M) :
    Nat.card {x : Omega F // (r ^ j) x = x} = Nat.card {x : Omega F // (r ^ (M / 2)) x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight
    (fixed_iff_of_two_power_order hF hr hM hM4 hrM j hj1 hjM))

end Rotations

section Translations

theorem translation_zero : translation F 0 = 1 := by
  ext x
  cases x <;> simp

theorem translation_add (a b : F) :
    translation F (a + b) = translation F a * translation F b := by
  ext x
  cases x with
  | none => rfl
  | some x =>
    rw [Equiv.Perm.mul_apply, translation_some, translation_some, translation_some, add_assoc,
      add_comm b a]

theorem translation_pow (b : F) (n : ℕ) : translation F b ^ n = translation F (n • b) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, translation_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, translation_add]

theorem card_fixed_translation {b : F} (hb : b ≠ 0) :
    Nat.card {x : Omega F // translation F b x = x} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨none, rfl⟩, ?_⟩
  rintro ⟨x, hx⟩
  cases x with
  | none => rfl
  | some x =>
    rw [translation_some, Option.some.injEq] at hx
    exact absurd (by simpa using hx) hb

theorem odd_orderOf_translation (hq : Odd (Nat.card F)) (b : F) :
    Odd (orderOf (translation F b)) :=
  hq.of_dvd_nat (orderOf_dvd_of_pow_eq_one (by
    rw [translation_pow, card_nsmul_eq_zero', translation_zero]))

end Translations

end CFSG.Semidihedral.Principal
