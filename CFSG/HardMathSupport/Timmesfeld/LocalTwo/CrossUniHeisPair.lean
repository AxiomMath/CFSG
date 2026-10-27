module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniPlane

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Power

theorem matrix_pow_mul_of_comm {m : ℕ} (X Y : Matrix (Fin m) (Fin m) K) (κ : K)
    (hXY : X * Y = κ • (Y * X)) (k : ℕ) : X ^ k * Y = κ ^ k • (Y * X ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc X ^ (k + 1) * Y = X * (X ^ k * Y) := by rw [pow_succ', mul_assoc]
      _ = X * (κ ^ k • (Y * X ^ k)) := by rw [ih]
      _ = κ ^ k • ((X * Y) * X ^ k) := by rw [Matrix.mul_smul, ← Matrix.mul_assoc]
      _ = κ ^ k • (κ • (Y * X) * X ^ k) := by rw [hXY]
      _ = κ ^ (k + 1) • (Y * X ^ (k + 1)) := by
          rw [Matrix.smul_mul, smul_smul, ← pow_succ, pow_succ' X k]
          simp only [Matrix.mul_assoc]

theorem matrix_pow_mul_comm {m : ℕ} (X Y : Matrix (Fin m) (Fin m) K) (κ : K)
    (hXY : X * Y = κ • (Y * X)) (k : ℕ) :
    (Y * X) ^ k = κ ^ (Finset.sum (Finset.range k) id) • (Y ^ k * X ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := matrix_pow_mul_of_comm X Y κ hXY k
    calc (Y * X) ^ (k + 1) = (Y * X) ^ k * (Y * X) := pow_succ _ _
      _ = κ ^ (Finset.sum (Finset.range k) id) • (Y ^ k * X ^ k) * (Y * X) := by rw [ih]
      _ = κ ^ (Finset.sum (Finset.range k) id) • (Y ^ k * (X ^ k * Y) * X) := by
          rw [Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = κ ^ (Finset.sum (Finset.range k) id) •
            (Y ^ k * (κ ^ k • (Y * X ^ k)) * X) := by rw [h1]
      _ = κ ^ (Finset.sum (Finset.range (k + 1)) id) • (Y ^ (k + 1) * X ^ (k + 1)) := by
          rw [Finset.sum_range_succ, id, pow_add, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
            pow_succ Y k, pow_succ X k]
          simp only [Matrix.mul_assoc, id]

end Power

theorem sum_range_id_prime {κ : K} (hp : p.Prime) (hp2 : p ≠ 2) (hκ : κ ^ p = 1) :
    κ ^ (Finset.sum (Finset.range p) id) = 1 := by
  obtain ⟨r, hr⟩ := hp.odd_of_ne_two hp2
  have h1 := Finset.sum_range_id_mul_two p
  have h2 : Finset.sum (Finset.range p) id = p * r := by
    simp only [id] at h1 ⊢
    rw [hr] at h1 ⊢
    simp only [Nat.add_sub_cancel] at h1
    nlinarith
  rw [h2, pow_mul, hκ, one_pow]

section Comm

variable {m : ℕ}

theorem gl_comm_matrix {X Y : GL (Fin m) K} {κ : Kˣ}
    (hXY : X * Y = Y * X * GeneralLinearGroup.scalar (Fin m) κ) :
    ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) * (Y : Matrix (Fin m) (Fin m) K) =
      (κ : K) • (((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  have := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) hXY
  simp only [Units.val_mul, scalar_coe_eq_smul_one] at this
  rw [this, Matrix.mul_smul, Matrix.mul_one]

theorem swap_comm {X Y : GL (Fin m) K} {κ : Kˣ}
    (hXY : X * Y = Y * X * GeneralLinearGroup.scalar (Fin m) κ) :
    Y * X = X * Y * GeneralLinearGroup.scalar (Fin m) κ⁻¹ := by
  rw [hXY, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem rescale_left_comm {X Y : GL (Fin m) K} {κ : Kˣ}
    (hXY : X * Y = Y * X * GeneralLinearGroup.scalar (Fin m) κ) (u : Kˣ) :
    (GeneralLinearGroup.scalar (Fin m) u * X) * Y =
      Y * (GeneralLinearGroup.scalar (Fin m) u * X) * GeneralLinearGroup.scalar (Fin m) κ := by
  calc (GeneralLinearGroup.scalar (Fin m) u * X) * Y
      = GeneralLinearGroup.scalar (Fin m) u * (X * Y) := by rw [mul_assoc]
    _ = GeneralLinearGroup.scalar (Fin m) u * (Y * X * GeneralLinearGroup.scalar (Fin m) κ) := by
        rw [hXY]
    _ = (GeneralLinearGroup.scalar (Fin m) u * Y) * X * GeneralLinearGroup.scalar (Fin m) κ := by
        simp only [mul_assoc]
    _ = (Y * GeneralLinearGroup.scalar (Fin m) u) * X * GeneralLinearGroup.scalar (Fin m) κ := by
        rw [GeneralLinearGroup.scalar_commute u Y]
    _ = Y * (GeneralLinearGroup.scalar (Fin m) u * X) * GeneralLinearGroup.scalar (Fin m) κ := by
        simp only [mul_assoc]

theorem rescale_right_comm {X Y : GL (Fin m) K} {κ : Kˣ}
    (hXY : X * Y = Y * X * GeneralLinearGroup.scalar (Fin m) κ) (u : Kˣ) :
    X * (GeneralLinearGroup.scalar (Fin m) u * Y) =
      (GeneralLinearGroup.scalar (Fin m) u * Y) * X * GeneralLinearGroup.scalar (Fin m) κ := by
  calc X * (GeneralLinearGroup.scalar (Fin m) u * Y)
      = (X * GeneralLinearGroup.scalar (Fin m) u) * Y := by rw [mul_assoc]
    _ = (GeneralLinearGroup.scalar (Fin m) u * X) * Y := by
        rw [GeneralLinearGroup.scalar_commute u X]
    _ = GeneralLinearGroup.scalar (Fin m) u * (X * Y) := by rw [mul_assoc]
    _ = GeneralLinearGroup.scalar (Fin m) u * (Y * X * GeneralLinearGroup.scalar (Fin m) κ) := by
        rw [hXY]
    _ = (GeneralLinearGroup.scalar (Fin m) u * Y) * X * GeneralLinearGroup.scalar (Fin m) κ := by
        simp only [mul_assoc]

end Comm

section Pair

theorem exists_pow_scalar_unitary (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {X : primeFormUnitary h (idGram K n)}
    (hX : primeFormConjHom h (idGram K n) X ^ p = 1) :
    ∃ a : Kˣ, h.norm (a : K) = 1 ∧
      (X : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) a := by
  have h1 : primeFormConjHom h (idGram K n) (X ^ p) = 1 := by rw [map_pow, hX]
  obtain ⟨a, ha, hA'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
  exact ⟨a, (pow_succ_eq_one_iff_norm h a).mp ha, by simpa using hA'⟩

theorem norm_inv_unit_eq_one {u : Kˣ} (hu : h.norm (u : K) = 1) : h.norm ((u⁻¹ : Kˣ) : K) = 1 := by
  simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hu

theorem exists_split_heis_pair (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {A B : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hAB : (A : GL (Fin n) K) * B = B * A * GeneralLinearGroup.scalar (Fin n) c)
    (hAp : primeFormConjHom h (idGram K n) A ^ p = 1)
    (hBp : primeFormConjHom h (idGram K n) B ^ p = 1)
    (hA1 : primeFormConjHom h (idGram K n) A ≠ 1)
    (hBA : primeFormConjHom h (idGram K n) B ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) A)) :
    ∃ (A0 B0 : primeFormUnitary h (idGram K n)) (c' : Kˣ), c' ≠ 1 ∧ c' ^ p = 1 ∧
      (A0 : GL (Fin n) K) * B0 = B0 * A0 * GeneralLinearGroup.scalar (Fin n) c' ∧
      A0 ^ p = 1 ∧ primeFormConjHom h (idGram K n) A0 ≠ 1 ∧
      primeFormConjHom h (idGram K n) A0 ∈ Subgroup.closure
        {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} ∧
      primeFormConjHom h (idGram K n) B0 ∈ Subgroup.closure
        {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} := by
  classical
  have := h.finite
  set ρ := primeFormConjHom h (idGram K n) with hρ
  obtain ⟨a, han, ha⟩ := exists_pow_scalar_unitary hn hne hAp
  obtain ⟨b, hbn, hb⟩ := exists_pow_scalar_unitary hn hne hBp
  have hAE : ρ A ∈ Subgroup.closure {ρ A, ρ B} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hBE : ρ B ∈ Subgroup.closure {ρ A, ρ B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hB1 : ρ B ≠ 1 := fun h1 => hBA (h1 ▸ one_mem _)
  by_cases hap : ∃ u : Kˣ, u ^ p = a
  · obtain ⟨u, rfl⟩ := hap
    have hun : h.norm (u : K) = 1 := norm_eq_one_of_pow_norm hp hp2 hpq (by simpa using han)
    have hu'n := norm_inv_unit_eq_one hun
    refine ⟨scalarU h n u⁻¹ hu'n * A, B, c, hc1, hcp, ?_, rescale_pow_eq_one hn hne hu'n ha, ?_,
      ?_, hBE⟩
    · rw [Subgroup.coe_mul, coe_scalarU]
      exact rescale_left_comm hAB u⁻¹
    · rw [map_mul, conjHom_scalarU hn hne, one_mul]; exact hA1
    · rw [map_mul, conjHom_scalarU hn hne, one_mul]; exact hAE
  · push Not at hap
    by_cases hbp : ∃ v : Kˣ, v ^ p = b
    · obtain ⟨v, rfl⟩ := hbp
      have hvn : h.norm (v : K) = 1 := norm_eq_one_of_pow_norm hp hp2 hpq (by simpa using hbn)
      have hv'n := norm_inv_unit_eq_one hvn
      refine ⟨scalarU h n v⁻¹ hv'n * B, A, c⁻¹, inv_ne_one.mpr hc1, by rw [inv_pow, hcp, inv_one],
        ?_, rescale_pow_eq_one hn hne hv'n hb, ?_, ?_, hAE⟩
      · rw [Subgroup.coe_mul, coe_scalarU]
        exact rescale_left_comm (swap_comm hAB) v⁻¹
      · rw [map_mul, conjHom_scalarU hn hne, one_mul]; exact hB1
      · rw [map_mul, conjHom_scalarU hn hne, one_mul]; exact hBE
    · push Not at hbp
      obtain ⟨k, d, hbk⟩ := exists_zpow_mul_pow_of_forall_pow_ne hp hap b
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      set m : ℕ := Int.toNat ((-k) % p) with hm
      have hm' : (m : ℤ) = (-k) % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
      obtain ⟨t, ht⟩ : ∃ t : ℤ, k + m = p * t := by
        refine ⟨-((-k) / p), ?_⟩
        rw [hm', Int.emod_def]
        ring
      set w : Kˣ := a ^ t * d with hw
      have hwp : w ^ p = b * a ^ m := by
        calc w ^ p = a ^ (t * (p : ℤ)) * d ^ p := by
              rw [hw, mul_pow, ← zpow_natCast (a ^ t) p, ← _root_.zpow_mul]
          _ = a ^ ((p : ℤ) * t) * d ^ p := by rw [mul_comm t]
          _ = a ^ (k + (m : ℤ)) * d ^ p := by rw [ht]
          _ = a ^ k * a ^ m * d ^ p := by rw [_root_.zpow_add, zpow_natCast]
          _ = b * a ^ m := by rw [hbk, mul_right_comm]
      have hbq : b ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h b).mpr hbn
      have haq : a ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h a).mpr han
      have hwn : h.norm (w : K) = 1 := by
        refine norm_eq_one_of_pow_norm hp hp2 hpq ?_
        rw [hwp]
        refine (pow_succ_eq_one_iff_norm h _).mp ?_
        rw [mul_pow, hbq, ← pow_mul, mul_comm m, pow_mul, haq, one_pow, one_mul]
      have hw'n := norm_inv_unit_eq_one hwn
      set Z : primeFormUnitary h (idGram K n) := B * A ^ m with hZ
      have hAmB : (A : GL (Fin n) K) ^ m * B =
          B * (A : GL (Fin n) K) ^ m * GeneralLinearGroup.scalar (Fin n) (c ^ m) :=
        scalar_pow_conj _ _ c hAB m
      have hZp : (Z : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) (w ^ p) := by
        have hc' := gl_comm_matrix hAmB
        have hκ : (((c ^ m : Kˣ)) : K) ^ p = 1 := by
          rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hcp, one_pow,
            Units.val_one]
        have hmat := matrix_pow_mul_comm
          ((((A : GL (Fin n) K) ^ m : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
          ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (((c ^ m : Kˣ)) : K) hc' p
        rw [sum_range_id_prime hp hp2 hκ, one_smul] at hmat
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, hZ, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul]
        rw [hmat, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← pow_mul,
          mul_comm m, pow_mul, ha, hb, ← map_pow, ← Units.val_mul, ← map_mul, hwp]
      have hAZ : (A : GL (Fin n) K) * (Z : GL (Fin n) K) =
          (Z : GL (Fin n) K) * A * GeneralLinearGroup.scalar (Fin n) c := by
        rw [hZ, Subgroup.coe_mul, Subgroup.coe_pow]
        calc (A : GL (Fin n) K) * ((B : GL (Fin n) K) * (A : GL (Fin n) K) ^ m)
            = ((A : GL (Fin n) K) * B) * (A : GL (Fin n) K) ^ m := by rw [mul_assoc]
          _ = (B * A * GeneralLinearGroup.scalar (Fin n) c) * (A : GL (Fin n) K) ^ m := by
              rw [hAB]
          _ = B * A * ((A : GL (Fin n) K) ^ m * GeneralLinearGroup.scalar (Fin n) c) := by
              rw [mul_assoc, GeneralLinearGroup.scalar_commute c ((A : GL (Fin n) K) ^ m)]
          _ = B * ((A : GL (Fin n) K) * (A : GL (Fin n) K) ^ m) *
                GeneralLinearGroup.scalar (Fin n) c := by simp only [mul_assoc]
          _ = ((B : GL (Fin n) K) * (A : GL (Fin n) K) ^ m) * A *
                GeneralLinearGroup.scalar (Fin n) c := by
              rw [← pow_succ', pow_succ]
              simp only [mul_assoc]
      have hρZ : ρ Z = ρ B * ρ A ^ m := by rw [hZ, map_mul, map_pow]
      refine ⟨scalarU h n w⁻¹ hw'n * Z, A, c⁻¹, inv_ne_one.mpr hc1, by rw [inv_pow, hcp, inv_one],
        ?_, rescale_pow_eq_one hn hne hw'n hZp, ?_, ?_, hAE⟩
      · rw [Subgroup.coe_mul, coe_scalarU]
        exact rescale_left_comm (swap_comm hAZ) w⁻¹
      · rw [map_mul, conjHom_scalarU hn hne, one_mul, hρZ]
        intro h1
        apply hBA
        have : ρ B = (ρ A ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m)
      · rw [map_mul, conjHom_scalarU hn hne, one_mul, hρZ]
        exact Subgroup.mul_mem _ hBE (Subgroup.pow_mem _ hAE m)

end Pair

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
