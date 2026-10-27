module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcUNum

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace CrossExcU

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix Subgroup

section Matrices

variable {ℓ f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def leviMat' (A D : Matrix (Fin r) (Fin r) K) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  Matrix.fromBlocks A 0 0 (Matrix.fromBlocks 1 0 0 D)

theorem leviMat'_mulVec (A D : Matrix (Fin r) (Fin r) K) (v z : Fin r → K) (w : Fin ε → K) :
    leviMat' (ε := ε) A D *ᵥ (Sum.elim v (Sum.elim w z) : HypIndex r ε → K) =
      Sum.elim (A *ᵥ v) (Sum.elim w (D *ᵥ z)) := by
  rw [leviMat', Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
  simp

theorem leviMat'_mul (A D A' D' : Matrix (Fin r) (Fin r) K) :
    leviMat' (ε := ε) A D * leviMat' A' D' = leviMat' (A * A') (D * D') := by
  simp [leviMat', Matrix.fromBlocks_multiply]

theorem leviMat'_one : leviMat' (ε := ε) (1 : Matrix (Fin r) (Fin r) K) 1 = 1 := by
  simp [leviMat', Matrix.fromBlocks_one]

theorem hypForm_elim (h : UnitaryFieldData ℓ f K) (x1 y1 x3 y3 : Fin r → K) (x2 y2 : Fin ε → K) :
    hypForm h r ε (Sum.elim x1 (Sum.elim x2 x3)) (Sum.elim y1 (Sum.elim y2 y3)) =
      (fun i => h.bar (x1 i)) ⬝ᵥ y3 + (fun k => h.bar (x2 k)) ⬝ᵥ y2 +
        (fun i => h.bar (x3 i)) ⬝ᵥ y1 := by
  rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [dotProduct, add_assoc]

theorem dot_bar_mulVec_mulVec (h : UnitaryFieldData ℓ f K) {M N : Matrix (Fin r) (Fin r) K}
    (hMN : (M.map h.bar)ᵀ * N = 1) (u v : Fin r → K) :
    (fun i => h.bar ((M *ᵥ u) i)) ⬝ᵥ (N *ᵥ v) = (fun i => h.bar (u i)) ⬝ᵥ v := by
  have hx : (fun a => h.bar ((M *ᵥ u) a)) = M.map h.bar *ᵥ fun a => h.bar (u a) := by
    funext a
    simp [mulVec, dotProduct, map_sum]
  rw [hx, ← vecMul_transpose (M.map h.bar), ← dotProduct_mulVec, mulVec_mulVec, hMN, one_mulVec]

theorem hypForm_leviMat' (h : UnitaryFieldData ℓ f K) {A D : Matrix (Fin r) (Fin r) K}
    (hAD : (A.map h.bar)ᵀ * D = 1) (x y : HypIndex r ε → K) :
    hypForm h r ε (leviMat' A D *ᵥ x) (leviMat' A D *ᵥ y) = hypForm h r ε x y := by
  have hDA : (D.map h.bar)ᵀ * A = 1 := by
    have h1 : ((A.map h.bar)ᵀ * D).map h.bar = 1 := by
      rw [hAD, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (A.map h.bar).map h.bar = A := by
      ext i j
      simp [UnitaryFieldData.bar_bar]
    rw [Matrix.map_mul, Matrix.transpose_map, h2] at h1
    have h3 := congrArg Matrix.transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_one] at h3
  have hx : ∃ x1 x2 x3, x = Sum.elim x1 (Sum.elim x2 x3) :=
    ⟨x ∘ Sum.inl, x ∘ Sum.inr ∘ Sum.inl, x ∘ Sum.inr ∘ Sum.inr, funext fun a => by
      rcases a with i | k | i <;> rfl⟩
  have hy : ∃ y1 y2 y3, y = Sum.elim y1 (Sum.elim y2 y3) :=
    ⟨y ∘ Sum.inl, y ∘ Sum.inr ∘ Sum.inl, y ∘ Sum.inr ∘ Sum.inr, funext fun a => by
      rcases a with i | k | i <;> rfl⟩
  obtain ⟨x1, x2, x3, rfl⟩ := hx
  obtain ⟨y1, y2, y3, rfl⟩ := hy
  rw [leviMat'_mulVec, leviMat'_mulVec, hypForm_elim, hypForm_elim,
    dot_bar_mulVec_mulVec h hAD, dot_bar_mulVec_mulVec h hDA]

@[expose] noncomputable def leviDual (h : UnitaryFieldData ℓ f K) (A : GL (Fin r) K) :
    Matrix (Fin r) (Fin r) K :=
  (((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ

theorem leviDual_mul_left (h : UnitaryFieldData ℓ f K) (A : GL (Fin r) K) :
    (((A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ * leviDual h A = 1 := by
  rw [leviDual, ← transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), transpose_one]

theorem leviDual_mul (h : UnitaryFieldData ℓ f K) (A B : GL (Fin r) K) :
    leviDual h (A * B) = leviDual h A * leviDual h B := by
  simp only [leviDual, _root_.mul_inv_rev, Units.val_mul, Matrix.map_mul, transpose_mul]

theorem leviDual_one (h : UnitaryFieldData ℓ f K) : leviDual h (1 : GL (Fin r) K) = 1 := by
  simp [leviDual, Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] noncomputable def leviMatHom (h : UnitaryFieldData ℓ f K) :
    GL (Fin r) K →* Matrix (HypIndex r ε) (HypIndex r ε) K where
  toFun A := leviMat' (A : Matrix (Fin r) (Fin r) K) (leviDual h A)
  map_one' := by simp [leviDual_one, leviMat'_one]
  map_mul' A B := by simp [leviDual_mul, leviMat'_mul]

@[expose] noncomputable def leviGL (h : UnitaryFieldData ℓ f K) :
    GL (Fin r) K →* GL (HypIndex r ε) K :=
  (leviMatHom h).toHomUnits

theorem coe_leviGL (h : UnitaryFieldData ℓ f K) (A : GL (Fin r) K) :
    ((leviGL (ε := ε) h A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      leviMat' (A : Matrix (Fin r) (Fin r) K) (leviDual h A) :=
  rfl

theorem leviGL_injective (h : UnitaryFieldData ℓ f K) :
    Function.Injective (leviGL (r := r) (ε := ε) h) := by
  intro A B hAB
  apply Units.ext
  ext i j
  have := congrFun (congrFun (congrArg (fun g : GL (HypIndex r ε) K =>
    (g : Matrix (HypIndex r ε) (HypIndex r ε) K)) hAB) (Sum.inl i)) (Sum.inl j)
  simpa [coe_leviGL, leviMat'] using this

theorem hypForm_leviGL (h : UnitaryFieldData ℓ f K) (A : GL (Fin r) K) (x y : HypIndex r ε → K) :
    hypForm h r ε (((leviGL (ε := ε) h A : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x)
      (((leviGL (ε := ε) h A : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) = hypForm h r ε x y := by
  rw [coe_leviGL]
  exact hypForm_leviMat' h (leviDual_mul_left h A) x y

theorem det_leviGL (h : UnitaryFieldData ℓ f K) (A : GL (Fin r) K) :
    ((leviGL (ε := ε) h A : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K).det =
      (A : Matrix (Fin r) (Fin r) K).det * (h.bar (A : Matrix (Fin r) (Fin r) K).det)⁻¹ := by
  rw [coe_leviGL, leviMat', Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, det_one,
    one_mul, leviDual, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  congr 2
  have h1 := congrArg Units.val (map_inv (Matrix.GeneralLinearGroup.det (n := Fin r) (R := K)) A)
  rw [Units.val_inv_eq_inv_val] at h1
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1

@[expose] noncomputable def leviNorm (h : UnitaryFieldData ℓ f K) : Kˣ →* Kˣ where
  toFun u := u * (Units.map h.bar.toMonoidHom u)⁻¹
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

@[expose] noncomputable def leviPhi (h : UnitaryFieldData ℓ f K) : GL (Fin r) K →* Kˣ :=
  (leviNorm h).comp Matrix.GeneralLinearGroup.det

theorem coe_leviPhi (h : UnitaryFieldData ℓ f K) (A : GL (Fin r) K) :
    ((leviPhi h A : Kˣ) : K) =
      (A : Matrix (Fin r) (Fin r) K).det * (h.bar (A : Matrix (Fin r) (Fin r) K).det)⁻¹ := by
  simp [leviPhi, leviNorm, Matrix.GeneralLinearGroup.val_det_apply]

theorem leviGL_mem_hypSU_iff (h : UnitaryFieldData ℓ f K) (A : GL (Fin r) K) :
    leviGL (ε := ε) h A ∈ hypSU h r ε ↔ leviPhi h A = 1 := by
  rw [mem_hypSU, det_leviGL, ← coe_leviPhi, Units.ext_iff, Units.val_one]
  exact ⟨fun hd => hd.2, fun hd => ⟨(gramForm_isometry_iff h _ _).1 (hypForm_leviGL h A), hd⟩⟩

@[expose] noncomputable def leviSUHom (h : UnitaryFieldData ℓ f K) :
    (leviPhi (r := r) h).ker →* hypSU h r ε where
  toFun A := ⟨leviGL (ε := ε) h (A : GL (Fin r) K),
    (leviGL_mem_hypSU_iff h (A : GL (Fin r) K)).2 (MonoidHom.mem_ker.1 A.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by simp)

theorem leviSUHom_injective (h : UnitaryFieldData ℓ f K) :
    Function.Injective (leviSUHom (r := r) (ε := ε) h) := by
  intro A B hAB
  apply Subtype.ext
  apply leviGL_injective (ε := ε) h
  exact congrArg Subtype.val hAB

theorem leviPhi_range_le_ker_norm (h : UnitaryFieldData ℓ f K) :
    (leviPhi (r := r) h).range ≤ (Units.map h.normHom).ker := by
  rintro _ ⟨A, rfl⟩
  rw [UnitaryFieldData.mem_ker_normUnits, coe_leviPhi]
  have hd0 : (A : Matrix (Fin r) (Fin r) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det A).ne_zero
  have hb0 : h.bar (A : Matrix (Fin r) (Fin r) K).det ≠ 0 := (map_ne_zero h.bar).2 hd0
  simp only [UnitaryFieldData.norm, map_mul, map_inv₀, h.bar_bar]
  field_simp

theorem card_range_leviPhi_dvd [Finite K] (h : UnitaryFieldData ℓ f K) :
    Nat.card (leviPhi (r := r) h).range ∣ ℓ ^ f + 1 := by
  rw [← (UnitaryFieldData.card_ker_normUnits_and_surjective h).1]
  exact Subgroup.card_dvd_of_le (leviPhi_range_le_ker_norm h)

end Matrices

section Orders

theorem crossExcU_card_GL {K : Type} [Field K] [Finite K] (r : ℕ) :
    Nat.card (GL (Fin r) K) = Nat.card K ^ (r * (r - 1) / 2) *
      ∏ j ∈ Finset.range r, (Nat.card K ^ (j + 1) - 1) := by
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  rw [Matrix.card_GL_field, hcard,
    Fin.prod_univ_eq_prod_range (fun i => Nat.card K ^ r - Nat.card K ^ i) r]
  set q := Nat.card K
  have h1 : ∀ i ∈ Finset.range r, q ^ r - q ^ i = q ^ i * (q ^ (r - i) - 1) := by
    intro i hi
    have hi' : i ≤ r := (Finset.mem_range.1 hi).le
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id]
  congr 1
  rw [← Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) r]
  refine Finset.prod_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have h2 : r - 1 - i + 1 = r - i := by omega
  simp only [h2]

@[expose] def crossExcUEvenProd (Q n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 2 n, if Even i then Q ^ i - 1 else 1

@[expose] def crossExcUOddProd (Q n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 2 n, if Odd i then Q ^ i + 1 else 1

theorem crossExcU_prod_Icc (Q n : ℕ) (hQ : 1 ≤ Q) :
    ∏ i ∈ Finset.Icc 2 n, ((Q : ℤ) ^ i - (-1) ^ i) =
      (crossExcUEvenProd Q n : ℤ) * (crossExcUOddProd Q n : ℤ) := by
  unfold crossExcUEvenProd crossExcUOddProd
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases Nat.even_or_odd i with he | ho
  · have hno : ¬ Odd i := Nat.not_odd_iff_even.2 he
    rw [if_pos he, if_neg hno, he.neg_pow, Nat.cast_sub (Nat.one_le_pow _ _ hQ)]
    push_cast
    ring
  · have hne : ¬ Even i := Nat.not_even_iff_odd.2 ho
    rw [if_neg hne, if_pos ho, ho.neg_pow]
    push_cast
    ring

theorem crossExcUEvenProd_eq (Q : ℕ) (n : ℕ) :
    crossExcUEvenProd Q n = ∏ j ∈ Finset.range (n / 2), (Q ^ (2 * (j + 1)) - 1) := by
  induction n with
  | zero => simp [crossExcUEvenProd]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [crossExcUEvenProd]
    · unfold crossExcUEvenProd at ih ⊢
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1), ih]
      rcases Nat.even_or_odd (n + 1) with he | ho
      · rw [if_pos he]
        have h2 : (n + 1) / 2 = n / 2 + 1 := by obtain ⟨k, hk⟩ := he; omega
        have h3 : 2 * (n / 2 + 1) = n + 1 := by omega
        rw [h2, Finset.prod_range_succ, h3]
      · rw [if_neg (Nat.not_even_iff_odd.2 ho), mul_one]
        have h2 : (n + 1) / 2 = n / 2 := by obtain ⟨k, hk⟩ := ho; omega
        rw [h2]

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] {r ε : ℕ}

theorem crossExcU_card_hypSU_nat (h : UnitaryFieldData ℓ f K) (hε : ε ≤ 1)
    (hn : 1 ≤ 2 * r + ε) :
    Nat.card (hypSU h r ε) = (ℓ ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) *
      (∏ j ∈ Finset.range r, ((ℓ ^ f) ^ (2 * (j + 1)) - 1)) *
        crossExcUOddProd (ℓ ^ f) (2 * r + ε) := by
  have hQ : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have h1 := (card_hypSU h hn).1
  rw [crossExcU_prod_Icc _ _ hQ, crossExcUEvenProd_eq] at h1
  have h2 : (2 * r + ε) / 2 = r := by omega
  rw [h2] at h1
  rw [mul_assoc]
  exact_mod_cast h1

theorem crossExcU_not_dvd_oddProd {p : ℕ} (hp : p.Prime) (heven : Even (unitaryOrder ℓ f p))
    (n : ℕ) : ¬ p ∣ crossExcUOddProd (ℓ ^ f) n := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hd
  obtain ⟨i, -, hdi⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hd
  by_cases ho : Odd i
  · rw [if_pos ho] at hdi
    have h1 : (((ℓ ^ f) ^ i + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hdi
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h1
    have h2 : (-((ℓ ^ f : ℕ) : ZMod p)) ^ i = 1 :=
      (Odd.neg_pow ho _).trans (neg_eq_of_add_eq_zero_right h1)
    have h3 : unitaryOrder ℓ f p ∣ i := orderOf_dvd_of_pow_eq_one h2
    exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 ((even_iff_two_dvd.1 heven).trans h3))
  · rw [if_neg ho] at hdi
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdi)

theorem crossExcU_not_dvd_succ {p : ℕ} (hp : p.Prime) (heven : Even (unitaryOrder ℓ f p)) :
    ¬ p ∣ ℓ ^ f + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hd
  have h1 : (((ℓ ^ f) + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  rw [Nat.cast_add, Nat.cast_one] at h1
  have h2 : (-((ℓ ^ f : ℕ) : ZMod p)) ^ 1 = 1 :=
    (pow_one _).trans (neg_eq_of_add_eq_zero_right h1)
  have h3 : unitaryOrder ℓ f p ∣ 1 := orderOf_dvd_of_pow_eq_one h2
  have h4 : unitaryOrder ℓ f p = 1 := Nat.dvd_one.1 h3
  rw [h4] at heven
  exact (Nat.not_even_one) heven

theorem crossExcU_not_dvd_index (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hpℓ : ¬ p ∣ ℓ) (heven : Even (unitaryOrder ℓ f p)) (hε : ε ≤ 1) (hn : 1 ≤ 2 * r + ε) :
    ¬ p ∣ (leviSUHom (r := r) (ε := ε) h).range.index := by
  set Q := ℓ ^ f with hQ
  have hpQ : ¬ p ∣ Q := fun hd => hpℓ (hp.dvd_of_dvd_pow hd)
  set M := (leviSUHom (r := r) (ε := ε) h).range with hM
  have hMcard : Nat.card M = Nat.card (leviPhi (r := r) h).ker :=
    (Nat.card_congr (MonoidHom.ofInjective (leviSUHom_injective h)).toEquiv).symm
  have h1 := Subgroup.card_ker_mul_card_range (leviPhi (r := r) h)
  have hGL := crossExcU_card_GL (K := K) r
  have hq : Nat.card K = Q ^ 2 := h.card_eq_sq
  have hGL' : Nat.card (GL (Fin r) K) =
      Q ^ (2 * (r * (r - 1) / 2)) * ∏ j ∈ Finset.range r, (Q ^ (2 * (j + 1)) - 1) := by
    rw [hGL, hq, ← pow_mul]
    simp only [← pow_mul]
  have hSU := crossExcU_card_hypSU_nat h hε hn
  have h2 := Subgroup.card_mul_index M
  set P := ∏ j ∈ Finset.range r, (Q ^ (2 * (j + 1)) - 1) with hP
  set T := crossExcUOddProd Q (2 * r + ε) with hT
  set m := Nat.card (leviPhi (r := r) h).range with hm
  set a := (2 * r + ε) * (2 * r + ε - 1) / 2 with ha
  set b := 2 * (r * (r - 1) / 2) with hb
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have key : M.index * Q ^ b = Q ^ a * T * m := by
    apply Nat.eq_of_mul_eq_mul_left hMpos
    calc Nat.card M * (M.index * Q ^ b) = (Nat.card M * M.index) * Q ^ b := by ring
      _ = Q ^ a * P * T * Q ^ b := by rw [h2, hSU]
      _ = Q ^ a * T * (Q ^ b * P) := by ring
      _ = Q ^ a * T * (Nat.card (leviPhi (r := r) h).ker * m) := by rw [h1, hGL']
      _ = Nat.card M * (Q ^ a * T * m) := by rw [hMcard]; ring
  intro hd
  have hd' : p ∣ Q ^ a * T * m := by
    rw [← key]
    exact Dvd.dvd.mul_right hd _
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h3 | h3
  · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
    · exact hpQ (hp.dvd_of_dvd_pow h4)
    · exact crossExcU_not_dvd_oddProd hp heven _ h4
  · exact crossExcU_not_dvd_succ hp heven (h3.trans (card_range_leviPhi_dvd h))

end Orders

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem crossExcU_isMulCommutative_of_not_dvd_index (S : Subgroup G)
    (hS : ∀ P : Subgroup G, P ≤ S → IsPGroup p P → IsMulCommutative P)
    (hidx : ¬ p ∣ S.index) {P : Subgroup G} (hP : IsPGroup p P) : IsMulCommutative P := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p S))
  have hQ : ¬ p ∣ (Q.map S.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out Q.not_dvd_index hidx
  let R₀ : Sylow p G := (Q.isPGroup'.map S.subtype).toSylow hQ
  have hR₀ : IsMulCommutative (R₀ : Subgroup G) :=
    hS _ (Subgroup.map_subtype_le _) R₀.isPGroup'
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  have hR : IsMulCommutative (R : Subgroup G) :=
    (R₀.equiv R).surjective.isMulCommutative hR₀
  exact isMulCommutative_anti hPR

theorem crossExcU_exists_conj_mem_of_not_dvd_index (S : Subgroup G) (hidx : ¬ p ∣ S.index)
    {y : G} (hy : y ^ p = 1) : ∃ g : G, g * y * g⁻¹ ∈ S := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p S))
  have hQ : ¬ p ∣ (Q.map S.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out Q.not_dvd_index hidx
  let R₀ : Sylow p G := (Q.isPGroup'.map S.subtype).toSylow hQ
  have hR₀S : (R₀ : Subgroup G) ≤ S := Subgroup.map_subtype_le _
  have hzp : IsPGroup p (Subgroup.zpowers y) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← hk, ← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, hy, _root_.one_zpow]
  obtain ⟨R, hR⟩ := hzp.exists_le_sylow
  have hyR : y ∈ (R : Subgroup G) := hR (Subgroup.mem_zpowers y)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R R₀
  refine ⟨g, hR₀S ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
  have := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (R : Subgroup G) hyR
  simpa [MulAut.smul_def, MulAut.conj_apply] using this

end Sylow

section Even

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] {r ε : ℕ}

theorem crossExcU_abelian_hypSU (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : ¬ p ∣ ℓ) (heven : Even (unitaryOrder ℓ f p)) (hε : ε ≤ 1)
    (hn : 1 ≤ 2 * r + ε) (hne : (2 * r + ε) / unitaryOrder ℓ f p < p)
    (P : Subgroup (hypSU h r ε)) (hP : IsPGroup p P) : IsMulCommutative P := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [h.card_eq_sq]
    exact fun hd => hpℓ (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd))
  refine crossExcU_isMulCommutative_of_not_dvd_index (leviSUHom (r := r) (ε := ε) h).range ?_
    (crossExcU_not_dvd_index h hp hpℓ heven hε hn) hP
  intro P' hP'le hP'
  have hι := leviSUHom_injective (r := r) (ε := ε) h
  have hcomap : IsPGroup p (P'.comap (leviSUHom (r := r) (ε := ε) h)) :=
    hP'.comap_of_injective _ hι
  have hpos := unitaryOrder_pos (f := f) hp hpℓ
  obtain ⟨d, hd⟩ := heven
  have he2 : unitaryOrder ℓ f p / 2 = d := by omega
  have hd0 : 0 < d := by omega
  have h1 : (2 * r + ε) / (d + d) = r / d := by
    rw [← two_mul, ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  have hGL : IsMulCommutative ((P'.comap (leviSUHom (r := r) (ε := ε) h)).map
      (leviPhi (r := r) h).ker.subtype) :=
    isMulCommutative_of_isPGroup_GL_matrix (hp.odd_of_ne_two (by omega)) hpK hd0
      (fun j => by rw [crossExcU_card_pow_iff_of_even h ⟨d, hd⟩ j, he2])
      (by rw [hd, h1] at hne; exact hne) (hcomap.map _)
  have hN : IsMulCommutative (P'.comap (leviSUHom (r := r) (ε := ε) h)) :=
    crossExcCl_isMulCommutative_of_map_injective _ (Subgroup.subtype_injective _) hGL
  rw [← Subgroup.map_comap_eq_self hP'le]
  infer_instance

theorem crossExcU_rank_hypSU (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : ¬ p ∣ ℓ) (heven : Even (unitaryOrder ℓ f p)) (hε : ε ≤ 1) (hn : 1 ≤ 2 * r + ε)
    (h4 : 4 * unitaryOrder ℓ f p ≤ 2 * r + ε) (Y : hypSU h r ε) (hY : Y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({Y} : Set (hypSU h r ε))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [h.card_eq_sq]
    exact fun hd => hpℓ (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd))
  have hι := leviSUHom_injective (r := r) (ε := ε) h
  obtain ⟨g, A, hA⟩ := crossExcU_exists_conj_mem_of_not_dvd_index
    (leviSUHom (r := r) (ε := ε) h).range (crossExcU_not_dvd_index h hp hpℓ heven hε hn) hY
  have hAp : ((A : (leviPhi (r := r) h).ker) : GL (Fin r) K) ^ p = 1 := by
    have h1 : leviSUHom (r := r) (ε := ε) h (A ^ p) = 1 := by
      rw [map_pow, hA, conj_pow, hY]
      group
    have h2 : A ^ p = 1 := hι (h1.trans (map_one _).symm)
    simpa using congrArg Subtype.val h2
  have hc : CFSG.Open.pRank p (centralizer ({g * Y * g⁻¹} : Set (hypSU h r ε))) ≤
      CFSG.Open.pRank p (centralizer ({Y} : Set (hypSU h r ε))) := by
    have := pRank_centralizer_of_mulEquiv (p := p) (MulAut.conj g) Y
    simpa [MulAut.conj_apply] using this
  refine le_trans ?_ hc
  rw [← hA]
  set a : GL (Fin r) K := ((A : (leviPhi (r := r) h).ker) : GL (Fin r) K) with ha
  obtain ⟨d, hd⟩ := heven
  have he2 : unitaryOrder ℓ f p / 2 = d := by omega
  have hd0 : 0 < d := by have := unitaryOrder_pos (f := f) hp hpℓ; omega
  have h4' : 4 * d ≤ r := by omega
  have hrank4 : 4 ≤ CFSG.Open.pRank p (centralizer ({a} : Set (GL (Fin r) K))) :=
    le_pRank_centralizer_GL_matrix hp5 hpK hd0
      (fun j => by rw [crossExcU_card_pow_iff_of_even h ⟨d, hd⟩ j, he2]) (by omega) h4' hAp
  have hker := pRank_le_pRank_inf_ker_add_one (p := p) (leviPhi (r := r) h)
    (centralizer ({a} : Set (GL (Fin r) K)))
  obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (centralizer ({a} : Set (GL (Fin r) K)) ⊓ (leviPhi (r := r) h).ker)
  obtain ⟨F, hF, hFcard, hFmem⟩ := exists_isElemAbelian_subgroupOf hE (leviPhi (r := r) h).ker
  have hEN : E ≤ (leviPhi (r := r) h).ker := hEle.trans inf_le_right
  have hFm : Nat.card F = p ^ CFSG.Open.pRank p
      (centralizer ({a} : Set (GL (Fin r) K)) ⊓ (leviPhi (r := r) h).ker) := by
    rw [hFcard, inf_eq_left.2 hEN, hEcard]
  haveI := hF.1
  let φ' : F →* hypSU h r ε := (leviSUHom (r := r) (ε := ε) h).comp F.subtype
  have hinj : Function.Injective φ' := hι.comp F.subtype_injective
  have hrange : φ'.range ≤ centralizer ({leviSUHom (r := r) (ε := ε) h A} : Set (hypSU h r ε)) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (((x : (leviPhi (r := r) h).ker)) : GL (Fin r) K) ∈ E := (hFmem (x : _)).1 x.2
    have hx' : (((x : (leviPhi (r := r) h).ker)) : GL (Fin r) K) ∈
        centralizer ({a} : Set (GL (Fin r) K)) := (hEle hx).1
    rw [Subgroup.mem_centralizer_singleton_iff] at hx'
    show leviSUHom (r := r) (ε := ε) h (x : (leviPhi (r := r) h).ker) *
      leviSUHom (r := r) (ε := ε) h A = leviSUHom (r := r) (ε := ε) h A *
        leviSUHom (r := r) (ε := ε) h (x : (leviPhi (r := r) h).ker)
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hx')
  have hle := CFSG.SectionRank.le_pRank_of_injective (A := F) hp.one_lt
    (fun a b => Subtype.ext (setLike_mul_comm a.2 b.2)) (fun a => Subtype.ext (hF.2 a a.2)) hFm
    φ' hinj hrange
  omega

theorem unitaryRankAt_of_even (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : ¬ p ∣ ℓ) (heven : Even (unitaryOrder ℓ f p)) (n : ℕ) :
    UnitaryRankAt ℓ f K n p (unitaryOrder ℓ f p) := by
  intro h4 Y hY
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos := unitaryOrder_pos (f := f) hp hpℓ
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  have hY' : (hypTransport h hR).symm Y ^ p = 1 := by rw [← map_pow, hY, map_one]
  have h3 := crossExcU_rank_hypSU h hp hp5 hpℓ heven hε (by omega) h4 _ hY'
  exact h3.trans (pRank_centralizer_of_mulEquiv (hypTransport h hR).symm Y)

theorem unitaryAbelianAt_of_even (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : ¬ p ∣ ℓ) (heven : Even (unitaryOrder ℓ f p)) (n : ℕ) :
    UnitaryAbelianAt ℓ f K n p (unitaryOrder ℓ f p) := by
  intro hne P hP
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos := unitaryOrder_pos (f := f) hp hpℓ
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hpK : ¬ p ∣ Nat.card K := by
      rw [h.card_eq_sq]
      exact fun hd => hpℓ (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd))
    obtain ⟨d, hd⟩ := heven
    have he2 : unitaryOrder ℓ f p / 2 = d := by omega
    have hGL : IsMulCommutative (P.map (unitarySU ℓ f K 0).subtype) :=
      isMulCommutative_of_isPGroup_GL_matrix (hp.odd_of_ne_two (by omega)) hpK (e := d)
        (by omega) (fun j => by rw [crossExcU_card_pow_iff_of_even h ⟨d, hd⟩ j, he2])
        (by rw [Nat.zero_div]; exact hp.pos) (hP.map _)
    exact crossExcCl_isMulCommutative_of_map_injective _ (Subgroup.subtype_injective _) hGL
  · obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε :=
      ⟨n / 2, n % 2, by omega, by omega⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
    have hcomap : IsPGroup p (P.comap (hypTransport h hR).toMonoidHom) :=
      hP.comap_of_injective _ (hypTransport h hR).injective
    haveI hab := crossExcU_abelian_hypSU h hp hp5 hpℓ heven hε hn0 hne _ hcomap
    rw [← Subgroup.map_comap_eq_self_of_surjective
      (f := (hypTransport h hR).toMonoidHom) (hypTransport h hR).surjective P]
    infer_instance

end Even

end CrossExcU

end CFSG.LocalAnalysis.RankFourTheoremC
