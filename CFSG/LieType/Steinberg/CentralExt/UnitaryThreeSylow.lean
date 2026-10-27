module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial

section Defs

open Matrix

variable {K : Type} [Field K]

@[expose] def coordPairSubgroup (τ : K →+* K) (G₀ : Matrix (Fin 3) (Fin 3) K) (P : GL (Fin 3) K)
    (c : Fin 3) : Subgroup (SUgram τ G₀) where
  carrier := {g | ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
    (fun k => (P : Matrix (Fin 3) (Fin 3) K) k c) = fun k => (P : Matrix (Fin 3) (Fin 3) K) k c}
  mul_mem' {g h} hg hh := by
    change (((g * h : SUgram τ G₀) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [show ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _ from hh]
    exact hg
  one_mem' := by
    change (((1 : SUgram τ G₀) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  inv_mem' {g} hg := by
    change (((g⁻¹ : SUgram τ G₀) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    have hg' : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (fun k => (P : Matrix (Fin 3) (Fin 3) K) k c) =
        fun k => (P : Matrix (Fin 3) (Fin 3) K) k c := hg
    conv_lhs => rw [← hg']
    rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

@[expose] def swapNegGL : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapNegGL :
    ((swapNegGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, -1] :=
  rfl

end Defs

section Arith

theorem ordProj_two_of_odd {n : ℕ} (hn : Odd n) : ordProj[2] n = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd hn.not_two_dvd_nat, pow_zero]

theorem ordProj_two_two_mul {m : ℕ} (hm : Odd m) : ordProj[2] (2 * m) = 2 := by
  rw [Nat.ordProj_mul 2 two_ne_zero (by rintro rfl; exact (Nat.not_odd_zero hm)),
    ordProj_two_of_odd hm, Nat.Prime.factorization_self Nat.prime_two, pow_one, mul_one]

theorem ordProj_two_card_SU_three {q : ℕ} (hq : Odd q) (hq1 : 1 < q) :
    ordProj[2] (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) =
      ordProj[2] (q - 1) * (ordProj[2] (q + 1)) ^ 2 := by
  have e : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) =
      q ^ 3 * (q ^ 2 - q + 1) * ((q - 1) * ((q + 1) * (q + 1))) := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
    zify [h1, h2, hq1.le]
    ring
  have hodd : Odd (q ^ 3 * (q ^ 2 - q + 1)) := by
    refine hq.pow.mul ?_
    have : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, sq]
    rw [this]
    exact (Nat.even_mul_pred_self q).add_one
  rw [e, Nat.ordProj_mul 2 hodd.pos.ne' (Nat.mul_ne_zero (by omega) (by positivity)),
    ordProj_two_of_odd hodd, one_mul, Nat.ordProj_mul 2 (by omega) (by positivity),
    Nat.ordProj_mul 2 (by omega) (by omega), sq]

theorem ordProj_two_sub_one_of_mod_four_eq_three {q : ℕ} (hq : q % 4 = 3) :
    ordProj[2] (q - 1) = 2 := by
  rw [show q - 1 = 2 * ((q - 1) / 2) by omega, ordProj_two_two_mul (Nat.odd_iff.2 (by omega))]

theorem ordProj_two_add_one_of_mod_four_eq_one {q : ℕ} (hq : q % 4 = 1) :
    ordProj[2] (q + 1) = 2 := by
  rw [show q + 1 = 2 * ((q + 1) / 2) by omega, ordProj_two_two_mul (Nat.odd_iff.2 (by omega))]

end Arith

section Group

variable {G : Type*} [Group G]

theorem exists_lt_orderOf_zpow_eq {x : G} (hx : 0 < orderOf x) (i : ℤ) :
    ∃ m : ℕ, m < orderOf x ∧ x ^ i = x ^ m := by
  have h0 : (0 : ℤ) ≤ i % (orderOf x : ℤ) := Int.emod_nonneg i (by exact_mod_cast hx.ne')
  have h1 : i % (orderOf x : ℤ) < orderOf x := Int.emod_lt_of_pos i (by exact_mod_cast hx)
  refine ⟨(i % (orderOf x : ℤ)).toNat, by omega, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg h0, zpow_mod_orderOf]

private theorem exists_mul_pow_eq_pow {t : G} (ht : t ^ 2 = 1) {e : ℕ} (he : e < 2) :
    ∃ e' : ℕ, e' < 2 ∧ t * t ^ e = t ^ e' := by
  interval_cases e
  · exact ⟨1, by norm_num, by rw [pow_zero, mul_one, pow_one]⟩
  · exact ⟨0, by norm_num, by rw [pow_one, ← sq, ht, pow_zero]⟩

theorem exists_zpow_mul_zpow_mul_pow {u v t : G} (huv : Commute u v) (hv : v = t⁻¹ * u * t)
    (ht : t ^ 2 = 1) {w : G} (hw : w ∈ Subgroup.closure {u, v, t}) :
    ∃ i j : ℤ, ∃ e : ℕ, e < 2 ∧ w = u ^ i * v ^ j * t ^ e := by
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht])
  have h1 : t * u = v * t := by
    rw [hv, htt, mul_assoc, ← sq, ht, mul_one]
  have h2 : t * v = u * t := by
    rw [hv, htt, ← mul_assoc, ← mul_assoc, ← sq, ht, one_mul]
  have hconj : ∀ i j : ℤ, t * (u ^ i * v ^ j) = u ^ j * v ^ i * t := by
    intro i j
    have := (SemiconjBy.zpow_right h1 i).mul_right (SemiconjBy.zpow_right h2 j)
    rw [this.eq, ((huv.zpow_zpow j i).symm).eq]
  have ht' : ∀ i j : ℤ, ∀ e : ℕ, e < 2 →
      ∃ i' j' : ℤ, ∃ e' : ℕ, e' < 2 ∧ t * (u ^ i * v ^ j * t ^ e) = u ^ i' * v ^ j' * t ^ e' := by
    intro i j e he
    obtain ⟨e', he', hte⟩ := exists_mul_pow_eq_pow ht he
    exact ⟨j, i, e', he', by rw [← mul_assoc, hconj, mul_assoc, hte]⟩
  induction hw using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, 0, by norm_num, by simp⟩
  | mul_left x hx y _ ih =>
    obtain ⟨i, j, e, he, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx <;> subst x
    · exact ⟨1 + i, j, e, he, by rw [zpow_one_add]; simp only [mul_assoc]⟩
    · refine ⟨i, 1 + j, e, he, ?_⟩
      rw [zpow_one_add]
      simp only [← mul_assoc]
      rw [(huv.symm.zpow_right i).eq]
    · exact ht' i j e he
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨i, j, e, he, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx <;> subst x
    · exact ⟨-1 + i, j, e, he, by rw [zpow_add, zpow_neg_one]; simp only [mul_assoc]⟩
    · refine ⟨i, -1 + j, e, he, ?_⟩
      rw [zpow_add, zpow_neg_one]
      simp only [← mul_assoc]
      rw [(huv.symm.inv_left.zpow_right i).eq]
    · rw [htt]
      exact ht' i j e he

theorem exists_zpow_mul_pow {u t : G} {k : ℤ} (ht : t ^ 2 = 1) (hut : t⁻¹ * u * t = u ^ k)
    {w : G} (hw : w ∈ Subgroup.closure {u, t}) :
    ∃ i : ℤ, ∃ e : ℕ, e < 2 ∧ w = u ^ i * t ^ e := by
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht])
  have h1 : t * u = u ^ k * t := by
    rw [← hut, htt, mul_assoc, ← sq, ht, mul_one]
  have ht' : ∀ i : ℤ, ∀ e : ℕ, e < 2 →
      ∃ i' : ℤ, ∃ e' : ℕ, e' < 2 ∧ t * (u ^ i * t ^ e) = u ^ i' * t ^ e' := by
    intro i e he
    obtain ⟨e', he', hte⟩ := exists_mul_pow_eq_pow ht he
    refine ⟨k * i, e', he', ?_⟩
    rw [← mul_assoc, (SemiconjBy.zpow_right h1 i).eq, ← zpow_mul, mul_assoc, hte]
  induction hw using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, by norm_num, by simp⟩
  | mul_left x hx y _ ih =>
    obtain ⟨i, e, he, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> subst x
    · exact ⟨1 + i, e, he, by rw [zpow_one_add, mul_assoc]⟩
    · exact ht' i e he
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨i, e, he, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> subst x
    · exact ⟨-1 + i, e, he, by rw [zpow_add, zpow_neg_one, mul_assoc]⟩
    · rw [htt]
      exact ht' i e he

theorem injOn_mk'_of_isPGroup_two {D : Subgroup G} [D.Normal] (hD : ∀ d ∈ D, d ^ 3 = 1)
    {W : Subgroup G} (hW : IsPGroup 2 W) : Set.InjOn (QuotientGroup.mk' D) (W : Set G) := by
  intro x hx y hy hxy
  have hd : x⁻¹ * y ∈ D := QuotientGroup.eq.1 hxy
  obtain ⟨k, hk⟩ := hW ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩
  have h1 : (x⁻¹ * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) :=
    (Nat.coprime_comm.1 (Nat.coprime_two_left.2 (by decide : Odd 3))).pow_right k
  have h := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one (hD _ hd)) (orderOf_dvd_of_pow_eq_one h1))
  exact inv_mul_eq_one.1 h

theorem card_map_mk'_of_isPGroup_two {D : Subgroup G} [D.Normal] (hD : ∀ d ∈ D, d ^ 3 = 1)
    {W : Subgroup G} (hW : IsPGroup 2 W) :
    Nat.card (W.map (QuotientGroup.mk' D)) = Nat.card W := by
  have := Nat.card_image_of_injOn (injOn_mk'_of_isPGroup_two hD hW)
  rw [← Subgroup.coe_map] at this
  exact this

end Group

section Matrices

open Matrix

variable {K : Type} [Field K]

private def diagGLHom (n : ℕ) : (Fin n → Kˣ) →* GL (Fin n) K where
  toFun := diagGL
  map_one' := Units.ext (by rw [coe_diagGL, Units.val_one]; simp)
  map_mul' d e := Units.ext (by
    rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
    simp)

private theorem diagGLHom_apply {n : ℕ} (d : Fin n → Kˣ) : diagGLHom n d = diagGL d :=
  rfl

theorem diagGL_injective {n : ℕ} :
    Function.Injective (diagGL : (Fin n → Kˣ) → GL (Fin n) K) := by
  intro d e h
  funext i
  have := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h)
    i) i
  simp only [coe_diagGL, diagonal_apply_eq] at this
  exact Units.ext this

theorem diagGL_ne_diagGL_mul_swapNegGL (y y' : Fin 3 → Kˣ) :
    diagGL y ≠ diagGL y' * swapNegGL := by
  intro h
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h)
    0) 1
  simp [coe_diagGL, coe_swapNegGL, Matrix.mul_apply, Fin.sum_univ_three] at this
  exact (y' 0).ne_zero this.symm

theorem diagGL_mul_swapNegGL_pow_inj {x x' : Fin 3 → Kˣ} {e e' : ℕ} (he : e < 2) (he' : e' < 2)
    (h : diagGL x * swapNegGL ^ e = diagGL x' * swapNegGL ^ e') : e = e' ∧ x = x' := by
  interval_cases e <;> interval_cases e'
  · rw [pow_zero, mul_one, mul_one] at h
    exact ⟨rfl, diagGL_injective h⟩
  · rw [pow_zero, mul_one, pow_one] at h
    exact absurd h (diagGL_ne_diagGL_mul_swapNegGL _ _)
  · rw [pow_zero, mul_one, pow_one] at h
    exact absurd h.symm (diagGL_ne_diagGL_mul_swapNegGL _ _)
  · exact ⟨rfl, diagGL_injective (mul_right_cancel h)⟩

theorem ctr_diagonal (τ : K →+* K) {n : ℕ} (v : Fin n → K) :
    ctr τ (diagonal v) = diagonal fun i => τ (v i) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [ctr]
  · simp [ctr, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem diagGL_mem_SUgram_one {τ : K →+* K} {n : ℕ} {d : Fin n → Kˣ}
    (hd : ∀ i, τ (d i) * d i = 1) (hdet : ∏ i, (d i : K) = 1) :
    diagGL d ∈ SUgram τ (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨by rw [coe_diagGL, det_diagonal, hdet], ?_⟩
  rw [Matrix.mul_one, coe_diagGL, ctr_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext hd)

theorem diagGL_mem_SUgram_hyp {τ : K →+* K} {d : Fin 3 → Kˣ} (h01 : τ (d 0) * d 1 = 1)
    (h10 : τ (d 1) * d 0 = 1) (h22 : τ (d 2) * d 2 = 1) (hdet : (d 0 : K) * d 1 * d 2 = 1) :
    diagGL d ∈ SUgram τ (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨by rw [coe_diagGL, det_diagonal, Fin.prod_univ_three, hdet], ?_⟩
  rw [coe_diagGL, ctr_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [h01, h10, h22]

theorem ctr_swapNegGL (τ : K →+* K) :
    ctr τ ((swapNegGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((swapNegGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [coe_swapNegGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ctr]

private theorem swapNegGL_mem_SUgram (τ : K →+* K) {G : Matrix (Fin 3) (Fin 3) K}
    (hG : ((swapNegGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * G *
      ((swapNegGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = G) :
    swapNegGL ∈ SUgram τ G := by
  refine ⟨by simp [coe_swapNegGL, Matrix.det_fin_three], ?_⟩
  rw [ctr_swapNegGL, hG]

theorem swapNegGL_mem_SUgram_one (τ : K →+* K) :
    swapNegGL ∈ SUgram τ (1 : Matrix (Fin 3) (Fin 3) K) :=
  swapNegGL_mem_SUgram τ (by
    rw [Matrix.mul_one, coe_swapNegGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem swapNegGL_mem_SUgram_hyp (τ : K →+* K) :
    swapNegGL ∈ SUgram τ (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) :=
  swapNegGL_mem_SUgram τ (by
    rw [coe_swapNegGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem swapNegGL_sq : (swapNegGL : GL (Fin 3) K) ^ 2 = 1 := by
  refine Units.ext ?_
  rw [sq, Units.val_mul, coe_swapNegGL, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swapNegGL_inv : (swapNegGL : GL (Fin 3) K)⁻¹ = swapNegGL :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, swapNegGL_sq])

theorem swapNegGL_conj_diagGL (d : Fin 3 → Kˣ) :
    swapNegGL⁻¹ * diagGL d * swapNegGL = diagGL ![d 1, d 0, d 2] := by
  rw [swapNegGL_inv]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_swapNegGL, coe_diagGL, coe_diagGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp

end Matrices

section CoordPair

open Matrix

variable {K : Type} [Field K]

private theorem col_eq_mulVec_single (P : GL (Fin 3) K) (c : Fin 3) :
    (fun k => (P : Matrix (Fin 3) (Fin 3) K) k c) =
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single c 1 := by
  rw [mulVec_single_one]
  rfl

private theorem mulVec_inv_mulVec (P : GL (Fin 3) K) (x : Fin 3 → K) :
    ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ x) =
      x := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

private theorem mulVec_mulVec_inv (P : GL (Fin 3) K) (x : Fin 3 → K) :
    (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) =
      x := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem mem_coordPairSubgroup_iff {τ : K →+* K} {G₀ : Matrix (Fin 3) (Fin 3) K}
    {P : GL (Fin 3) K} {c : Fin 3} {g : SUgram τ G₀} :
    g ∈ coordPairSubgroup τ G₀ P c ↔
      ((P⁻¹ * (g : GL (Fin 3) K) * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        Pi.single c 1 = Pi.single c 1 := by
  change ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun k => _) = (fun k => _) ↔ _
  rw [col_eq_mulVec_single, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  constructor
  · intro h
    rw [h, mulVec_inv_mulVec]
  · intro h
    have := congrArg ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ ·) h
    simp only at this
    rwa [mulVec_mulVec_inv] at this

private theorem col_ne_zero (P : GL (Fin 3) K) (c : Fin 3) :
    (fun k => (P : Matrix (Fin 3) (Fin 3) K) k c) ≠ 0 := by
  intro h
  have h' := mulVec_inv_mulVec P (Pi.single c 1)
  rw [← col_eq_mulVec_single, h, mulVec_zero] at h'
  have := congrFun h' c
  simp at this

theorem injective_mk'_comp_coordPairSubgroup_subtype {τ : K →+* K}
    {G₀ : Matrix (Fin 3) (Fin 3) K} (P : GL (Fin 3) K) (c : Fin 3) (D : Subgroup (SUgram τ G₀))
    [D.Normal] (hD : D ≤ (StatedScalars (Fin 3) K).subgroupOf (SUgram τ G₀)) :
    Function.Injective ((QuotientGroup.mk' D).comp (coordPairSubgroup τ G₀ P c).subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgD : (g : SUgram τ G₀) ∈ D := (QuotientGroup.eq_one_iff _).1 hg
  obtain ⟨a, ha⟩ := hD hgD
  have hgx : (((g : SUgram τ G₀) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (fun k => (P : Matrix (Fin 3) (Fin 3) K) k c) =
      fun k => (P : Matrix (Fin 3) (Fin 3) K) k c := g.2
  have ha' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) a : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (((g : SUgram τ G₀) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    congrArg Units.val ha
  rw [← ha', Matrix.GeneralLinearGroup.coe_scalar] at hgx
  have hsmul : (a : K) • (fun k => (P : Matrix (Fin 3) (Fin 3) K) k c) =
      fun k => (P : Matrix (Fin 3) (Fin 3) K) k c := by
    rwa [scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec] at hgx
  have ha1 : a = 1 := by
    have h0 : ((a : K) - 1) • (fun k => (P : Matrix (Fin 3) (Fin 3) K) k c) = 0 := by
      rw [sub_smul, one_smul, hsmul, sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact Units.ext (sub_eq_zero.1 h)
    · exact absurd h (col_ne_zero P c)
  have ha'' : (Matrix.GeneralLinearGroup.scalar (Fin 3) a : GL (Fin 3) K) =
      ((g : SUgram τ G₀) : GL (Fin 3) K) := ha
  refine Subtype.ext (Subtype.ext ?_)
  rw [Subgroup.coe_one, Subgroup.coe_one, ← ha'', ha1, map_one]

theorem embPair_mulVec_single (c : Fin 3) (A : Matrix (Fin 2) (Fin 2) K) :
    embPair c A *ᵥ Pi.single c 1 = Pi.single c 1 := by
  fin_cases c <;> ext k <;> fin_cases k <;>
    simp [embPair, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_embSUid_eq_of_mulVec {σ : K ≃+* K} {B : SUid σ 3} {c : Fin 3}
    (hB : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single c 1 = Pi.single c 1) :
    ∃ A, embSUid σ c A = B := by
  set b := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  obtain ⟨hdet, hu⟩ := B.2
  change b.det = 1 at hdet
  change conjTr σ b * b = 1 at hu
  have hcol : ∀ i, b i c = if i = c then 1 else 0 := by
    intro i
    have := congrFun hB i
    rw [mulVec_single_one] at this
    simpa [Pi.single_apply] using this
  have hrow : ∀ j, b c j = if j = c then 1 else 0 := by
    intro j
    have h1 : conjTr σ b *ᵥ Pi.single c 1 = Pi.single c 1 := by
      calc conjTr σ b *ᵥ Pi.single c 1 = conjTr σ b *ᵥ (b *ᵥ Pi.single c 1) := by rw [hB]
        _ = Pi.single c 1 := by rw [mulVec_mulVec, hu, one_mulVec]
    have h2 := congrFun h1 j
    rw [mulVec_single_one] at h2
    apply σ.injective
    simp only [conjTr, col_apply, transpose_apply, map_apply] at h2
    rw [h2]
    split_ifs with h
    · subst h
      simp
    · simp [h]
  set A : Matrix (Fin 2) (Fin 2) K := b.submatrix c.succAbove c.succAbove
  have hemb : embPair c A = b := by
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at hcol hrow ⊢ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [embPair, A, hcol, hrow] <;> rfl
  have hAu : conjTr σ A * A = 1 := by
    apply embPair_injective c
    rw [embPair_mul, ← conjTr_embPair, hemb, hu, embPair_one]
  have hAdet : A.det = 1 := by rw [← det_embPair c, hemb, hdet]
  let AGL : GL (Fin 2) K := ⟨A, conjTr σ A, mul_eq_one_comm.mp hAu, hAu⟩
  exact ⟨⟨AGL, hAdet, hAu⟩, Subtype.ext (Units.ext hemb)⟩

end CoordPair

section Finite

open Matrix

variable {K : Type} [Field K] {p f : ℕ}

theorem fixedField_eq_fixedSubfield (hK : UnitaryFieldData p f K) [Finite K] [Fact p.Prime]
    [CharP K p] : hK.fixedField = fixedSubfield K p f := by
  unfold UnitaryFieldData.fixedField fixedSubfield
  rw [unitaryFieldData_bar_eq hK]

theorem SUgram_bar_one (hK : UnitaryFieldData p f K) [Finite K] [Fact p.Prime] [CharP K p]
    (n : ℕ) : SUgram hK.bar (1 : Matrix (Fin n) (Fin n) K) = SUid (unitaryInvolution K p f) n := by
  rw [unitaryFieldData_bar_eq hK, SUgram_one]

theorem nonempty_coordPairSubgroup_mulEquiv (hK : UnitaryFieldData p f K) [Finite K]
    [Fact p.Prime] [CharP K p] {G₀ : Matrix (Fin 3) (Fin 3) K} (P : GL (Fin 3) K)
    (hP : ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * G₀ * (P : Matrix (Fin 3) (Fin 3) K) = 1)
    (c : Fin 3) :
    Nonempty (coordPairSubgroup hK.bar G₀ P c ≃* SpecialLinearGroup (Fin 2) hK.fixedField) := by
  have hF := card_eq_sq_of_unitaryFieldData hK
  set σ := unitaryInvolution K p f
  let ψ : SUgram hK.bar G₀ ≃* SUid σ 3 :=
    (gramEquiv P hP).trans (MulEquiv.subgroupCongr (SUgram_bar_one hK 3))
  have hmem : ∀ g, g ∈ coordPairSubgroup hK.bar G₀ P c ↔ ∃ A, embSUid σ c A = ψ g := by
    intro g
    rw [mem_coordPairSubgroup_iff]
    constructor
    · exact fun h => exists_embSUid_eq_of_mulVec h
    · rintro ⟨A, hA⟩
      have := embPair_mulVec_single c ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      rw [← coe_embSUid, hA] at this
      exact this
  let φ : SUid σ 2 →* coordPairSubgroup hK.bar G₀ P c :=
    (ψ.symm.toMonoidHom.comp (embSUid σ c)).codRestrict _ fun A =>
      (hmem _).2 ⟨A, by rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun A B h => embSUid_injective σ c (ψ.symm.injective (congrArg Subtype.val h)),
      fun g => ?_⟩
    obtain ⟨A, hA⟩ := (hmem g).1 g.2
    refine ⟨A, Subtype.ext ?_⟩
    change ψ.symm (embSUid σ c A) = g
    rw [hA, MulEquiv.symm_apply_apply]
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P₂, hP₂⟩ := exists_wittMatrix hF 2
  rw [fixedField_eq_fixedSubfield hK]
  exact ⟨(MulEquiv.ofBijective φ hφ).symm.trans ((hypEquiv hζ0 hζ).trans
    (conjEquiv P₂ hP₂)).symm⟩

end Finite

section Orders

open Matrix

variable {K : Type} [Field K] {p f : ℕ}

theorem exists_ctr_mul_mul_eq_one (hK : UnitaryFieldData p f K) {n : ℕ}
    {G₀ : Matrix (Fin n) (Fin n) K} (hG : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (hdet : G₀.det ≠ 0) :
    ∃ P : GL (Fin n) K,
      ctr hK.bar (P : Matrix (Fin n) (Fin n) K) * G₀ * (P : Matrix (Fin n) (Fin n) K) = 1 := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  have hGσ : conjTr (unitaryInvolution K p f) G₀ = G₀ := by
    ext i j
    rw [← hG i j, unitaryFieldData_bar_eq hK]
    rfl
  obtain ⟨P, hP⟩ := exists_conjTr_mul_mul_eq_one (card_eq_sq_of_unitaryFieldData hK) hGσ hdet
  refine ⟨P, ?_⟩
  rw [unitaryFieldData_bar_eq hK]
  exact hP

theorem exists_ctr_mul_mul_eq_hyp (hK : UnitaryFieldData p f K) {G₀ : Matrix (Fin 3) (Fin 3) K}
    (hG : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (hdet : G₀.det ≠ 0) :
    ∃ M : GL (Fin 3) K, ctr hK.bar (M : Matrix (Fin 3) (Fin 3) K) * G₀ *
      (M : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  obtain ⟨P, hP⟩ := exists_ctr_mul_mul_eq_one hK hG hdet
  obtain ⟨W, hW⟩ := exists_wittMatrix (card_eq_sq_of_unitaryFieldData hK) 2
  let N : GL (Fin 3) K := ⟨embPair 2 W, embPair 2 ((W⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
    by rw [← embPair_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, embPair_one],
    by rw [← embPair_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, embPair_one]⟩
  refine ⟨P * N, ?_⟩
  have e : ctr hK.bar ((P * N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * G₀ *
      ((P * N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ctr hK.bar (N : Matrix (Fin 3) (Fin 3) K) *
        (ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * G₀ * (P : Matrix (Fin 3) (Fin 3) K)) *
          (N : Matrix (Fin 3) (Fin 3) K) := by
    rw [Units.val_mul, ctr_mul]
    simp only [Matrix.mul_assoc]
  rw [e, hP, Matrix.mul_one, unitaryFieldData_bar_eq hK]
  change conjTr (unitaryInvolution K p f) (embPair 2 (W : Matrix (Fin 2) (Fin 2) K)) *
    embPair 2 (W : Matrix (Fin 2) (Fin 2) K) = _
  rw [conjTr_embPair, ← embPair_mul, hW, antidiag_two]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem card_scalars_SUgram_dvd_three [Finite K] (τ : K →+* K) (G₀ : Matrix (Fin 3) (Fin 3) K) :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf (SUgram τ G₀)) ∣ 3 := by
  set Z := (StatedScalars (Fin 3) K).subgroupOf (SUgram τ G₀)
  have hcyc : IsCyclic (StatedScalars (Fin 3) K) :=
    isCyclic_of_surjective (Matrix.GeneralLinearGroup.scalar (Fin 3) :
      Kˣ →* GL (Fin 3) K).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  let g : Z →* StatedScalars (Fin 3) K :=
    ((SUgram τ G₀).subtype.comp Z.subtype).codRestrict _ fun x => x.2
  have : IsCyclic Z := isCyclic_of_injective g fun x y h =>
    Subtype.ext (Subtype.ext (by have := congrArg Subtype.val h; exact this))
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
  rw [Subgroup.coe_pow, pow_three_eq_one_of_mem_statedScalars
    (fun _ hy => det_eq_one_of_mem_SUgram hy) x.2, Subgroup.coe_one]

theorem ordProj_two_card_SUgram (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {G₀ : Matrix (Fin 3) (Fin 3) K} (hG : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (hdet : G₀.det ≠ 0) :
    ordProj[2] (Nat.card (SUgram hK.bar G₀)) =
      ordProj[2] (p ^ f - 1) * (ordProj[2] (p ^ f + 1)) ^ 2 := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  have hF := card_eq_sq_of_unitaryFieldData hK
  obtain ⟨e⟩ := nonempty_SUgram_mulEquiv hK hG hdet
  rw [Nat.card_congr e.toEquiv, card_SU_three hF]
  exact ordProj_two_card_SU_three (hK.prime.odd_of_ne_two hp2).pow
    (CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF)

theorem ordProj_two_card_quotient_of_odd {S : Type*} [Group S] [Finite S] (D : Subgroup S)
    [D.Normal] (hD : Odd (Nat.card D)) :
    ordProj[2] (Nat.card (S ⧸ D)) = ordProj[2] (Nat.card S) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D,
    Nat.ordProj_mul 2 Nat.card_pos.ne' Nat.card_pos.ne', ordProj_two_of_odd hD, mul_one]

theorem exists_norm_one_orderOf_eq_ordProj (hK : UnitaryFieldData p f K) :
    ∃ l : Kˣ, hK.bar l * l = 1 ∧ orderOf l = ordProj[2] (p ^ f + 1) := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  obtain ⟨l₀, hl₀, hlo⟩ := exists_norm_one_orderOf_eq (card_eq_sq_of_unitaryFieldData hK)
  obtain ⟨m, hm⟩ := Nat.ordProj_dvd (p ^ f + 1) 2
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  refine ⟨l₀ ^ m, ?_, ?_⟩
  · rw [unitaryFieldData_bar_eq hK, Units.val_pow_eq_pow_val]
    change unitaryInvolution K p f ((l₀ : K) ^ m) * (l₀ : K) ^ m = 1
    rw [map_pow, ← mul_pow, hl₀, one_pow]
  · rw [orderOf_pow_of_dvd hm0 (by rw [hlo]; exact Dvd.intro_left _ hm.symm), hlo]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0) hm

theorem exists_orderOf_eq_two_mul_ordProj (hK : UnitaryFieldData p f K) (hq : p ^ f % 4 = 1) :
    ∃ z : Kˣ, orderOf z = 2 * ordProj[2] (p ^ f - 1) := by
  have := hK.finite
  have hF := card_eq_sq_of_unitaryFieldData hK
  have hq1 := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      CFSG.ClassicalGroups.Unitary.card_units_of_card hF]
  have hdvd : 2 * ordProj[2] (p ^ f - 1) ∣ (p ^ f) ^ 2 - 1 := by
    rw [CFSG.ClassicalGroups.Unitary.sq_sub_one_eq _ hq1.le]
    exact Nat.mul_dvd_mul (by omega) (Nat.ordProj_dvd _ _)
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < (p ^ f) ^ 2 - 1 := by
    have : 1 < (p ^ f) ^ 2 := Nat.one_lt_pow two_ne_zero hq1
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  refine ⟨g ^ m, ?_⟩
  rw [orderOf_pow_of_dvd hm0 (by rw [hgo]; exact Dvd.intro_left _ hm.symm), hgo]
  exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0) hm

end Orders

section Models

open Matrix

variable {K : Type} [Field K] {p f : ℕ}

private theorem orderOf_eq_of_forall_zpow {H : Type*} [Group H] {n : ℕ} {d : Fin n → H} {x : H}
    {i₀ : Fin n} (h₀ : d i₀ = x) (hpow : ∀ i, ∃ m : ℤ, d i = x ^ m) : orderOf d = orderOf x := by
  refine orderOf_eq_orderOf_iff.2 fun k => ⟨fun h => ?_, fun h => funext fun i => ?_⟩
  · rw [← h₀]
    exact congrFun h i₀
  · obtain ⟨m, hm⟩ := hpow i
    rw [Pi.pow_apply, hm, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, h, _root_.one_zpow, Pi.one_apply]

theorem exists_unitary_three_model_of_norm_one (hK : UnitaryFieldData p f K)
    {G₀ : Matrix (Fin 3) (Fin 3) K} (P : GL (Fin 3) K)
    (hP : ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * G₀ * (P : Matrix (Fin 3) (Fin 3) K) = 1)
    (l : Kˣ) (hl : hK.bar l * l = 1) :
    ∃ (u v τ : SUgram hK.bar G₀),
      (u : GL (Fin 3) K) = P * diagGL ![l, 1, l⁻¹] * P⁻¹ ∧
      (v : GL (Fin 3) K) = P * diagGL ![1, l, l⁻¹] * P⁻¹ ∧
      (τ : GL (Fin 3) K) = P * swapNegGL * P⁻¹ ∧
      v = τ⁻¹ * u * τ ∧ Commute u v ∧ orderOf u = orderOf l ∧ orderOf v = orderOf l ∧
      τ ^ 2 = 1 ∧ u ∈ coordPairSubgroup hK.bar G₀ P 1 ∧ v ∈ coordPairSubgroup hK.bar G₀ P 0 ∧
      ∀ i j e i' j' e' : ℕ, e < 2 → e' < 2 → u ^ i * v ^ j * τ ^ e = u ^ i' * v ^ j' * τ ^ e' →
        l ^ i = l ^ i' ∧ l ^ j = l ^ j' ∧ e = e' := by
  have hinv : (hK.bar (l : K))⁻¹ * (l : K)⁻¹ = 1 := by
    rw [← mul_inv, hl, inv_one]
  have ha : diagGL ![l, 1, l⁻¹] ∈ SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) :=
    diagGL_mem_SUgram_one (fun i => by fin_cases i <;> simp [hl, hinv])
      (by simp [Fin.prod_univ_three])
  have hb : diagGL ![1, l, l⁻¹] ∈ SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) :=
    diagGL_mem_SUgram_one (fun i => by fin_cases i <;> simp [hl, hinv])
      (by simp [Fin.prod_univ_three])
  have ht := swapNegGL_mem_SUgram_one (K := K) hK.bar
  let ψ := (gramEquiv (τ := hK.bar) (G₁ := 1) P hP).symm
  let A : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) := ⟨_, ha⟩
  let B : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) := ⟨_, hb⟩
  let T : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) := ⟨_, ht⟩
  have hBA : B = T⁻¹ * A * T := Subtype.ext (by
    change diagGL ![1, l, l⁻¹] = swapNegGL⁻¹ * diagGL ![l, 1, l⁻¹] * swapNegGL
    rw [swapNegGL_conj_diagGL]
    rfl)
  have hAB : Commute A B := Subtype.ext (by
    change diagGLHom 3 ![l, 1, l⁻¹] * diagGLHom 3 ![1, l, l⁻¹] =
      diagGLHom 3 ![1, l, l⁻¹] * diagGLHom 3 ![l, 1, l⁻¹]
    rw [← map_mul, ← map_mul, mul_comm])
  have hT : T ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact swapNegGL_sq)
  have hoA : orderOf A = orderOf l := by
    rw [Subgroup.orderOf_mk, ← diagGLHom_apply, orderOf_injective _ diagGL_injective]
    refine orderOf_eq_of_forall_zpow (i₀ := 0) rfl fun i => ?_
    fin_cases i
    exacts [⟨1, by simp⟩, ⟨0, by simp⟩, ⟨-1, by simp⟩]
  have hoB : orderOf B = orderOf l := by
    rw [Subgroup.orderOf_mk, ← diagGLHom_apply, orderOf_injective _ diagGL_injective]
    refine orderOf_eq_of_forall_zpow (i₀ := 1) rfl fun i => ?_
    fin_cases i
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩]
  have hval : ∀ i j : ℕ, ((A ^ i * B ^ j : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) :
      GL (Fin 3) K) = diagGL (![l, 1, l⁻¹] ^ i * ![1, l, l⁻¹] ^ j) := fun i j => by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    change diagGLHom 3 ![l, 1, l⁻¹] ^ i * diagGLHom 3 ![1, l, l⁻¹] ^ j =
      diagGLHom 3 (![l, 1, l⁻¹] ^ i * ![1, l, l⁻¹] ^ j)
    rw [map_mul, map_pow, map_pow]
  refine ⟨ψ A, ψ B, ψ T, rfl, rfl, rfl, by rw [hBA, map_mul, map_mul, map_inv], hAB.map ψ,
    by rw [MulEquiv.orderOf_eq, hoA], by rw [MulEquiv.orderOf_eq, hoB],
    by rw [← map_pow, hT, map_one], ?_, ?_, ?_⟩
  · rw [mem_coordPairSubgroup_iff]
    change ((P⁻¹ * (P * diagGL ![l, 1, l⁻¹] * P⁻¹) * P : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [show P⁻¹ * (P * diagGL ![l, 1, l⁻¹] * P⁻¹) * P = diagGL ![l, 1, l⁻¹] by group,
      coe_diagGL, diagonal_mulVec_single]
    simp
  · rw [mem_coordPairSubgroup_iff]
    change ((P⁻¹ * (P * diagGL ![1, l, l⁻¹] * P⁻¹) * P : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [show P⁻¹ * (P * diagGL ![1, l, l⁻¹] * P⁻¹) * P = diagGL ![1, l, l⁻¹] by group,
      coe_diagGL, diagonal_mulVec_single]
    simp
  · intro i j e i' j' e' he he' h
    have h' : A ^ i * B ^ j * T ^ e = A ^ i' * B ^ j' * T ^ e' :=
      ψ.injective (by simpa only [map_mul, map_pow] using h)
    have h'' : diagGL (![l, 1, l⁻¹] ^ i * ![1, l, l⁻¹] ^ j) * swapNegGL ^ e =
        diagGL (![l, 1, l⁻¹] ^ i' * ![1, l, l⁻¹] ^ j') * swapNegGL ^ e' := by
      have := congrArg Subtype.val h'
      rwa [Subgroup.coe_mul, Subgroup.coe_mul _ (A ^ i' * B ^ j'), hval, hval, Subgroup.coe_pow,
        Subgroup.coe_pow] at this
    obtain ⟨hee, hx⟩ := diagGL_mul_swapNegGL_pow_inj he he' h''
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    simp only [Pi.mul_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_pow, mul_one, one_mul] at h0 h1
    exact ⟨h0, h1, hee⟩

theorem exists_unitary_three_model_hyp (hK : UnitaryFieldData p f K)
    {G₀ : Matrix (Fin 3) (Fin 3) K} (M : GL (Fin 3) K)
    (hM : ctr hK.bar (M : Matrix (Fin 3) (Fin 3) K) * G₀ * (M : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 1, 0, 0; 0, 0, 1]) (z : Kˣ) :
    ∃ (u τ : SUgram hK.bar G₀),
      (u : GL (Fin 3) K) = M * diagGL ![z, z ^ (-(p ^ f : ℤ)), z ^ ((p ^ f : ℤ) - 1)] * M⁻¹ ∧
      (τ : GL (Fin 3) K) = M * swapNegGL * M⁻¹ ∧
      orderOf u = orderOf z ∧ τ ^ 2 = 1 ∧ τ⁻¹ * u * τ = u ^ (-(p ^ f : ℤ)) ∧
      ∀ i e i' e' : ℕ, e < 2 → e' < 2 → u ^ i * τ ^ e = u ^ i' * τ ^ e' →
        z ^ i = z ^ i' ∧ e = e' := by
  have := hK.finite
  have hF := card_eq_sq_of_unitaryFieldData hK
  have hq1 := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF
  set Q : ℤ := (p ^ f : ℤ) with hQ
  have hQn : ((p ^ f : ℕ) : ℤ) = Q := by rw [hQ]; push_cast; rfl
  have hzN : z ^ ((p ^ f) ^ 2 - 1) = 1 := by
    rw [← CFSG.ClassicalGroups.Unitary.card_units_of_card hF]
    exact pow_card_eq_one'
  have hzQ : z ^ (Q ^ 2 - 1) = 1 := by
    have h1 : (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) = Q ^ 2 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, hQn, Nat.cast_one]
    rw [← h1, zpow_natCast, hzN]
  have hzpow : ∀ m n : ℤ, (Q ^ 2 - 1) ∣ m - n → z ^ m = z ^ n := by
    rintro m n ⟨k, hk⟩
    rw [show m = n + (Q ^ 2 - 1) * k by linarith, _root_.zpow_add, _root_.zpow_mul, hzQ,
      _root_.one_zpow, mul_one]
  have hbar : ∀ m m' : ℤ, (Q ^ 2 - 1) ∣ m * Q + m' →
      hK.bar ((z ^ m : Kˣ) : K) * ((z ^ m' : Kˣ) : K) = 1 := by
    intro m m' hmm
    rw [hK.bar_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_add, hQn, hzpow _ 0 (by simpa using hmm), zpow_zero,
      Units.val_one]
  set d : Fin 3 → Kˣ := ![z, z ^ (-Q), z ^ (Q - 1)]
  have ha : diagGL d ∈ SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) :=
    diagGL_mem_SUgram_hyp
      (by have := hbar 1 (-Q) ⟨0, by ring⟩; rwa [zpow_one] at this)
      (by have := hbar (-Q) 1 ⟨-1, by ring⟩; rwa [zpow_one] at this)
      (hbar (Q - 1) (Q - 1) ⟨1, by ring⟩)
      (by
        rw [← Units.val_mul, ← Units.val_mul]
        simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [show z * z ^ (-Q) * z ^ (Q - 1) = 1 by group, Units.val_one])
  have ht := swapNegGL_mem_SUgram_hyp (K := K) hK.bar
  let ψ := (gramEquiv (τ := hK.bar) (G₁ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]) M hM).symm
  let A : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := ⟨_, ha⟩
  let T : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := ⟨_, ht⟩
  have hT : T ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact swapNegGL_sq)
  have hoA : orderOf A = orderOf z := by
    rw [Subgroup.orderOf_mk, ← diagGLHom_apply, orderOf_injective _ diagGL_injective]
    refine orderOf_eq_of_forall_zpow (i₀ := 0) rfl fun i => ?_
    fin_cases i
    exacts [⟨1, by simp [d]⟩, ⟨-Q, rfl⟩, ⟨Q - 1, rfl⟩]
  have hTA : T⁻¹ * A * T = A ^ (-Q) := Subtype.ext (by
    change swapNegGL⁻¹ * diagGL d * swapNegGL = diagGLHom 3 d ^ (-Q)
    rw [swapNegGL_conj_diagGL, ← map_zpow, diagGLHom_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · change z = (z ^ (-Q)) ^ (-Q)
      rw [← _root_.zpow_mul, neg_mul_neg, hzpow (Q * Q) 1 ⟨1, by ring⟩, zpow_one]
    · change z ^ (Q - 1) = (z ^ (Q - 1)) ^ (-Q)
      rw [← _root_.zpow_mul]
      exact hzpow _ _ ⟨1, by ring⟩)
  have hval : ∀ i : ℕ, ((A ^ i : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) = diagGL (d ^ i) := fun i => by
    rw [Subgroup.coe_pow]
    change diagGLHom 3 d ^ i = diagGLHom 3 (d ^ i)
    rw [map_pow]
  refine ⟨ψ A, ψ T, rfl, rfl, by rw [MulEquiv.orderOf_eq, hoA], by rw [← map_pow, hT, map_one],
    by rw [← map_inv, ← map_mul, ← map_mul, hTA, map_zpow], ?_⟩
  intro i e i' e' he he' h
  have h' : A ^ i * T ^ e = A ^ i' * T ^ e' :=
    ψ.injective (by simpa only [map_mul, map_pow] using h)
  have h'' : diagGL (d ^ i) * swapNegGL ^ e = diagGL (d ^ i') * swapNegGL ^ e' := by
    have := congrArg Subtype.val h'
    rwa [Subgroup.coe_mul, Subgroup.coe_mul _ (A ^ i'), hval, hval, Subgroup.coe_pow,
      Subgroup.coe_pow] at this
  obtain ⟨hee, hx⟩ := diagGL_mul_swapNegGL_pow_inj he he' h''
  have h0 := congrFun hx 0
  simp only [Pi.pow_apply, d, Matrix.cons_val_zero] at h0
  exact ⟨h0, hee⟩

end Models

section Main

open Matrix

variable {K : Type} [Field K]

private theorem pow_mul_pow_mul_pow_mem_closure {G : Type*} [Group G] (u v t : G) (i j e : ℕ) :
    u ^ i * v ^ j * t ^ e ∈ Subgroup.closure {u, v, t} :=
  mul_mem (mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _)) (pow_mem (Subgroup.subset_closure (by simp)) _)

private theorem pow_mul_pow_mem_closure {G : Type*} [Group G] (u t : G) (i e : ℕ) :
    u ^ i * t ^ e ∈ Subgroup.closure {u, t} :=
  mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem odd_unitary_three_exact_coordinate_and_Sylow_models {p f : ℕ}
    (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2) {G₀ : Matrix (Fin 3) (Fin 3) K}
    (hG : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (hdet : G₀.det ≠ 0)
    (D : Subgroup (SUgram hK.bar G₀)) [D.Normal]
    (hD : D ≤ (StatedScalars (Fin 3) K).subgroupOf (SUgram hK.bar G₀)) :
    (∃ P : GL (Fin 3) K, ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * G₀ *
      (P : Matrix (Fin 3) (Fin 3) K) = 1) ∧
    (∀ P : GL (Fin 3) K, ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * G₀ *
        (P : Matrix (Fin 3) (Fin 3) K) = 1 → ∀ c : Fin 3,
      Nonempty (coordPairSubgroup hK.bar G₀ P c ≃*
        Matrix.SpecialLinearGroup (Fin 2) hK.fixedField) ∧
      Function.Injective ((QuotientGroup.mk' D).comp (coordPairSubgroup hK.bar G₀ P c).subtype)) ∧
    (Nat.card ((StatedScalars (Fin 3) K).subgroupOf (SUgram hK.bar G₀)) ∣ 3 ∧
      Odd (Nat.card ((StatedScalars (Fin 3) K).subgroupOf (SUgram hK.bar G₀)))) ∧
    (ordProj[2] (Nat.card (SUgram hK.bar G₀)) =
        ordProj[2] (p ^ f - 1) * (ordProj[2] (p ^ f + 1)) ^ 2 ∧
      ordProj[2] (Nat.card (SUgram hK.bar G₀ ⧸ D)) =
        ordProj[2] (p ^ f - 1) * (ordProj[2] (p ^ f + 1)) ^ 2) ∧
    (p ^ f % 4 = 3 → (∃ l : Kˣ, hK.bar l * l = 1 ∧ orderOf l = ordProj[2] (p ^ f + 1)) ∧
      ∀ P : GL (Fin 3) K, ctr hK.bar (P : Matrix (Fin 3) (Fin 3) K) * G₀ *
        (P : Matrix (Fin 3) (Fin 3) K) = 1 →
      ∀ l : Kˣ, hK.bar l * l = 1 → orderOf l = ordProj[2] (p ^ f + 1) →
        ∃ (u v τ : SUgram hK.bar G₀),
          (u : GL (Fin 3) K) = P * diagGL ![l, 1, l⁻¹] * P⁻¹ ∧
          (v : GL (Fin 3) K) = P * diagGL ![1, l, l⁻¹] * P⁻¹ ∧
          (τ : GL (Fin 3) K) = P * swapNegGL * P⁻¹ ∧
          v = τ⁻¹ * u * τ ∧ Commute u v ∧ orderOf u = ordProj[2] (p ^ f + 1) ∧
          orderOf v = ordProj[2] (p ^ f + 1) ∧ τ ^ 2 = 1 ∧
          u ∈ coordPairSubgroup hK.bar G₀ P 1 ∧ v ∈ coordPairSubgroup hK.bar G₀ P 0 ∧
          Function.Injective (fun x : Fin (ordProj[2] (p ^ f + 1)) ×
              Fin (ordProj[2] (p ^ f + 1)) × Fin 2 =>
            u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ)) ∧
          (∀ w ∈ Subgroup.closure {u, v, τ}, ∃ i j e : ℕ, i < ordProj[2] (p ^ f + 1) ∧
            j < ordProj[2] (p ^ f + 1) ∧ e < 2 ∧ w = u ^ i * v ^ j * τ ^ e) ∧
          IsPGroup 2 (Subgroup.closure {u, v, τ}) ∧
          Nat.card (Subgroup.closure {u, v, τ}) = ordProj[2] (Nat.card (SUgram hK.bar G₀)) ∧
          Set.InjOn (QuotientGroup.mk' D) (Subgroup.closure {u, v, τ} : Set (SUgram hK.bar G₀)) ∧
          IsPGroup 2 ((Subgroup.closure {u, v, τ}).map (QuotientGroup.mk' D)) ∧
          Nat.card ((Subgroup.closure {u, v, τ}).map (QuotientGroup.mk' D)) =
            ordProj[2] (Nat.card (SUgram hK.bar G₀ ⧸ D))) ∧
    (p ^ f % 4 = 1 → (∃ z : Kˣ, orderOf z = 2 * ordProj[2] (p ^ f - 1)) ∧
      (∃ M : GL (Fin 3) K, ctr hK.bar (M : Matrix (Fin 3) (Fin 3) K) * G₀ *
        (M : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1]) ∧
      ∀ M : GL (Fin 3) K, ctr hK.bar (M : Matrix (Fin 3) (Fin 3) K) * G₀ *
        (M : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] →
      ∀ z : Kˣ, orderOf z = 2 * ordProj[2] (p ^ f - 1) →
        ∃ (u τ : SUgram hK.bar G₀),
          (u : GL (Fin 3) K) = M * diagGL ![z, z ^ (-(p ^ f : ℤ)), z ^ ((p ^ f : ℤ) - 1)] * M⁻¹ ∧
          (τ : GL (Fin 3) K) = M * swapNegGL * M⁻¹ ∧
          orderOf u = 2 * ordProj[2] (p ^ f - 1) ∧ τ ^ 2 = 1 ∧
          τ⁻¹ * u * τ = u ^ (-(p ^ f : ℤ)) ∧
          Function.Injective (fun x : Fin (2 * ordProj[2] (p ^ f - 1)) × Fin 2 =>
            u ^ (x.1 : ℕ) * τ ^ (x.2 : ℕ)) ∧
          (∀ w ∈ Subgroup.closure {u, τ}, ∃ i e : ℕ, i < 2 * ordProj[2] (p ^ f - 1) ∧ e < 2 ∧
            w = u ^ i * τ ^ e) ∧
          IsPGroup 2 (Subgroup.closure {u, τ}) ∧
          Nat.card (Subgroup.closure {u, τ}) = ordProj[2] (Nat.card (SUgram hK.bar G₀)) ∧
          Set.InjOn (QuotientGroup.mk' D) (Subgroup.closure {u, τ} : Set (SUgram hK.bar G₀)) ∧
          IsPGroup 2 ((Subgroup.closure {u, τ}).map (QuotientGroup.mk' D)) ∧
          Nat.card ((Subgroup.closure {u, τ}).map (QuotientGroup.mk' D)) =
            ordProj[2] (Nat.card (SUgram hK.bar G₀ ⧸ D))) := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  have hS := ordProj_two_card_SUgram hK hp2 hG hdet
  have hZ := card_scalars_SUgram_dvd_three hK.bar G₀
  have hD3 : ∀ d ∈ D, d ^ 3 = 1 := fun d hd =>
    pow_three_eq_one_of_mem_statedScalars (fun _ hx => det_eq_one_of_mem_SUgram hx) (hD hd)
  have hDodd : Odd (Nat.card D) :=
    Odd.of_dvd_nat (by decide) ((Subgroup.card_dvd_of_le hD).trans hZ)
  have hQ := ordProj_two_card_quotient_of_odd D hDodd
  refine ⟨exists_ctr_mul_mul_eq_one hK hG hdet, fun P hP c =>
    ⟨nonempty_coordPairSubgroup_mulEquiv hK P hP c,
      injective_mk'_comp_coordPairSubgroup_subtype P c D hD⟩,
    ⟨hZ, Odd.of_dvd_nat (by decide) hZ⟩, ⟨hS, hQ.trans hS⟩, fun hq => ?_, fun hq => ?_⟩
  ·
    refine ⟨exists_norm_one_orderOf_eq_ordProj hK, fun P hP l hl hlo => ?_⟩
    obtain ⟨u, v, τ, hu, hv, hτ, hvu, huv, hou, hov, hτ2, hu1, hv0, hinj⟩ :=
      exists_unitary_three_model_of_norm_one hK P hP l hl
    set s := ordProj[2] (p ^ f + 1) with hs
    have hs0 : 0 < s := Nat.ordProj_pos _ _
    have hφ : Function.Injective (fun x : Fin s × Fin s × Fin 2 =>
        u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ)) := by
      rintro ⟨i, j, e⟩ ⟨i', j', e'⟩ h
      obtain ⟨h1, h2, h3⟩ := hinj i j e i' j' e' e.2 e'.2 h
      have hi : (i : ℕ) = i' := pow_injOn_Iio_orderOf (by rw [hlo]; exact i.2)
        (by rw [hlo]; exact i'.2) h1
      have hj : (j : ℕ) = j' := pow_injOn_Iio_orderOf (by rw [hlo]; exact j.2)
        (by rw [hlo]; exact j'.2) h2
      rw [Fin.ext hi, Fin.ext hj, Fin.ext h3]
    have hnf : ∀ w ∈ Subgroup.closure {u, v, τ}, ∃ i j e : ℕ, i < s ∧ j < s ∧ e < 2 ∧
        w = u ^ i * v ^ j * τ ^ e := by
      intro w hw
      obtain ⟨i, j, e, he, rfl⟩ := exists_zpow_mul_zpow_mul_pow huv hvu hτ2 hw
      obtain ⟨i', hi', hii⟩ := exists_lt_orderOf_zpow_eq (x := u) (by rw [hou, hlo]; exact hs0) i
      obtain ⟨j', hj', hjj⟩ := exists_lt_orderOf_zpow_eq (x := v) (by rw [hov, hlo]; exact hs0) j
      rw [hou, hlo] at hi'
      rw [hov, hlo] at hj'
      exact ⟨i', j', e, hi', hj', he, by rw [hii, hjj]⟩
    have hcardW : Nat.card (Subgroup.closure ({u, v, τ} : Set (SUgram hK.bar G₀))) =
        s * (s * 2) := by
      refine (Nat.card_eq_of_bijective (fun x : Fin s × Fin s × Fin 2 =>
        (⟨u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ),
          pow_mul_pow_mul_pow_mem_closure u v τ _ _ _⟩ :
            Subgroup.closure ({u, v, τ} : Set (SUgram hK.bar G₀)))) ⟨fun x y h => hφ
          (congrArg Subtype.val h), fun w => ?_⟩).symm.trans ?_
      · obtain ⟨i, j, e, hi, hj, he, hw⟩ := hnf w w.2
        exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨e, he⟩), Subtype.ext hw.symm⟩
      · rw [Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin]
    have hW2 : IsPGroup 2 (Subgroup.closure ({u, v, τ} : Set (SUgram hK.bar G₀))) :=
      IsPGroup.of_card (n := (p ^ f + 1).factorization 2 + ((p ^ f + 1).factorization 2 + 1))
        (by rw [hcardW, pow_add, pow_succ])
    have hcard : Nat.card (Subgroup.closure ({u, v, τ} : Set (SUgram hK.bar G₀))) =
        ordProj[2] (Nat.card (SUgram hK.bar G₀)) := by
      rw [hcardW, hS, ordProj_two_sub_one_of_mod_four_eq_three hq]
      ring
    exact ⟨u, v, τ, hu, hv, hτ, hvu, huv, hou.trans hlo, hov.trans hlo, hτ2, hu1, hv0, hφ, hnf,
      hW2, hcard, injOn_mk'_of_isPGroup_two hD3 hW2, hW2.map _,
      (card_map_mk'_of_isPGroup_two hD3 hW2).trans (hcard.trans hQ.symm)⟩
  ·
    refine ⟨exists_orderOf_eq_two_mul_ordProj hK hq, exists_ctr_mul_mul_eq_hyp hK hG hdet,
      fun M hM z hz => ?_⟩
    obtain ⟨u, τ, hu, hτ, hou, hτ2, hτu, hinj⟩ := exists_unitary_three_model_hyp hK M hM z
    set n := 2 * ordProj[2] (p ^ f - 1) with hn
    have hn0 : 0 < n := Nat.mul_pos two_pos (Nat.ordProj_pos _ _)
    have hφ : Function.Injective (fun x : Fin n × Fin 2 => u ^ (x.1 : ℕ) * τ ^ (x.2 : ℕ)) := by
      rintro ⟨i, e⟩ ⟨i', e'⟩ h
      obtain ⟨h1, h2⟩ := hinj i e i' e' e.2 e'.2 h
      have hi : (i : ℕ) = i' := pow_injOn_Iio_orderOf (by rw [hz]; exact i.2)
        (by rw [hz]; exact i'.2) h1
      rw [Fin.ext hi, Fin.ext h2]
    have hnf : ∀ w ∈ Subgroup.closure {u, τ}, ∃ i e : ℕ, i < n ∧ e < 2 ∧ w = u ^ i * τ ^ e := by
      intro w hw
      obtain ⟨i, e, he, rfl⟩ := exists_zpow_mul_pow hτ2 hτu hw
      obtain ⟨i', hi', hii⟩ := exists_lt_orderOf_zpow_eq (x := u) (by rw [hou, hz]; exact hn0) i
      rw [hou, hz] at hi'
      exact ⟨i', e, hi', he, by rw [hii]⟩
    have hcardW : Nat.card (Subgroup.closure ({u, τ} : Set (SUgram hK.bar G₀))) = n * 2 := by
      refine (Nat.card_eq_of_bijective (fun x : Fin n × Fin 2 =>
        (⟨u ^ (x.1 : ℕ) * τ ^ (x.2 : ℕ), pow_mul_pow_mem_closure u τ _ _⟩ :
          Subgroup.closure ({u, τ} : Set (SUgram hK.bar G₀)))) ⟨fun x y h => hφ
          (congrArg Subtype.val h), fun w => ?_⟩).symm.trans ?_
      · obtain ⟨i, e, hi, he, hw⟩ := hnf w w.2
        exact ⟨(⟨i, hi⟩, ⟨e, he⟩), Subtype.ext hw.symm⟩
      · rw [Nat.card_prod, Nat.card_fin, Nat.card_fin]
    have hW2 : IsPGroup 2 (Subgroup.closure ({u, τ} : Set (SUgram hK.bar G₀))) :=
      IsPGroup.of_card (n := (p ^ f - 1).factorization 2 + 2)
        (by rw [hcardW, hn, pow_add]; ring)
    have hcard : Nat.card (Subgroup.closure ({u, τ} : Set (SUgram hK.bar G₀))) =
        ordProj[2] (Nat.card (SUgram hK.bar G₀)) := by
      rw [hcardW, hS, ordProj_two_add_one_of_mod_four_eq_one hq, hn]
      ring
    exact ⟨u, τ, hu, hτ, hou.trans hz, hτ2, hτu, hφ, hnf, hW2, hcard,
      injOn_mk'_of_isPGroup_two hD3 hW2, hW2.map _,
      (card_map_mk'_of_isPGroup_two hD3 hW2).trans (hcard.trans hQ.symm)⟩

end Main

end CFSG.LieType.Steinberg
