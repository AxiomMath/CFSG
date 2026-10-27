module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (blockOn compInd compInd_mul_apply
  mul_compInd_apply compInd_apply signMat signMat_mul_self signGL coe_signGL blockScalarGL
  coe_blockScalarGL rotSL coe_rotSL rotSL_mem_unitarySL diagSL diagSL_mem_unitarySL
  mem_unitarySL vecMulVec_mul_self det_one_add_smul_vecMulVec)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def barEq : K ≃+* K :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barEq_apply (c : K) : barEq h c = h.bar c := rfl

theorem map_bar (τ : K ≃+* K) (c : K) : τ (h.bar c) = h.bar (τ c) := by
  rw [h.bar_apply, h.bar_apply, map_pow]

theorem eq_one_of_odd_of_fix {τ : K ≃+* K} {m : ℕ} (hm : Odd m) (hτm : τ ^ m = 1)
    (hfix : ∀ c, h.bar c = c → τ c = c) : τ = 1 := by
  have hroot : ∀ x, τ x = x ∨ τ x = h.bar x := by
    intro x
    have e1 := hfix (x + h.bar x) (by rw [map_add, h.bar_bar, add_comm])
    have e2 := hfix (x * h.bar x) (by rw [map_mul, h.bar_bar, mul_comm])
    rw [map_add, map_bar] at e1
    rw [map_mul, map_bar] at e2
    have e3 : (τ x - x) * (τ x - h.bar x) = 0 := by
      linear_combination (τ x) * e1 - e2 - τ x * e1 + τ x * e1
    rcases mul_eq_zero.1 e3 with e | e
    · exact Or.inl (sub_eq_zero.1 e)
    · exact Or.inr (sub_eq_zero.1 e)
  have hsq : τ * τ = 1 := by
    refine RingEquiv.ext fun x => ?_
    change τ (τ x) = x
    rcases hroot x with e | e
    · rw [e, e]
    · rw [e, map_bar, e, h.bar_bar]
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at hτm
  exact hτm

theorem commute_of_odd_of_ker {U T : Type*} [Group U] [Group T] (c : U →* T)
    (hker : ∀ x, c x = 1 → ∀ g, x * g = g * x) {D D₀ : U} (hD₀ : c (D₀ * D₀) = 1)
    (hodd : Odd (orderOf (c D))) (hc : c D * c D₀ = c D₀ * c D) : D * D₀ = D₀ * D := by
  set L := D * D₀ * D⁻¹ * D₀⁻¹ with hLdef
  have hL : c L = 1 := by
    rw [hLdef, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hLc := hker L hL
  have hDD : D * D₀ * D⁻¹ = L * D₀ := by rw [hLdef]; group
  have hD₀c := hker _ hD₀
  have hL2 : L * L = 1 := by
    have e1 : (L * D₀) * (L * D₀) = (L * L) * (D₀ * D₀) := by
      calc (L * D₀) * (L * D₀) = L * (D₀ * L) * D₀ := by group
        _ = L * (L * D₀) * D₀ := by rw [hLc D₀]
        _ = (L * L) * (D₀ * D₀) := by group
    have e2 : (L * D₀) * (L * D₀) = D * (D₀ * D₀) * D⁻¹ := by rw [← hDD]; group
    have e3 : D * (D₀ * D₀) * D⁻¹ = D₀ * D₀ := by rw [← hD₀c D, mul_inv_cancel_right]
    rw [e2, e3] at e1
    exact mul_right_cancel (b := D₀ * D₀) (e1.symm.trans (one_mul _).symm)
  have hpow : ∀ k : ℕ, D ^ k * D₀ * (D ^ k)⁻¹ = L ^ k * D₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc D ^ (k + 1) * D₀ * (D ^ (k + 1))⁻¹ = D * (D ^ k * D₀ * (D ^ k)⁻¹) * D⁻¹ := by
            rw [pow_succ']
            group
        _ = D * (L ^ k * D₀) * D⁻¹ := by rw [ih]
        _ = L ^ k * (D * D₀ * D⁻¹) := by
            have hLk : ∀ g, L ^ k * g = g * L ^ k := fun g =>
              ((Commute.pow_left (hLc g) k).eq)
            rw [← mul_assoc, ← hLk D]
            group
        _ = L ^ (k + 1) * D₀ := by rw [hDD, ← mul_assoc, pow_succ]
  set m := orderOf (c D) with hm
  have hDm : c (D ^ m) = 1 := by rw [map_pow, hm, pow_orderOf_eq_one]
  have hLm : L ^ m = 1 := by
    have e := hpow m
    rw [hker _ hDm D₀, mul_inv_cancel_right] at e
    exact mul_right_cancel (b := D₀) (e.symm.trans (one_mul _).symm)
  obtain ⟨k, hk⟩ := hodd
  have hL1 : L = 1 := by
    have e : L ^ m = L * (L * L) ^ k := by rw [hk, pow_succ', pow_mul, pow_two]
    rw [hLm, hL2, one_pow, mul_one] at e
    exact e.symm
  rw [hL1, one_mul] at hDD
  calc D * D₀ = D * D₀ * D⁻¹ * D := by group
    _ = D₀ * D := by rw [hDD]

theorem uConjAut_ker_central (hn : 3 ≤ n) (A : uU h n) (hA : uConjAut h (by omega) A = 1)
    (g : uU h n) : A * g = g * A := by
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn A).1 hA
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact ((commute_scalar c (g : GL (Fin n) K)).eq).symm

theorem uCommute_of_odd (hn : 3 ≤ n) {D D₀ : uU h n}
    (hD₀ : uConjAut h (by omega) (D₀ * D₀) = 1) (hodd : Odd (orderOf (uConjAut h (by omega) D)))
    (hc : uConjAut h (by omega) D * uConjAut h (by omega) D₀ =
      uConjAut h (by omega) D₀ * uConjAut h (by omega) D) : D * D₀ = D₀ * D :=
  commute_of_odd_of_ker (uConjAut h (by omega)) (uConjAut_ker_central h hn) hD₀ hodd hc

theorem fieldAut_pow_eq_one (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) {A : uU h n}
    {φ : K ≃+* K} {m : ℕ} (hm : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ m = 1) :
    φ ^ m = 1 := by
  have := congrArg (uFactor h hn hq) hm
  rwa [map_pow, uFactor_apply, map_one] at this

@[expose] def uGL (M : Matrix (Fin n) (Fin n) K) (hM : (M.map h.bar)ᵀ * M = 1) : GL (Fin n) K :=
  ⟨M, (M.map h.bar)ᵀ, mul_eq_one_comm.1 hM, hM⟩

theorem coe_uGL (M : Matrix (Fin n) (Fin n) K) (hM : (M.map h.bar)ᵀ * M = 1) :
    ((uGL h M hM : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := rfl

theorem uGL_mem (M : Matrix (Fin n) (Fin n) K) (hM : (M.map h.bar)ᵀ * M = 1) :
    uGL h M hM ∈ uU h n := (mem_uU h).2 hM

@[expose] def uSUmk (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hM : (M.map h.bar)ᵀ * M = 1) : StatedSU n (p ^ f) K :=
  ⟨uGL h M hM, (mem_unitarySU_iff h).2 ⟨hdet, hM⟩⟩

theorem coe_uSUmk (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hM : (M.map h.bar)ᵀ * M = 1) :
    (((uSUmk h M hdet hM : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      M := rfl

theorem map_signMat (φ : K →+* K) (J : Finset (Fin n)) : (signMat K J).map φ = signMat K J := by
  ext a b
  simp only [signMat, map_apply, diagonal_apply]
  split_ifs <;> simp

@[expose] def uSign (J : Finset (Fin n)) : uU h n :=
  ⟨signGL K J, (mem_uU h).2 (by
    rw [coe_signGL, map_signMat, signMat, diagonal_transpose, ← signMat, signMat_mul_self])⟩

theorem coe_uSign (J : Finset (Fin n)) :
    (((uSign h J : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = signMat K J := rfl

theorem uSign_mul_self (J : Finset (Fin n)) : uSign h J * uSign h J = 1 :=
  Subtype.ext (Units.ext (signMat_mul_self J))

@[expose] def uDiagJ (J : Finset (Fin n)) (a b : Kˣ) (ha : h.norm (a : K) = 1)
    (hb : h.norm (b : K) = 1) : uU h n :=
  ⟨blockScalarGL J a b, (mem_uU h).2 (by
    rw [coe_blockScalarGL, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    ext i
    split_ifs
    · rw [mul_comm]; exact ha
    · rw [mul_comm]; exact hb)⟩

theorem coe_uDiagJ (J : Finset (Fin n)) (a b : Kˣ) (ha : h.norm (a : K) = 1)
    (hb : h.norm (b : K) = 1) :
    (((uDiagJ h J a b ha hb : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => if i ∈ J then (a : K) else b := rfl

theorem exists_uTr {v : Fin n → K} (hv : (fun k => h.bar (v k)) ⬝ᵥ v = 0) {η : K}
    (hη : h.bar η = -η) : ∃ g : StatedSU n (p ^ f) K,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + η • vecMulVec v (fun k => h.bar (v k)) := by
  set w : Fin n → K := fun k => h.bar (v k) with hw
  set V := vecMulVec v w with hV
  have hVV : V * V = 0 := vecMulVec_mul_self hv
  have hmap : ((1 + η • V).map h.bar)ᵀ = 1 - η • V := by
    ext x y
    rw [transpose_apply, map_apply]
    simp only [hV, hw, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, map_add, map_mul, hη, h.bar_bar, one_apply]
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte, map_one]
      ring
    · simp only [Ne.symm hxy, hxy, ↓reduceIte, map_zero]
      ring
  have hU : ((1 + η • V).map h.bar)ᵀ * (1 + η • V) = 1 := by
    rw [hmap]
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hVV, smul_zero, sub_zero, sub_add_cancel]
  exact ⟨uSUmk h (1 + η • V) (det_one_add_smul_vecMulVec hv η) hU, rfl⟩

@[expose] def uRot {i j : Fin n} (hij : i ≠ j) : StatedSU n (p ^ f) K :=
  uSUmk h ((rotSL hij : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    (rotSL hij).2 (mem_unitarySL.1 (rotSL_mem_unitarySL (barEq h) hij))

theorem coe_uRot {i j : Fin n} (hij : i ≠ j) :
    (((uRot h hij : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 - single i i 1 - single j j 1 + single i j 1 - single j i 1 :=
  coe_rotSL hij

@[expose] def uDiag2 {i j : Fin n} (hij : i ≠ j) {ζ : K} (hζ0 : ζ ≠ 0) (hζ : h.norm ζ = 1) :
    StatedSU n (p ^ f) K :=
  uSUmk h ((diagSL hij hζ0 : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    (diagSL hij hζ0).2 (mem_unitarySL.1 (diagSL_mem_unitarySL (σ := barEq h) hij hζ0
      (by rw [barEq_apply, mul_comm]; exact hζ)))

theorem coe_uDiag2 {i j : Fin n} (hij : i ≠ j) {ζ : K} (hζ0 : ζ ≠ 0) (hζ : h.norm ζ = 1) :
    (((uDiag2 h hij hζ0 hζ : StatedSU n (p ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      diagonal fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1 := rfl

theorem uRot_mem_uBlock {I : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∈ I)
    (hj : j ∈ I) : uRot h hij ∈ uBlock p f K I := by
  rw [mem_uBlock_iff]
  intro x y hxy
  rw [coe_uRot]
  have hx : ¬ (x = i ∧ y = i) ∧ ¬ (x = j ∧ y = j) ∧ ¬ (x = i ∧ y = j) ∧ ¬ (x = j ∧ y = i) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨rfl, rfl⟩ <;> tauto
  simp only [Matrix.add_apply, Matrix.sub_apply, single_apply, one_apply]
  obtain ⟨h1, h2, h3, h4⟩ := hx
  simp only [eq_comm (a := i), eq_comm (a := j)] at h1 h2 h3 h4 ⊢
  split_ifs <;> simp_all

theorem uDiag2_mem_uBlock {I : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∈ I)
    (hj : j ∈ I) {ζ : K} (hζ0 : ζ ≠ 0) (hζ : h.norm ζ = 1) :
    uDiag2 h hij hζ0 hζ ∈ uBlock p f K I := by
  rw [mem_uBlock_iff]
  intro x y hxy
  rw [coe_uDiag2, diagonal_apply]
  by_cases hxy' : x = y
  · subst hxy'
    have hxi : x ≠ i := by rintro rfl; tauto
    have hxj : x ≠ j := by rintro rfl; tauto
    simp [hxi, hxj]
  · simp [hxy']

theorem exists_norm_one_sq_ne_one : ∃ ζ : K, ζ ≠ 0 ∧ h.norm ζ = 1 ∧ ζ ^ 2 ≠ 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨l, hl, hlo⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq h.card_eq_sq
  refine ⟨l, l.ne_zero, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, mul_comm, h.bar_apply,
      ← CFSG.LieType.BorelTits.unitaryInvolution_apply]
    exact hl
  · intro h2
    have hl2 : l ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h2, Units.val_one])
    have hdvd := orderOf_dvd_of_pow_eq_one hl2
    rw [hlo] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have : 2 ≤ p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
    omega

theorem exists_norm_neg_one : ∃ μ : K, h.norm μ = -1 := by
  obtain ⟨μ, hμ⟩ := h.normHom_surjective ⟨-1, by
    rw [UnitaryFieldData.mem_fixedField, map_neg, map_one]⟩
  exact ⟨μ, congrArg Subtype.val hμ⟩

theorem exists_skew : ∃ η : K, η ≠ 0 ∧ h.bar η = -η := by
  obtain ⟨η, hη, hη0⟩ := h.exists_mem_traceZero_ne_zero
  refine ⟨η, hη0, ?_⟩
  have := (h.mem_traceZero).1 hη
  rw [UnitaryFieldData.trace] at this
  linear_combination this

theorem entries_of_commute_diag {i j : Fin n} {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ2 : ζ ^ 2 ≠ 1) {D : Matrix (Fin n) (Fin n) K}
    (hc : D * diagonal (fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1) =
      diagonal (fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1) * D) :
    ∀ y, y ≠ i → D i y = 0 ∧ D y i = 0 := by
  intro y hy
  have hne : (if y = j then ζ⁻¹ else 1) - ζ ≠ 0 := by
    intro h0
    split_ifs at h0 with hyj
    · apply hζ2
      have : ζ⁻¹ = ζ := sub_eq_zero.1 h0
      field_simp at this
      linear_combination -this
    · apply hζ2
      have : (1 : K) = ζ := sub_eq_zero.1 h0
      rw [← this, one_pow]
  have e1 := congrFun (congrFun hc i) y
  have e2 := congrFun (congrFun hc y) i
  simp only [mul_diagonal, diagonal_mul, hy, ↓reduceIte] at e1 e2
  constructor
  · have : D i y * ((if y = j then ζ⁻¹ else 1) - ζ) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_right hne
  · have : D y i * ((if y = j then ζ⁻¹ else 1) - ζ) = 0 := by linear_combination -e2
    exact (mul_eq_zero.1 this).resolve_right hne

theorem diag_eq_of_commute_rot {i j : Fin n} (hij : i ≠ j) {D : Matrix (Fin n) (Fin n) K}
    (hc : D * (1 - single i i 1 - single j j 1 + single i j 1 - single j i 1) =
      (1 - single i i 1 - single j j 1 + single i j 1 - single j i 1) * D)
    (hoff : D i j = 0) : D i i = D j j := by
  have e := congrFun (congrFun hc i) j
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.add_apply, Matrix.sub_apply, mul_single_apply_same,
    single_mul_apply_same, mul_one, one_mul, mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hij),
    single_mul_apply_of_ne _ _ _ _ _ hij] at e
  rw [hoff] at e
  linear_combination e

include h in
theorem eq_of_commute_uBlock {I : Finset (Fin n)} (hI : 2 ≤ I.card) {D : Matrix (Fin n) (Fin n) K}
    (hc : ∀ g ∈ uBlock p f K I, D * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D) :
    (∀ i ∈ I, ∀ y, y ≠ i → D i y = 0 ∧ D y i = 0) ∧ ∀ i ∈ I, ∀ j ∈ I, D i i = D j j := by
  obtain ⟨ζ, hζ0, hζ, hζ2⟩ := exists_norm_one_sq_ne_one h
  have hoff : ∀ i ∈ I, ∀ y, y ≠ i → D i y = 0 ∧ D y i = 0 := by
    intro i hi
    obtain ⟨j, hj, hji⟩ : ∃ j ∈ I, j ≠ i := by
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hI
      by_cases hai : a = i
      · exact ⟨b, hb, fun h => hab (hai.trans h.symm)⟩
      · exact ⟨a, ha, hai⟩
    have e := hc _ (uDiag2_mem_uBlock h (Ne.symm hji) hi hj hζ0 hζ)
    rw [coe_uDiag2] at e
    exact entries_of_commute_diag hζ0 hζ2 e
  refine ⟨hoff, fun i hi j hj => ?_⟩
  by_cases hij : i = j
  · rw [hij]
  have e := hc _ (uRot_mem_uBlock h hij hi hj)
  rw [coe_uRot] at e
  exact diag_eq_of_commute_rot hij e ((hoff i hi j (Ne.symm hij)).1)

theorem fix_of_conj_family {D : GL (Fin n) K} {τ : K ≃+* K} {N : Matrix (Fin n) (Fin n) K}
    {a b : Fin n} (hab : N a b ≠ 0)
    (hD : ∀ c, h.bar c = c → (D : Matrix (Fin n) (Fin n) K) * (1 + c • N).map τ *
      ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + c • N) :
    ∀ c, h.bar c = c → τ c = c := by
  set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hM
  set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have h1M : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmap : ∀ c, (1 + c • N).map τ = 1 + τ c • N.map τ := by
    intro c
    ext x y
    simp only [map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      one_apply]
    split_ifs <;> simp
  have key : ∀ c, h.bar c = c → τ c • (M * N.map τ * Mi) = c • N := by
    intro c hc
    have e := hD c hc
    rw [hmap, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1M, Matrix.mul_smul,
      Matrix.smul_mul] at e
    exact add_left_cancel e
  have e1 := key 1 (map_one _)
  rw [map_one, one_smul, one_smul] at e1
  intro c hc
  have e2 := key c hc
  rw [e1] at e2
  have := congrFun (congrFun e2 a) b
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hab this

end CFSG.ComponentClassification.Burgoyne.U
