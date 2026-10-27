module

public import CFSG.CharacterTheory.Semidihedral.MatrixTorus

public section

namespace CFSG.Semidihedral.AllPrime.QDTI

noncomputable section

open Matrix CFSG.Semidihedral CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.MatrixTorus

variable {F : Type} [Field F]

theorem sl_inv_val (X : SL F) :
    (X⁻¹).1 = !![X.1 1 1, -X.1 0 1; -X.1 1 0, X.1 0 0] := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sl_det (X : SL F) : X.1 0 0 * X.1 1 1 - X.1 0 1 * X.1 1 0 = 1 := by
  have h := X.2
  rwa [Matrix.det_fin_two] at h

theorem sl_mul_val (X Y : SL F) (i j : Fin 2) :
    (X * Y).1 i j = X.1 i 0 * Y.1 0 j + X.1 i 1 * Y.1 1 j := by
  change (X.1 * Y.1) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl_pow_val (X : SL F) (k : ℕ) : (X ^ k).1 = X.1 ^ k :=
  Matrix.SpecialLinearGroup.coe_pow X k

theorem sl_ext {X Y : SL F} (h00 : X.1 0 0 = Y.1 0 0) (h01 : X.1 0 1 = Y.1 0 1)
    (h10 : X.1 1 0 = Y.1 1 0) (h11 : X.1 1 1 = Y.1 1 1) : X = Y := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem sl_one_val (i j : Fin 2) : (1 : SL F).1 i j = if i = j then 1 else 0 := by
  change (1 : Matrix (Fin 2) (Fin 2) F) i j = _
  rw [Matrix.one_apply]

theorem J_val (a : Fˣ) :
    (J F a : Matrix (Fin 2) (Fin 2) F) = !![0, -(a : F); 1, 0] := J_matrix F a

theorem beta_eq_iff (a : Fˣ) (X Y : SL F) :
    beta F a X = Y ↔
      (J F a : Matrix (Fin 2) (Fin 2) F) * X.1 = Y.1 * (J F a : Matrix (Fin 2) (Fin 2) F) := by
  rw [← SpecialLinearGroup.toGL_inj]
  change SpecialLinearGroup.toGL (slConjugation F (J F a) X) = _ ↔ _
  rw [slConjugation_toGL, mul_inv_eq_iff_eq_mul, Units.ext_iff]
  rfl

theorem beta_eq_inv_iff (a : Fˣ) (X : SL F) :
    beta F a X = X⁻¹ ↔ X.1 0 1 = (a : F) * X.1 1 0 := by
  rw [beta_eq_iff, sl_inv_val, J_val]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    linear_combination -h00
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h] <;> ring

theorem beta_eq_neg_iff (a : Fˣ) (X : SL F) :
    beta F a X = OddFieldSL2.minusIdentity F * X ↔
      X.1 0 1 = (a : F) * X.1 1 0 ∧ X.1 1 1 = -X.1 0 0 := by
  have hm : (OddFieldSL2.minusIdentity F * X).1 = -X.1 := by
    change (OddFieldSL2.minusIdentity F).1 * X.1 = -X.1
    rw [show (OddFieldSL2.minusIdentity F).1 = Matrix.scalar (Fin 2) (-1) from
      OddFieldSL2.minusIdentity_matrix F, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    simp
  rw [beta_eq_iff, hm, J_val]
  have ha : (a : F) ≠ 0 := a.ne_zero
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    refine ⟨by linear_combination -h00, ?_⟩
    have : (a : F) * (X.1 1 1 + X.1 0 0) = 0 := by linear_combination -h01
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha
    · linear_combination h
  · rintro ⟨h01, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h11] <;> ring

theorem comm_entry (a : Fˣ) (Y τ : SL F) (hY : Y.1 0 1 = (a : F) * Y.1 1 0)
    (hτ : τ ∈ Torus F a) :
    (Y * (τ * Y * τ⁻¹)).1 1 0 - ((τ * Y * τ⁻¹) * Y).1 1 0 =
      -(τ.1 0 0 * τ.1 1 0) * ((Y.1 0 0 - Y.1 1 1) ^ 2 + 4 * (a : F) * Y.1 1 0 ^ 2) := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a τ).mp hτ
  simp only [sl_mul_val, sl_inv_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [hY, h01, h11]
  ring

theorem disc_eq_zero (a : Fˣ) (Y τ : SL F) (hY : Y.1 0 1 = (a : F) * Y.1 1 0)
    (hτ : τ ∈ Torus F a) (hτxy : τ.1 0 0 * τ.1 1 0 ≠ 0)
    (hcomm : Y * (τ * Y * τ⁻¹) = (τ * Y * τ⁻¹) * Y) :
    (Y.1 0 0 - Y.1 1 1) ^ 2 + 4 * (a : F) * Y.1 1 0 ^ 2 = 0 := by
  have h := comm_entry a Y τ hY hτ
  rw [hcomm, sub_self] at h
  have h' : (τ.1 0 0 * τ.1 1 0) *
      ((Y.1 0 0 - Y.1 1 1) ^ 2 + 4 * (a : F) * Y.1 1 0 ^ 2) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h').resolve_left hτxy

theorem trace_sq_eq_four (a : Fˣ) (Y : SL F) (hY : Y.1 0 1 = (a : F) * Y.1 1 0)
    (hdisc : (Y.1 0 0 - Y.1 1 1) ^ 2 + 4 * (a : F) * Y.1 1 0 ^ 2 = 0) :
    (Y.1 0 0 + Y.1 1 1) ^ 2 = 4 := by
  have hdet := sl_det Y
  rw [hY] at hdet
  linear_combination hdisc + 4 * hdet

theorem one_add_nilpotent_pow {N : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : F) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      hN, smul_zero, add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel

theorem nilpotent_sub_one_pow {N : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0) (k : ℕ) :
    (N - 1) ^ k = (-1 : F) ^ k • (1 - (k : F) • N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      hN, smul_zero, sub_zero, pow_succ, mul_smul]
    push_cast
    rw [add_smul, one_smul]
    module

theorem not_odd_orderOf_of_trace_neg_two (h2 : (2 : F) ≠ 0) (Y : SL F)
    (htr : Y.1 0 0 + Y.1 1 1 = -2) : ¬ Odd (orderOf Y) := by
  intro hodd
  set N : Matrix (Fin 2) (Fin 2) F := Y.1 + 1 with hNdef
  have hdet := sl_det Y
  have hN : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [hNdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply,
        Matrix.zero_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_ne_zero, zero_ne_one] <;>
      simp only [Fin.isValue, ↓reduceIte, add_zero]
    · linear_combination (Y.1 0 0) * htr - hdet
    · linear_combination (Y.1 0 1) * htr
    · linear_combination (Y.1 1 0) * htr
    · linear_combination (Y.1 1 1) * htr - hdet
  obtain ⟨m, hm⟩ := hodd
  have hpow := nilpotent_sub_one_pow hN (orderOf Y)
  have hY1 : N - 1 = Y.1 := by rw [hNdef]; abel
  rw [hY1, ← sl_pow_val, pow_orderOf_eq_one, hm] at hpow
  have hneg : (-1 : F) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  rw [hneg] at hpow
  change (1 : Matrix (Fin 2) (Fin 2) F) = _ at hpow
  rw [neg_smul, one_smul] at hpow
  have hk : ((2 * m + 1 : ℕ) : F) • N = (2 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [two_smul]
    nth_rewrite 1 [hpow]
    abel
  have h4 : ((2 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) * ((2 : F) • 1) = 0 := by
    rw [← hk, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, smul_zero]
  have h00 := congrFun (congrFun h4 0) 0
  simp only [Matrix.mul_smul, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.zero_apply,
    smul_eq_mul, mul_one] at h00
  exact h2 (by simpa using h00)

@[expose] def vecStab (v : Fin 2 → F) : Subgroup (SL F) where
  carrier := {X | X.1 *ᵥ v = v}
  mul_mem' {X Y} hX hY := by
    change (X.1 * Y.1) *ᵥ v = v
    have hX' : X.1 *ᵥ v = v := hX
    have hY' : Y.1 *ᵥ v = v := hY
    rw [← Matrix.mulVec_mulVec, hY', hX']
  one_mem' := Matrix.one_mulVec v
  inv_mem' {X} hX := by
    have hX : X.1 *ᵥ v = v := hX
    change (X⁻¹).1 *ᵥ v = v
    calc (X⁻¹).1 *ᵥ v = (X⁻¹).1 *ᵥ (X.1 *ᵥ v) := by rw [hX]
      _ = (X⁻¹ * X).1 *ᵥ v := Matrix.mulVec_mulVec _ _ _
      _ = v := by rw [inv_mul_cancel]; exact Matrix.one_mulVec v

theorem mem_vecStab (v : Fin 2 → F) (X : SL F) : X ∈ vecStab v ↔ X.1 *ᵥ v = v := Iff.rfl

theorem conj_mem_vecStab {v w : Fin 2 → F} (g : SL F) {μ : F} (hμ : μ ≠ 0)
    (hg : g.1 *ᵥ v = μ • w) {X : SL F} (hX : X ∈ vecStab v) : g * X * g⁻¹ ∈ vecStab w := by
  rw [mem_vecStab] at hX ⊢
  have hinv : (g⁻¹).1 *ᵥ w = μ⁻¹ • v := by
    have h1 : (g⁻¹).1 *ᵥ (g.1 *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec]
      change (g⁻¹ * g).1 *ᵥ v = v
      rw [inv_mul_cancel]
      exact Matrix.one_mulVec v
    rw [hg, Matrix.mulVec_smul] at h1
    rw [← h1, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  change (g.1 * X.1 * (g⁻¹).1) *ᵥ w = w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hX, hg, smul_smul, inv_mul_cancel₀ hμ, one_smul]

@[expose] def rootGroup (l : F) : Subgroup (SL F) := vecStab ![l, 1]

theorem mulVec_pair (M : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    M *ᵥ ![x, y] = ![M 0 0 * x + M 0 1 * y, M 1 0 * x + M 1 1 * y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mem_rootGroup_iff (l : F) (X : SL F) :
    X ∈ rootGroup l ↔ X.1 0 0 * l + X.1 0 1 = l ∧ X.1 1 0 * l + X.1 1 1 = 1 := by
  rw [rootGroup, mem_vecStab, mulVec_pair]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

theorem rootGroup_entries {l : F} {X : SL F} (hX : X ∈ rootGroup l) :
    X.1 0 0 = 1 + l * X.1 1 0 ∧ X.1 0 1 = -(l ^ 2 * X.1 1 0) ∧
      X.1 1 1 = 1 - l * X.1 1 0 := by
  obtain ⟨h0, h1⟩ := (mem_rootGroup_iff l X).mp hX
  have hdet := sl_det X
  have h00 : X.1 0 0 = 1 + l * X.1 1 0 := by
    have h01 : X.1 0 1 = l - X.1 0 0 * l := by linear_combination h0
    have h11 : X.1 1 1 = 1 - X.1 1 0 * l := by linear_combination h1
    rw [h01, h11] at hdet
    linear_combination hdet
  refine ⟨h00, ?_, by linear_combination h1⟩
  linear_combination h0 - l * h00

theorem rootGroup_ext {l : F} {X Y : SL F} (hX : X ∈ rootGroup l) (hY : Y ∈ rootGroup l)
    (h : X.1 1 0 = Y.1 1 0) : X = Y := by
  obtain ⟨hX0, hX1, hX2⟩ := rootGroup_entries hX
  obtain ⟨hY0, hY1, hY2⟩ := rootGroup_entries hY
  exact sl_ext (by rw [hX0, hY0, h]) (by rw [hX1, hY1, h]) h (by rw [hX2, hY2, h])

@[expose] def rootMat (l c : F) : SL F :=
  ⟨!![1 - c * l, c * l ^ 2; -c, 1 + c * l], by
    rw [Matrix.det_fin_two_of]
    ring⟩

theorem rootMat_val (l c : F) :
    (rootMat l c).1 = !![1 - c * l, c * l ^ 2; -c, 1 + c * l] := rfl

@[expose] def rootHom (l : F) : Multiplicative F →* SL F where
  toFun c := rootMat l c.toAdd
  map_one' := by
    apply Subtype.ext
    rw [rootMat_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' c d := by
    apply Subtype.ext
    change (rootMat l (c * d).toAdd).1 = (rootMat l c.toAdd).1 * (rootMat l d.toAdd).1
    rw [rootMat_val, rootMat_val, rootMat_val, toAdd_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rootHom_val (l : F) (c : Multiplicative F) :
    (rootHom l c).1 = !![1 - c.toAdd * l, c.toAdd * l ^ 2; -c.toAdd, 1 + c.toAdd * l] := rfl

theorem rootHom_mem (l : F) (c : Multiplicative F) : rootHom l c ∈ rootGroup l := by
  rw [mem_rootGroup_iff, rootHom_val]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor <;> ring

theorem rootHom_entry (l : F) (c : Multiplicative F) : (rootHom l c).1 1 0 = -c.toAdd := by
  rw [rootHom_val]
  simp

theorem rootHom_injective (l : F) : Function.Injective (rootHom l) := by
  intro c d h
  have h' := congrArg (fun X : SL F => X.1 1 0) h
  simp only [rootHom_entry, neg_inj] at h'
  exact h'

theorem eq_rootHom {l : F} {X : SL F} (hX : X ∈ rootGroup l) :
    X = rootHom l (Multiplicative.ofAdd (-X.1 1 0)) := by
  apply rootGroup_ext hX (rootHom_mem l _)
  rw [rootHom_entry, toAdd_ofAdd, neg_neg]

theorem rootHom_range (l : F) : (rootHom l).range = rootGroup l := by
  ext X
  constructor
  · rintro ⟨c, rfl⟩
    exact rootHom_mem l c
  · intro hX
    exact ⟨_, (eq_rootHom hX).symm⟩

theorem card_rootGroup [Finite F] (l : F) : Nat.card (rootGroup l) = Nat.card F := by
  rw [← rootHom_range,
    ← Nat.card_congr (MonoidHom.ofInjective (rootHom_injective l)).toEquiv]
  rfl

theorem rootGroup_pow_char {l : F} (p : ℕ) [CharP F p] {X : SL F} (hX : X ∈ rootGroup l) :
    X ^ p = 1 := by
  rw [eq_rootHom hX, ← map_pow]
  have : (Multiplicative.ofAdd (-X.1 1 0)) ^ p = 1 := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero]
  rw [this, map_one]

theorem torus_mulVec (a : Fˣ) {l : F} (hl : l ^ 2 = -(a : F)) {τ : SL F} (hτ : τ ∈ Torus F a) :
    τ.1 *ᵥ ![l, 1] = (τ.1 0 0 + l * τ.1 1 0) • ![l, 1] := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a τ).mp hτ
  rw [mulVec_pair, h01, h11]
  ext i
  fin_cases i <;> simp
  · linear_combination (-τ.1 1 0) * hl
  · ring

theorem torus_eigen_ne_zero (a : Fˣ) {l : F} (hl : l ^ 2 = -(a : F)) {τ : SL F}
    (hτ : τ ∈ Torus F a) : τ.1 0 0 + l * τ.1 1 0 ≠ 0 := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a τ).mp hτ
  have hdet := sl_det τ
  rw [h01, h11] at hdet
  intro h
  have : (τ.1 0 0 + l * τ.1 1 0) * (τ.1 0 0 - l * τ.1 1 0) = 1 := by
    linear_combination hdet - (τ.1 1 0) ^ 2 * hl
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem torus_conj_mem_rootGroup (a : Fˣ) {l : F} (hl : l ^ 2 = -(a : F)) {τ : SL F}
    (hτ : τ ∈ Torus F a) {X : SL F} (hX : X ∈ rootGroup l) : τ * X * τ⁻¹ ∈ rootGroup l :=
  conj_mem_vecStab τ (torus_eigen_ne_zero a hl hτ) (torus_mulVec a hl hτ) hX

theorem beta_mem_rootGroup (a : Fˣ) {l : F} (hl : l ^ 2 = -(a : F)) {X : SL F}
    (hX : X ∈ rootGroup l) : beta F a X ∈ rootGroup l := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hl.symm)
  have hJv : (J F a : Matrix (Fin 2) (Fin 2) F) *ᵥ ![l, 1] = l • ![l, 1] := by
    rw [J_val, mulVec_pair]
    ext i
    fin_cases i <;> simp
    linear_combination -hl
  have hb := (beta_eq_iff a X (beta F a X)).mp rfl
  rw [rootGroup, mem_vecStab] at hX ⊢
  have h1 : (beta F a X).1 *ᵥ ((J F a : Matrix (Fin 2) (Fin 2) F) *ᵥ ![l, 1]) =
      (J F a : Matrix (Fin 2) (Fin 2) F) *ᵥ ![l, 1] := by
    rw [Matrix.mulVec_mulVec, ← hb, ← Matrix.mulVec_mulVec, hX]
  rw [hJv, Matrix.mulVec_smul] at h1
  exact smul_right_injective _ hl0 h1

theorem map_mem_rootGroup (σ : F ≃+* F) {l : F} (hσ : σ l = l) {X : SL F}
    (hX : X ∈ rootGroup l) :
    Matrix.SpecialLinearGroup.map (σ : F ≃+* F).toRingHom X ∈ rootGroup l := by
  rw [mem_rootGroup_iff] at hX ⊢
  obtain ⟨h0, h1⟩ := hX
  change σ (X.1 0 0) * l + σ (X.1 0 1) = l ∧ σ (X.1 1 0) * l + σ (X.1 1 1) = 1
  constructor
  · rw [← hσ, ← map_mul, ← map_add, h0]
  · rw [← hσ, ← map_mul, ← map_add, h1, map_one]

theorem anticomm_conj_mem_rootGroup (a : Fˣ) {l : F} (hl : l ^ 2 = -(a : F)) {Z : SL F}
    (hZ : Z.1 0 1 = (a : F) * Z.1 1 0 ∧ Z.1 1 1 = -Z.1 0 0) {X : SL F}
    (hX : X ∈ rootGroup l) : Z * X * Z⁻¹ ∈ rootGroup (-l) := by
  obtain ⟨h01, h11⟩ := hZ
  have hdet := sl_det Z
  rw [h01, h11] at hdet
  have hμ : Z.1 1 0 * l - Z.1 0 0 ≠ 0 := by
    intro h
    have : (Z.1 1 0 * l - Z.1 0 0) * (Z.1 1 0 * l + Z.1 0 0) = 1 := by
      linear_combination hdet + (Z.1 1 0) ^ 2 * hl
    rw [h, zero_mul] at this
    exact zero_ne_one this
  refine conj_mem_vecStab Z hμ ?_ hX
  rw [mulVec_pair, h01, h11]
  ext i
  fin_cases i <;> simp
  · linear_combination (Z.1 1 0) * hl
  · ring

theorem rootGroup_inf_torus (a : Fˣ) (h2 : (2 : F) ≠ 0) {l : F} (hl : l ^ 2 = -(a : F)) :
    rootGroup l ⊓ Torus F a = ⊥ := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hl.symm)
  rw [eq_bot_iff]
  rintro X ⟨hX, hXT⟩
  rw [Subgroup.mem_bot]
  obtain ⟨h0, h1, h2'⟩ := rootGroup_entries hX
  obtain ⟨-, h11⟩ := (mem_torus_iff F a X).mp hXT
  have h10 : X.1 1 0 = 0 := by
    have : (2 * l) * X.1 1 0 = 0 := by linear_combination -h0 + h2' - h11
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hl0)
  apply rootGroup_ext hX (one_mem _)
  rw [h10]
  rfl

theorem rootGroup_ne_neg (h2 : (2 : F) ≠ 0) {l : F} (hl0 : l ≠ 0) :
    rootGroup l ≠ rootGroup (-l) := by
  intro h
  have hmem := rootHom_mem l (Multiplicative.ofAdd 1)
  rw [h, mem_rootGroup_iff, rootHom_val] at hmem
  obtain ⟨h0, -⟩ := hmem
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, toAdd_ofAdd] at h0
  have : 2 * l ^ 2 = 0 := by linear_combination h0
  exact (mul_ne_zero h2 (pow_ne_zero 2 hl0)) this

theorem slConjugation_mem_vecStab (g : GL2 F) {v : Fin 2 → F} {X : SL F}
    (hX : X ∈ vecStab v) :
    slConjugation F g X ∈ vecStab ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
  rw [mem_vecStab] at hX ⊢
  have hval : (slConjugation F g X).1 = (g : Matrix (Fin 2) (Fin 2) F) * X.1 *
      (((g⁻¹ : GL2 F)) : Matrix (Fin 2) (Fin 2) F) := slConjugation_matrix F g X
  have hinv : (((g⁻¹ : GL2 F)) : Matrix (Fin 2) (Fin 2) F) * g = 1 :=
    congrArg Units.val (inv_mul_cancel g)
  have hprod : (g : Matrix (Fin 2) (Fin 2) F) * X.1 *
      (((g⁻¹ : GL2 F)) : Matrix (Fin 2) (Fin 2) F) * g = (g : Matrix (Fin 2) (Fin 2) F) * X.1 := by
    rw [Matrix.mul_assoc _ (((g⁻¹ : GL2 F)) : Matrix (Fin 2) (Fin 2) F), hinv, Matrix.mul_one]
  rw [hval, Matrix.mulVec_mulVec, hprod, ← Matrix.mulVec_mulVec, hX]

@[expose] def upperT (c : F) : SL F :=
  ⟨!![1, c; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[expose] def lowerT (c : F) : SL F :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem upperT_mem (c : F) : upperT c ∈ vecStab ![1, 0] := by
  rw [mem_vecStab]
  change !![1, c; 0, 1] *ᵥ ![1, 0] = ![1, 0]
  rw [mulVec_pair]
  ext i
  fin_cases i <;> simp

theorem lowerT_mem (c : F) : lowerT c ∈ vecStab ![0, 1] := by
  rw [mem_vecStab]
  change !![1, 0; c, 1] *ᵥ ![0, 1] = ![0, 1]
  rw [mulVec_pair]
  ext i
  fin_cases i <;> simp

theorem vecStab_sup_eq_top : vecStab (![1, 0] : Fin 2 → F) ⊔ vecStab ![0, 1] = ⊤ := by
  rw [eq_top_iff]
  have key : ∀ M : SL F, M.1 1 0 ≠ 0 → M ∈ vecStab (![1, 0] : Fin 2 → F) ⊔ vecStab ![0, 1] := by
    intro M hM
    have hdet := sl_det M
    have heq : M = upperT ((M.1 0 0 - 1) / M.1 1 0) * lowerT (M.1 1 0) *
        upperT ((M.1 1 1 - 1) / M.1 1 0) := by
      apply sl_ext <;> simp only [sl_mul_val] <;> simp [upperT, lowerT] <;> field_simp
      · ring
      · linear_combination -hdet
      · ring
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (upperT_mem _))
      (Subgroup.mem_sup_right (lowerT_mem _))) (Subgroup.mem_sup_left (upperT_mem _))
  intro M _
  by_cases hM : M.1 1 0 = 0
  · have hdet := sl_det M
    rw [hM, mul_zero, sub_zero] at hdet
    have h00 : M.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hLM : (lowerT 1 * M).1 1 0 ≠ 0 := by
      rw [sl_mul_val]
      simp [lowerT, hM, h00]
    have h := key _ hLM
    have : M = (lowerT 1)⁻¹ * (lowerT 1 * M) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (lowerT_mem _))) h
  · exact key M hM

theorem rootGroup_sup_neg (h2 : (2 : F) ≠ 0) {l : F} (hl0 : l ≠ 0) :
    rootGroup l ⊔ rootGroup (-l) = ⊤ := by
  let P : GL2 F := GeneralLinearGroup.mkOfDetNeZero !![l, -l; 1, 1] (by
    rw [Matrix.det_fin_two_of]
    intro h
    exact mul_ne_zero h2 hl0 (by linear_combination h))
  have hP : (P : Matrix (Fin 2) (Fin 2) F) = !![l, -l; 1, 1] := rfl
  have h0 : (P : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = ![l, 1] := by
    rw [hP, mulVec_pair]; ext i; fin_cases i <;> simp
  have h1 : (P : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, 1] = ![-l, 1] := by
    rw [hP, mulVec_pair]; ext i; fin_cases i <;> simp
  rw [eq_top_iff]
  intro M _
  have hM : (slConjugation F P).symm M ∈ vecStab (![1, 0] : Fin 2 → F) ⊔ vecStab ![0, 1] := by
    rw [vecStab_sup_eq_top]
    exact Subgroup.mem_top _
  have hmap : (vecStab (![1, 0] : Fin 2 → F) ⊔ vecStab ![0, 1]).map
      (slConjugation F P).toMonoidHom ≤ rootGroup l ⊔ rootGroup (-l) := by
    rw [Subgroup.map_sup]
    apply sup_le_sup
    · rintro _ ⟨X, hX, rfl⟩
      have := slConjugation_mem_vecStab P hX
      rwa [h0] at this
    · rintro _ ⟨X, hX, rfl⟩
      have := slConjugation_mem_vecStab P hX
      rwa [h1] at this
  have := hmap ⟨_, hM, rfl⟩
  simpa using this

@[expose] def torusElt (l μ : F) (hl0 : l ≠ 0) (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) : SL F :=
  ⟨!![(μ + μ⁻¹) / 2, l ^ 2 * ((μ - μ⁻¹) / (2 * l));
      (μ - μ⁻¹) / (2 * l), (μ + μ⁻¹) / 2], by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

theorem torusElt_mem (a : Fˣ) {l : F} (μ : F) (hl : l ^ 2 = -(a : F)) (hl0 : l ≠ 0)
    (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) : torusElt l μ hl0 h2 hμ ∈ Torus F a := by
  rw [mem_torus_iff]
  simp only [torusElt, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, and_true]
  rw [hl]

theorem torusElt_eigen (l μ : F) (hl0 : l ≠ 0) (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) :
    (torusElt l μ hl0 h2 hμ).1 0 0 + l * (torusElt l μ hl0 h2 hμ).1 1 0 = μ := by
  simp [torusElt]
  field_simp
  ring

theorem torus_conj_entry (a : Fˣ) {l : F} {τ : SL F} (hτ : τ ∈ Torus F a) {X : SL F}
    (hX : X ∈ rootGroup l) :
    (τ * X * τ⁻¹).1 1 0 = (τ.1 0 0 + l * τ.1 1 0) ^ 2 * X.1 1 0 := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a τ).mp hτ
  obtain ⟨hX0, hX1, hX2⟩ := rootGroup_entries hX
  simp only [sl_mul_val, sl_inv_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, h01, h11, hX0, hX1, hX2]
  ring

theorem torus_conj_rootHom (a : Fˣ) {l : F} (hl : l ^ 2 = -(a : F)) {τ : SL F}
    (hτ : τ ∈ Torus F a) (c : Multiplicative F) :
    τ * rootHom l c * τ⁻¹ =
      rootHom l (Multiplicative.ofAdd ((τ.1 0 0 + l * τ.1 1 0) ^ 2 * c.toAdd)) := by
  apply rootGroup_ext (torus_conj_mem_rootGroup a hl hτ (rootHom_mem l c)) (rootHom_mem l _)
  rw [torus_conj_entry a hτ (rootHom_mem l c), rootHom_entry, rootHom_entry, toAdd_ofAdd]
  ring

theorem rootGroup_irreducible [Finite F] (hodd : Odd (Nat.card F)) (a : Fˣ) {l : F}
    (hl : l ^ 2 = -(a : F)) (X : Subgroup (SL F)) (hX : X ≤ rootGroup l)
    (hnorm : ∀ τ ∈ Torus F a, ∀ x ∈ X, τ * x * τ⁻¹ ∈ X) : X = ⊥ ∨ X = rootGroup l := by
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hl.symm)
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x₀, hx₀⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hx₀1 : x₀ ≠ 1 := fun h => hne (Subtype.ext h)
  set c₀ : F := -x₀.1 1 0 with hc₀
  have hx₀eq : x₀ = rootHom l (Multiplicative.ofAdd c₀) := eq_rootHom (hX hx₀)
  have hc₀0 : c₀ ≠ 0 := by
    intro h
    apply hx₀1
    rw [hx₀eq, h, ofAdd_zero, map_one]
  have hsq : ∀ s : F, rootHom l (Multiplicative.ofAdd (s ^ 2 * c₀)) ∈ X := by
    intro s
    by_cases hs : s = 0
    · rw [hs]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, ofAdd_zero,
        map_one]
      exact X.one_mem
    · have hmem := hnorm _ (torusElt_mem a s hl hl0 h2 hs) _ hx₀
      rw [hx₀eq, torus_conj_rootHom a hl (torusElt_mem a s hl hl0 h2 hs), torusElt_eigen,
        toAdd_ofAdd] at hmem
      exact hmem
  apply le_antisymm hX
  intro Y hY
  obtain ⟨s₁, s₂, hs⟩ := OddFieldSL2.sum_two_squares F hodd (-Y.1 1 0 / c₀)
  rw [eq_rootHom hY]
  have : Multiplicative.ofAdd (-Y.1 1 0) = Multiplicative.ofAdd (s₁ ^ 2 * c₀) *
      Multiplicative.ofAdd (s₂ ^ 2 * c₀) := by
    rw [← ofAdd_add, ← add_mul, hs, div_mul_cancel₀ _ hc₀0]
  rw [this, map_mul]
  exact X.mul_mem (hsq s₁) (hsq s₂)

theorem torus_pow_four (a : Fˣ) {τ : SL F} (hτ : τ ∈ Torus F a)
    (hxy : τ.1 0 0 * τ.1 1 0 = 0) : τ ^ 4 = 1 := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a τ).mp hτ
  have hdet := sl_det τ
  rw [h01, h11] at hdet
  have h4 : τ ^ 4 = τ * τ * τ * τ := by simp only [pow_succ, pow_zero, one_mul]
  rw [h4]
  apply sl_ext <;> simp only [sl_mul_val, h01, h11, sl_one_val] <;> simp
  · linear_combination (τ.1 0 0 ^ 2 + (a : F) * τ.1 1 0 ^ 2 + 1) * hdet -
      8 * (a : F) * (τ.1 0 0 * τ.1 1 0) * hxy
  · linear_combination (-4 * (a : F) * (τ.1 0 0 ^ 2 - (a : F) * τ.1 1 0 ^ 2)) * hxy
  · linear_combination (4 * (τ.1 0 0 ^ 2 - (a : F) * τ.1 1 0 ^ 2)) * hxy
  · linear_combination (τ.1 0 0 ^ 2 + (a : F) * τ.1 1 0 ^ 2 + 1) * hdet -
      8 * (a : F) * (τ.1 0 0 * τ.1 1 0) * hxy

theorem mem_torus_of_commute (a : Fˣ) {w : SL F} (hw : w ∈ Torus F a) (hw0 : w.1 1 0 ≠ 0)
    {Y : SL F} (hYw : Y * w = w * Y) : Y ∈ Torus F a := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a w).mp hw
  have e00 := congrArg (fun X : SL F => X.1 0 0) hYw
  have e01 := congrArg (fun X : SL F => X.1 0 1) hYw
  simp only [sl_mul_val, h01, h11] at e00 e01
  rw [mem_torus_iff]
  constructor
  · have : w.1 1 0 * (Y.1 0 1 + (a : F) * Y.1 1 0) = 0 := by linear_combination e00
    have h := (mul_eq_zero.mp this).resolve_left hw0
    linear_combination h
  · have : ((a : F) * w.1 1 0) * (Y.1 1 1 - Y.1 0 0) = 0 := by linear_combination e01
    have h := (mul_eq_zero.mp this).resolve_left (mul_ne_zero a.ne_zero hw0)
    linear_combination h

theorem torus_or_anticomm_of_conj (a : Fˣ) (h2 : (2 : F) ≠ 0) {w w' g : SL F}
    (hw : w ∈ Torus F a) (hw' : w' ∈ Torus F a) (hw0 : w.1 1 0 ≠ 0) (hg : g * w' = w * g) :
    g ∈ Torus F a ∨ (g.1 0 1 = (a : F) * g.1 1 0 ∧ g.1 1 1 = -g.1 0 0) := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a w).mp hw
  obtain ⟨h01', h11'⟩ := (mem_torus_iff F a w').mp hw'
  have hdw := sl_det w
  have hdw' := sl_det w'
  have hdg := sl_det g
  rw [h01, h11] at hdw
  rw [h01', h11'] at hdw'
  have E1 := congrArg (fun X : SL F => X.1 0 0) hg
  have E2 := congrArg (fun X : SL F => X.1 0 1) hg
  have E3 := congrArg (fun X : SL F => X.1 1 0) hg
  have E4 := congrArg (fun X : SL F => X.1 1 1) hg
  simp only [sl_mul_val, h01, h11, h01', h11'] at E1 E2 E3 E4
  have hx : w'.1 0 0 = w.1 0 0 := by
    have : 2 * (w'.1 0 0 - w.1 0 0) = 0 := by
      linear_combination (g.1 1 1) * E1 - (g.1 0 1) * E3 + (g.1 0 0) * E4 - (g.1 1 0) * E2 -
        2 * (w'.1 0 0 - w.1 0 0) * hdg
    have := (mul_eq_zero.mp this).resolve_left h2
    linear_combination this
  rw [hx] at E1 E2 E3 E4 hdw'
  have hy : (w'.1 1 0 - w.1 1 0) * (w'.1 1 0 + w.1 1 0) = 0 := by
    have : (a : F) * ((w'.1 1 0 - w.1 1 0) * (w'.1 1 0 + w.1 1 0)) = 0 := by
      linear_combination hdw' - hdw
    exact (mul_eq_zero.mp this).resolve_left a.ne_zero
  rcases mul_eq_zero.mp hy with hy | hy
  · left
    have hy' : w'.1 1 0 = w.1 1 0 := by linear_combination hy
    rw [hy'] at E1 E3
    rw [mem_torus_iff]
    constructor
    · have : w.1 1 0 * (g.1 0 1 + (a : F) * g.1 1 0) = 0 := by linear_combination E1
      have h := (mul_eq_zero.mp this).resolve_left hw0
      linear_combination h
    · have : w.1 1 0 * (g.1 1 1 - g.1 0 0) = 0 := by linear_combination E3
      have h := (mul_eq_zero.mp this).resolve_left hw0
      linear_combination h
  · right
    have hy' : w'.1 1 0 = -w.1 1 0 := by linear_combination hy
    rw [hy'] at E1 E3
    constructor
    · have : w.1 1 0 * (g.1 0 1 - (a : F) * g.1 1 0) = 0 := by linear_combination -E1
      have h := (mul_eq_zero.mp this).resolve_left hw0
      linear_combination h
    · have : w.1 1 0 * (g.1 1 1 + g.1 0 0) = 0 := by linear_combination -E3
      have h := (mul_eq_zero.mp this).resolve_left hw0
      linear_combination h

theorem sq_eq_neg_one_of_anticomm (a : Fˣ) {g : SL F}
    (hg : g.1 0 1 = (a : F) * g.1 1 0 ∧ g.1 1 1 = -g.1 0 0) :
    g ^ 2 = OddFieldSL2.minusIdentity F := by
  obtain ⟨h01, h11⟩ := hg
  have hdet := sl_det g
  rw [h01, h11] at hdet
  have hm : (OddFieldSL2.minusIdentity F).1 = !![-1, 0; 0, -1] := by
    rw [show (OddFieldSL2.minusIdentity F).1 = Matrix.scalar (Fin 2) (-1) from
      OddFieldSL2.minusIdentity_matrix F]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [pow_two]
  apply sl_ext <;> simp only [sl_mul_val, h01, h11, hm] <;> simp
  · linear_combination -hdet
  · ring
  · ring
  · linear_combination -hdet

theorem inverted_odd_mem_rootGroup (a : Fˣ) (h2 : (2 : F) ≠ 0) {Y : SL F}
    (hinv : beta F a Y = Y⁻¹) (hY1 : Y ≠ 1) (hodd : Odd (orderOf Y)) {τ : SL F}
    (hτ : τ ∈ Torus F a) (hτxy : τ.1 0 0 * τ.1 1 0 ≠ 0)
    (hcomm : Y * (τ * Y * τ⁻¹) = (τ * Y * τ⁻¹) * Y) :
    ∃ l : F, l ^ 2 = -(a : F) ∧ Y ∈ rootGroup l := by
  have hY01 := (beta_eq_inv_iff a Y).mp hinv
  have hdisc := disc_eq_zero a Y τ hY01 hτ hτxy hcomm
  have htr4 := trace_sq_eq_four a Y hY01 hdisc
  have htr : Y.1 0 0 + Y.1 1 1 = 2 := by
    have : (Y.1 0 0 + Y.1 1 1 - 2) * (Y.1 0 0 + Y.1 1 1 + 2) = 0 := by
      linear_combination htr4
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd hodd (not_odd_orderOf_of_trace_neg_two h2 Y (by linear_combination h))
  have hY10 : Y.1 1 0 ≠ 0 := by
    intro h10
    apply hY1
    rw [h10] at hdisc hY01
    have hdiff : Y.1 0 0 - Y.1 1 1 = 0 := by
      have : (Y.1 0 0 - Y.1 1 1) ^ 2 = 0 := by linear_combination hdisc
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have h00 : Y.1 0 0 = 1 := by
      have : 2 * (Y.1 0 0 - 1) = 0 := by linear_combination htr + hdiff
      have := (mul_eq_zero.mp this).resolve_left h2
      linear_combination this
    apply sl_ext
    · rw [h00]; rfl
    · rw [hY01, mul_zero]; rfl
    · rw [h10]; rfl
    · rw [show Y.1 1 1 = 1 by linear_combination htr - h00]; rfl
  set l : F := (Y.1 0 0 - Y.1 1 1) / (2 * Y.1 1 0) with hl
  have h2Y : 2 * Y.1 1 0 ≠ 0 := mul_ne_zero h2 hY10
  have hlY : l * (2 * Y.1 1 0) = Y.1 0 0 - Y.1 1 1 := div_mul_cancel₀ _ h2Y
  refine ⟨l, ?_, ?_⟩
  · have : (l ^ 2 + (a : F)) * (2 * Y.1 1 0) ^ 2 = 0 := by
      linear_combination (l * (2 * Y.1 1 0) + (Y.1 0 0 - Y.1 1 1)) * hlY + hdisc
    have := (mul_eq_zero.mp this).resolve_right (pow_ne_zero 2 h2Y)
    linear_combination this
  · rw [mem_rootGroup_iff, hY01]
    constructor
    · have : (Y.1 0 0 * l + (a : F) * Y.1 1 0 - l) * (2 * (2 * Y.1 1 0)) = 0 := by
        linear_combination (2 * Y.1 0 0 - 2) * hlY + (Y.1 0 0 - Y.1 1 1) * htr + hdisc
      have := (mul_eq_zero.mp this).resolve_right (mul_ne_zero h2 h2Y)
      linear_combination this
    · have : (Y.1 1 0 * l + Y.1 1 1 - 1) * 2 = 0 := by linear_combination hlY + htr
      have := (mul_eq_zero.mp this).resolve_right h2
      linear_combination this

theorem ringEquiv_eq_refl_of_fix_torus [Finite F] (a : Fˣ) (h2 : (2 : F) ≠ 0)
    (hF : 5 ≤ Nat.card F) (σ : F ≃+* F)
    (hfix : ∀ τ ∈ Torus F a, ∀ i j : Fin 2, σ (τ.1 i j) = τ.1 i j) : σ = RingEquiv.refl F := by
  classical
  have hgood : ∀ t : F, 1 + (a : F) * t ^ 2 ≠ 0 → σ t = t := by
    intro t ht
    let x : F := (1 - (a : F) * t ^ 2) / (1 + (a : F) * t ^ 2)
    let y : F := 2 * t / (1 + (a : F) * t ^ 2)
    let τ : SL F := ⟨!![x, -(a : F) * y; y, x], by
      rw [Matrix.det_fin_two_of]
      simp only [x, y]
      field_simp
      ring⟩
    have hτ : τ ∈ Torus F a := by
      rw [mem_torus_iff]
      simp [τ]
    have hx : σ x = x := hfix τ hτ 0 0
    have hy : σ y = y := hfix τ hτ 1 0
    have h1x' : 1 + x = 2 / (1 + (a : F) * t ^ 2) := by
      simp only [x]
      field_simp
      ring
    have ht'' : 1 + t ^ 2 * (a : F) ≠ 0 := by rw [mul_comm]; exact ht
    have ht' : t = y / (1 + x) := by
      rw [h1x']
      simp only [y]
      field_simp
    rw [ht', map_div₀, map_add, map_one, hx, hy]
  apply RingEquiv.ext
  intro t
  change σ t = t
  by_cases ht : 1 + (a : F) * t ^ 2 = 0
  · let : Fintype F := Fintype.ofFinite F
    have hcard : ({t, -t, 0, 2 * t} : Finset F).card < (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt Finset.card_le_four (by omega)
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨hct, hcnt, hc0, hc2t⟩ := hc
    have hgc : 1 + (a : F) * c ^ 2 ≠ 0 := by
      intro h
      have : (a : F) * ((c - t) * (c + t)) = 0 := by linear_combination h - ht
      rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left a.ne_zero) with h' | h'
      · exact hct (by linear_combination h')
      · exact hcnt (by linear_combination h')
    have hgtc : 1 + (a : F) * (t - c) ^ 2 ≠ 0 := by
      intro h
      have : (a : F) * (c * (c - 2 * t)) = 0 := by linear_combination h - ht
      rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left a.ne_zero) with h' | h'
      · exact hc0 h'
      · exact hc2t (by linear_combination h')
    have := congrArg₂ (· + ·) (hgood c hgc) (hgood (t - c) hgtc)
    simp only [← map_add, add_sub_cancel] at this
    exact this
  · exact hgood t ht

theorem le_or_le_of_forall_mem_or_mem {G : Type*} [Group G] {K A B : Subgroup G}
    (h : ∀ k ∈ K, k ∈ A ∨ k ∈ B) : K ≤ A ∨ K ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hKA, hKB⟩ := hcon
  obtain ⟨x, hxK, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hKA
  obtain ⟨y, hyK, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp hKB
  have hxB := (h x hxK).resolve_left hxA
  have hyA := (h y hyK).resolve_right hyB
  rcases h (x * y) (K.mul_mem hxK hyK) with hxy | hxy
  · exact hxA (by simpa using A.mul_mem hxy (A.inv_mem hyA))
  · exact hyB (by simpa using B.mul_mem (B.inv_mem hxB) hxy)

end

end CFSG.Semidihedral.AllPrime.QDTI
