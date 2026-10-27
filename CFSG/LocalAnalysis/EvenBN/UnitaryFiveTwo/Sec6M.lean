module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSL44Three
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix Subgroup CFSG.Fischer
open scoped MatrixGroups

theorem F4_sq_ne_one : ∀ a : F4, a ≠ 1 → a ^ 2 ≠ 1 := by decide

theorem F4_pow_two_pow_ne_one {a : F4} (ha : a ≠ 1) (k : ℕ) : a ^ 2 ^ k ≠ 1 := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact F4_sq_ne_one _ ih

theorem mat_sq_step : ∀ a b c d : F4,
    !![a, b; c, d] * !![a, b; c, d] ≠ (1 : Matrix (Fin 2) (Fin 2) F4) →
      (!![a, b; c, d] * !![a, b; c, d]) * (!![a, b; c, d] * !![a, b; c, d]) ≠
        (1 : Matrix (Fin 2) (Fin 2) F4) := by
  decide

@[expose] def Shape (x : SL(4, F4)) : Prop :=
  x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 0 3 = 0 ∧ x 1 3 = 0 ∧ x 2 3 = 0 ∧ x 3 3 = x 0 0

theorem shape_of_comm {x : SL(4, F4)} (h : x * pSL 0 0 0 0 0 1 = pSL 0 0 0 0 0 1 * x) :
    Shape x := by
  have h' : (x : Matrix (Fin 4) (Fin 4) F4) * pMat 0 0 0 0 0 1 =
      pMat 0 0 0 0 0 1 * (x : Matrix (Fin 4) (Fin 4) F4) := by
    have := congrArg (fun y : SL(4, F4) => (y : Matrix (Fin 4) (Fin 4) F4)) h
    simpa using this
  have e : ∀ i j, ((x : Matrix (Fin 4) (Fin 4) F4) * pMat 0 0 0 0 0 1) i j =
      (pMat 0 0 0 0 0 1 * (x : Matrix (Fin 4) (Fin 4) F4)) i j := fun i j => by rw [h']
  have e1 := e 3 1
  have e2 := e 3 2
  have e3 := e 3 3
  have e4 := e 1 0
  have e5 := e 2 0
  have e6 := e 3 0
  simp [pMat, Matrix.mul_apply, Fin.sum_univ_four] at e1 e2 e3 e4 e5 e6
  exact ⟨e1, e2, e3, e4, e5, by linear_combination e6⟩

@[expose] def mid (x : SL(4, F4)) : Matrix (Fin 2) (Fin 2) F4 := !![x 1 1, x 1 2; x 2 1, x 2 2]

theorem lam_mul {x y : SL(4, F4)} (hx : Shape x) (_hy : Shape y) :
    (x * y) 0 0 = x 0 0 * y 0 0 := by
  obtain ⟨hx1, hx2, hx3, -, -, -⟩ := hx
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_four, hx1, hx2, hx3]

theorem mid_mul {x y : SL(4, F4)} (hx : Shape x) (hy : Shape y) :
    mid (x * y) = mid x * mid y := by
  obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6⟩ := hy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mid, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_two, hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5]

theorem lam_mid_pow {T : Subgroup SL(4, F4)} (hT : ∀ y ∈ T, Shape y) {x : SL(4, F4)} (hx : x ∈ T)
    (n : ℕ) : (x ^ n) 0 0 = (x 0 0) ^ n ∧ mid (x ^ n) = (mid x) ^ n := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mid]
  | succ n ih =>
    have hs := hT _ (T.pow_mem hx n)
    have hs' := hT _ hx
    rw [pow_succ, pow_succ, pow_succ]
    exact ⟨by rw [lam_mul hs hs', ih.1], by rw [mid_mul hs hs', ih.2]⟩

theorem lam_eq_one {T : Subgroup SL(4, F4)} (hT : ∀ y ∈ T, Shape y) {x : SL(4, F4)} (hx : x ∈ T)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x 0 0 = 1 := by
  by_contra hne
  have h1 := F4_pow_two_pow_ne_one hne k
  rw [← (lam_mid_pow hT hx _).1, hk] at h1
  exact h1 (by simp)

theorem mat_pow_sq_ne_one (g : Matrix (Fin 2) (Fin 2) F4) (hg : g * g ≠ 1) (j : ℕ) :
    g ^ 2 ^ j * g ^ 2 ^ j ≠ 1 := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
    have e : g ^ 2 ^ (j + 1) = g ^ 2 ^ j * g ^ 2 ^ j := by
      rw [pow_succ, pow_mul, sq]
    rw [e]
    have := mat_sq_step ((g ^ 2 ^ j) 0 0) ((g ^ 2 ^ j) 0 1) ((g ^ 2 ^ j) 1 0) ((g ^ 2 ^ j) 1 1)
    rw [← Matrix.eta_fin_two (g ^ 2 ^ j)] at this
    exact this ih

theorem mid_sq_eq_one {T : Subgroup SL(4, F4)} (hT : ∀ y ∈ T, Shape y) {x : SL(4, F4)} (hx : x ∈ T)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : mid x * mid x = 1 := by
  by_contra hne
  have h1 := mat_pow_sq_ne_one (mid x) hne k
  rw [← (lam_mid_pow hT hx _).2] at h1
  apply h1
  rw [hk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mid]

theorem odd15_step : ∀ a b c d : F4,
    (!![a, b; c, d] ≠ (1 : Matrix (Fin 2) (Fin 2) F4) ∧ !![a, b; c, d] ^ 15 = 1) →
      (!![a, b; c, d] * !![a, b; c, d] ≠ (1 : Matrix (Fin 2) (Fin 2) F4) ∧
        (!![a, b; c, d] * !![a, b; c, d]) ^ 15 = 1) := by
  decide +kernel

theorem odd15_pow_ne_one (g : Matrix (Fin 2) (Fin 2) F4) (hg : g ≠ 1 ∧ g ^ 15 = 1) (j : ℕ) :
    g ^ 2 ^ j ≠ 1 ∧ (g ^ 2 ^ j) ^ 15 = 1 := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
    have e : g ^ 2 ^ (j + 1) = g ^ 2 ^ j * g ^ 2 ^ j := by
      rw [pow_succ, pow_mul, sq]
    rw [e]
    have := odd15_step ((g ^ 2 ^ j) 0 0) ((g ^ 2 ^ j) 0 1) ((g ^ 2 ^ j) 1 0) ((g ^ 2 ^ j) 1 1)
    rw [← Matrix.eta_fin_two (g ^ 2 ^ j)] at this
    exact this ih

theorem key_decide : ∀ c b₀₀ b₀₁ b₁₀ b₁₁ : F4, c ≠ 0 →
    ¬ (b₀₀ = 1 ∧ b₁₁ = 1 ∧ b₀₁ = 0) → !![b₀₀, b₀₁; b₁₀, b₁₁] * !![b₀₀, b₀₁; b₁₀, b₁₁] = 1 →
      (!![1, 0; c, 1] * !![b₀₀, b₀₁; b₁₀, b₁₁] ≠ (1 : Matrix (Fin 2) (Fin 2) F4) ∧
        (!![1, 0; c, 1] * !![b₀₀, b₀₁; b₁₀, b₁₁]) ^ 15 = 1) := by
  decide +kernel

theorem mem_PK_of_entries {y : SL(4, F4)} (h00 : y 0 0 = 1) (h01 : y 0 1 = 0) (h02 : y 0 2 = 0)
    (h03 : y 0 3 = 0) (h11 : y 1 1 = 1) (h12 : y 1 2 = 0) (h13 : y 1 3 = 0) (h22 : y 2 2 = 1)
    (h23 : y 2 3 = 0) (h33 : y 3 3 = 1) : y ∈ PK := by
  refine ⟨y 1 0, y 2 1, y 3 2, y 2 0, y 3 1, y 3 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pSL, pMat, h00, h01, h02, h03, h11, h12, h13, h22, h23, h33]

theorem pSL_one_mem_ZK : pSL 0 0 0 0 0 1 ∈ ZK := ⟨0, 0, 0, 0, 1, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem le_PK_of_pGroup {T : Subgroup SL(4, F4)} (hT : IsPGroup 2 T)
    (hC : ∀ x ∈ T, ∀ z ∈ ZK, x * z = z * x)
    (hnc : ∃ x ∈ T ⊓ PK, ∃ y ∈ T ⊓ PK, x * y * x⁻¹ * y⁻¹ ∉ ZK) : T ≤ PK := by
  have hsh : ∀ y ∈ T, Shape y := fun y hy => shape_of_comm (hC y hy _ pSL_one_mem_ZK)
  have hpow : ∀ x ∈ T, ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hT ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  by_contra hTP
  obtain ⟨τ, hτT, hτP⟩ := SetLike.not_le_iff_exists.1 hTP
  obtain ⟨kτ, hkτ⟩ := hpow τ hτT
  have hlam : τ 0 0 = 1 := lam_eq_one hsh hτT hkτ
  have hbb : mid τ * mid τ = 1 := mid_sq_eq_one hsh hτT hkτ
  have hτ' : ¬ (mid τ 0 0 = 1 ∧ mid τ 1 1 = 1 ∧ mid τ 0 1 = 0) := by
    rintro ⟨h1, h2, h3⟩
    apply hτP
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsh τ hτT
    simp only [mid, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h1 h2 h3
    exact mem_PK_of_entries hlam s1 s2 s3 h1 h3 s4 h2 s5 (s6.trans hlam)
  have hMK : ∀ x ∈ T ⊓ PK, x ∈ MK := by
    rintro x ⟨hxT, hxP⟩
    by_contra hxM
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩ := hxP
    have ha₂ : a₂ ≠ 0 := fun h0 => hxM (mem_MK.2 ⟨a₁, a₄, a₅, a₃, a₈, by rw [h0]⟩)
    have hxτT := T.mul_mem hxT hτT
    obtain ⟨k, hk⟩ := hpow _ hxτT
    have hmid : mid (pSL a₁ a₂ a₃ a₄ a₅ a₈ * τ) = !![1, 0; a₂, 1] * mid τ := by
      rw [mid_mul (hsh _ hxT) (hsh _ hτT)]
      congr 1
    have hg := (lam_mid_pow hsh hxτT (2 ^ k)).2
    rw [hk, hmid] at hg
    have hone : mid (1 : SL(4, F4)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mid]
    rw [hone] at hg
    have hkd := key_decide a₂ (mid τ 0 0) (mid τ 0 1) (mid τ 1 0) (mid τ 1 1) ha₂ hτ'
      (by rw [← Matrix.eta_fin_two (mid τ)]; exact hbb)
    rw [← Matrix.eta_fin_two (mid τ)] at hkd
    exact (odd15_pow_ne_one _ hkd k).1 hg.symm
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  apply hxy
  have hcm := Subgroup.commutator_mem_commutator (hMK x hx) (hMK y hy)
  rw [commutator_MK] at hcm
  simpa [commutatorElement_def] using hcm

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
