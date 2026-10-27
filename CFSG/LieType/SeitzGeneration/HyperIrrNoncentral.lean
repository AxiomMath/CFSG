module

public import CFSG.LieType.SeitzGeneration.HyperIrrModel

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F]

theorem shiftIdx_injective {p : ℕ} (hp : 0 < p) : Function.Injective (shiftIdx hp) := by
  intro k k' h
  have h' : ((k : ℕ) + 1) % p = ((k' : ℕ) + 1) % p := congrArg Fin.val h
  apply Fin.ext
  have hk := k.2
  have hk' := k'.2
  by_cases h1 : (k : ℕ) + 1 = p <;> by_cases h2 : (k' : ℕ) + 1 = p
  · omega
  · rw [h1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h'; omega
  · rw [h2, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h'; omega
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'; omega

theorem shiftMat_apply {p : ℕ} (hp : 0 < p) (i k : Fin p) :
    shiftMat p F i k = if i = shiftIdx hp k then 1 else 0 := by
  simp only [shiftMat, Matrix.of_apply, shiftIdx, Fin.ext_iff]

theorem shiftMat_mul_onesM {p : ℕ} (hp : 0 < p) :
    shiftMat p F * onesM = (onesM : Matrix (Fin p) (Fin p) F) := by
  ext i j
  simp only [Matrix.mul_apply, onesM, Matrix.of_apply, mul_one, shiftMat_apply hp]
  obtain ⟨k₀, hk₀⟩ := ((shiftIdx_injective hp).bijective_of_finite).2 i
  rw [Finset.sum_eq_single k₀]
  · simp [hk₀]
  · intro k _ hk
    have : i ≠ shiftIdx hp k := fun h => hk (shiftIdx_injective hp (by rw [hk₀, h]))
    simp [this]
  · simp

theorem onesM_mul_shiftMat {p : ℕ} (hp : 0 < p) :
    (onesM : Matrix (Fin p) (Fin p) F) * shiftMat p F = onesM := by
  ext i j
  simp only [Matrix.mul_apply, onesM, Matrix.of_apply, one_mul, shiftMat_apply hp]
  simp

theorem shiftMat_mul_projF {p : ℕ} (hp : 0 < p) :
    shiftMat p F * projF = (projF : Matrix (Fin p) (Fin p) F) := by
  rw [projF, Matrix.mul_smul, shiftMat_mul_onesM hp]

theorem projF_mul_shiftMat {p : ℕ} (hp : 0 < p) :
    (projF : Matrix (Fin p) (Fin p) F) * shiftMat p F = projF := by
  rw [projF, Matrix.smul_mul, onesM_mul_shiftMat hp]

theorem kr_pow_right {p : ℕ} (K : Matrix (Fin p) (Fin p) F) (m : ℕ) :
    (kr (1 : Matrix (Fin p) (Fin p) F) K) ^ m = kr 1 (K ^ m) := by
  induction m with
  | zero => simp [kr_one]
  | succ m ih => rw [pow_succ, ih, kr_mul, Matrix.mul_one, pow_succ]

theorem kr_one_left_injective {p : ℕ} (hp : 0 < p) {X Y : Matrix (Fin p) (Fin p) F}
    (h : kr 1 X = kr 1 Y) : X = Y := by
  ext j l
  have := congrFun (congrFun h (finProdFinEquiv (⟨0, hp⟩, j))) (finProdFinEquiv (⟨0, hp⟩, l))
  rwa [kr_apply, kr_apply, Matrix.one_apply_eq, one_mul, one_mul] at this

theorem compMat_pow_eq {p : ℕ} (hp : 0 < p) {c : F} {C : Matrix (Fin (p * p)) (Fin (p * p)) F}
    (hC : C ^ p = c • (1 : Matrix (Fin (p * p)) (Fin (p * p)) F)) (P : GL (Fin (p * p)) F)
    (hP : C * (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr 1 (compMat p c)) :
    (compMat p c) ^ p = c • (1 : Matrix (Fin p) (Fin p) F) := by
  have hm : ∀ m : ℕ, C ^ m * (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (kr 1 (compMat p c)) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hP, Matrix.mul_assoc, pow_succ']
  have h1 := hm p
  rw [hC, kr_pow_right, Matrix.smul_mul, Matrix.one_mul] at h1
  have hinv : ((P⁻¹ : GL (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : kr 1 ((compMat p c) ^ p) = c • (1 : Matrix (Fin (p * p)) (Fin (p * p)) F) := by
    calc kr 1 ((compMat p c) ^ p)
        = ((P⁻¹ : GL (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) *
          ((P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr 1 ((compMat p c) ^ p)) := by
          rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = c • 1 := by rw [← h1, Matrix.mul_smul, hinv]
  have h3 : kr 1 ((compMat p c) ^ p) = kr 1 (c • (1 : Matrix (Fin p) (Fin p) F)) := by
    rw [h2, kr_smul_right, kr_one]
  exact kr_one_left_injective hp h3

theorem charMat_mul_compMat {p : ℕ} {ω : F} (hω : ω ^ p = 1) (c : F) :
    charMat p ω * compMat p c = ω • (compMat p c * charMat p ω) := by
  ext i j
  simp only [charMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i : ℕ) = ((j : ℕ) + 1) % p
  · have hi : ω ^ (i : ℕ) = ω * ω ^ (j : ℕ) := by
      rw [h, ← pow_eq_pow_mod _ hω, pow_succ']
    rw [hi]
    simp only [compMat, Matrix.of_apply, h, ↓reduceIte]
    ring
  · simp [compMat, h]

theorem charMat_mul_charMat_inv {p : ℕ} {ω : F} (hω : ω ≠ 0) :
    charMat p ω * charMat p ω⁻¹ = (1 : Matrix (Fin p) (Fin p) F) := by
  rw [charMat, charMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← mul_pow, mul_inv_cancel₀ hω, one_pow]

theorem exists_inv_one_add {p : ℕ} (hodd : Odd p) {c : F} (hc : 1 + c ≠ 0)
    {K : Matrix (Fin p) (Fin p) F} (hK : K ^ p = c • (1 : Matrix (Fin p) (Fin p) F)) :
    ∃ N : Matrix (Fin p) (Fin p) F, (1 + K) * N = 1 ∧ N * (1 + K) = 1 ∧ Commute K N := by
  set G₀ : Matrix (Fin p) (Fin p) F := ∑ i ∈ Finset.range p, (-K) ^ i with hG
  have h1 : (1 + K) * G₀ = (1 + c) • (1 : Matrix (Fin p) (Fin p) F) := by
    have h := mul_neg_geom_sum (-K) p
    rw [sub_neg_eq_add, Odd.neg_pow hodd, hK] at h
    rw [hG, h, sub_neg_eq_add, add_smul, one_smul]
  have h2 : G₀ * (1 + K) = (1 + c) • (1 : Matrix (Fin p) (Fin p) F) := by
    have h := geom_sum_mul_neg (-K) p
    rw [sub_neg_eq_add, Odd.neg_pow hodd, hK] at h
    rw [hG, h, sub_neg_eq_add, add_smul, one_smul]
  refine ⟨(1 + c)⁻¹ • G₀, ?_, ?_, ?_⟩
  · rw [Matrix.mul_smul, h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rw [Matrix.smul_mul, h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · refine Commute.smul_right ?_ _
    exact Commute.sum_right _ _ _ fun i _ => ((Commute.refl K).neg_right.pow_right i)

theorem det_conj_mul_eq_one {p : ℕ} {D D' U N : Matrix (Fin p) (Fin p) F} (hDD : D * D' = 1)
    (hUN : U * N = 1) : (D * U * D' * N).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  have h2 : D.det * D'.det = 1 := by rw [← Matrix.det_mul, hDD, Matrix.det_one]
  have h3 : U.det * N.det = 1 := by rw [← Matrix.det_mul, hUN, Matrix.det_one]
  calc D.det * U.det * D'.det * N.det = (D.det * D'.det) * (U.det * N.det) := by ring
    _ = 1 := by rw [h2, h3, one_mul]

theorem det_Mf_conj {p : ℕ} (hpF : (p : F) ≠ 0) {D D' U N : Matrix (Fin p) (Fin p) F}
    (hDD : D * D' = 1) (hUN : U * N = 1) : (Mf (D * U * D' * N)).det = 1 := by
  have h1 : Mf (D * U * D' * N) = (kr 1 D * Mf U * kr 1 D') * Mf N := by
    rw [← Mf_mul hpF, kr_one_mul_Mf_mul D D' U hDD]
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  have h2 : (kr 1 D).det * (kr 1 D').det = 1 := by
    rw [← Matrix.det_mul, kr_mul, Matrix.one_mul, hDD, kr_one, Matrix.det_one]
  have h3 : (Mf U).det * (Mf N).det = 1 := by
    rw [← Matrix.det_mul, Mf_mul hpF, hUN, Mf_one, Matrix.det_one]
  calc (kr 1 D).det * (Mf U).det * (kr 1 D').det * (Mf N).det
      = ((kr 1 D).det * (kr 1 D').det) * ((Mf U).det * (Mf N).det) := by ring
    _ = 1 := by rw [h2, h3, one_mul]

theorem compMat_one_zero {p : ℕ} (hp3 : 3 ≤ p) (c : F) :
    compMat p c ⟨1, by omega⟩ ⟨0, by omega⟩ = 1 := by
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  simp [compMat, h1, show ¬ (1 = p) by omega]

theorem compMat_zero_zero {p : ℕ} (hp3 : 3 ≤ p) (c : F) :
    compMat p c ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  simp [compMat, h1]

theorem exists_noncentral_block {p : ℕ} (hp3 : 3 ≤ p) (hodd : Odd p) {ω c : F}
    (hω : IsPrimitiveRoot ω p) (hc : 1 + c ≠ 0)
    (hKp : (compMat p c) ^ p = c • (1 : Matrix (Fin p) (Fin p) F)) :
    ∃ (a : SpecialLinearGroup (Fin p) F) (D D' U N : Matrix (Fin p) (Fin p) F),
      a ∉ Subgroup.center (SpecialLinearGroup (Fin p) F) ∧
      (a : Matrix (Fin p) (Fin p) F) * compMat p c = compMat p c * (a : Matrix (Fin p) (Fin p) F) ∧
      D * D' = 1 ∧ U * N = 1 ∧ (a : Matrix (Fin p) (Fin p) F) = D * U * D' * N := by
  have hp : 0 < p := by omega
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hω1 : ω ≠ 1 := hω.ne_one (by omega)
  obtain ⟨N, hUN, hNU, hKN⟩ := exists_inv_one_add hodd hc hKp
  have hDD : charMat p ω * charMat p ω⁻¹ = (1 : Matrix (Fin p) (Fin p) F) :=
    charMat_mul_charMat_inv hω0
  have hDK : charMat p ω * compMat p c = ω • (compMat p c * charMat p ω) :=
    charMat_mul_compMat hω.pow_eq_one c
  have hV : charMat p ω * (1 + compMat p c) * charMat p ω⁻¹ = 1 + ω • compMat p c := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hDD, hDK, Matrix.smul_mul,
      Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hdet := det_conj_mul_eq_one hDD hUN
  refine ⟨⟨charMat p ω * (1 + compMat p c) * charMat p ω⁻¹ * N, hdet⟩, charMat p ω,
    charMat p ω⁻¹, 1 + compMat p c, N, ?_, ?_, hDD, hUN, rfl⟩
  · intro hcen
    obtain ⟨lm, -, hlm⟩ := exists_scalar_of_mem_center hp hcen
    have hlm' : (1 + ω • compMat p c) * N = lm • (1 : Matrix (Fin p) (Fin p) F) := by
      rw [← hV]; exact hlm
    have h1 : 1 + ω • compMat p c = lm • (1 + compMat p c) := by
      have := congrArg (fun X => X * (1 + compMat p c)) hlm'
      simpa [Matrix.mul_assoc, hNU, Matrix.smul_mul] using this
    have e10 := congrFun (congrFun h1 ⟨1, by omega⟩) ⟨0, hp⟩
    have e00 := congrFun (congrFun h1 ⟨0, hp⟩) ⟨0, hp⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      compMat_one_zero hp3, compMat_zero_zero hp3] at e10 e00
    simp at e10 e00
    exact hω1 (by rw [e10, ← e00])
  · show (charMat p ω * (1 + compMat p c) * charMat p ω⁻¹ * N) * compMat p c =
      compMat p c * (charMat p ω * (1 + compMat p c) * charMat p ω⁻¹ * N)
    rw [hV]
    exact ((Commute.add_right (Commute.one_right (compMat p c))
      (Commute.smul_right (Commute.refl (compMat p c)) ω)).mul_right hKN).eq.symm

end CFSG.LieType.SeitzGeneration
