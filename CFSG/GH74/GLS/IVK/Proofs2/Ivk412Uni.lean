module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Lin

public section

open Subgroup CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial Matrix

namespace CFSG.GH74.GLS.IVK.Proofs2

section Rlm

variable {F : Type} [Field F]

@[expose] def Rlm (i l m : F) : Matrix (Fin 2) (Fin 2) F :=
  !![(l + m) / 2, i * (m - l) / 2; -(i * (m - l) / 2), (l + m) / 2]

variable {i : F} (h2 : (2 : F) ≠ 0)

include h2

theorem Rlm_mul (hi : i * i = -1) (l m l' m' : F) :
    Rlm i l m * Rlm i l' m' = Rlm i (l * l') (m * m') := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Rlm, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | linear_combination (-(l * l') + l * m' + m * l' - m * m') * hi | ring

theorem Rlm_one : Rlm i 1 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Rlm] <;> field_simp <;> norm_num

theorem Rlm_neg (l m : F) : -Rlm i l m = Rlm i (-l) (-m) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Rlm] <;> field_simp <;> ring

theorem Rlm_refl (l m : F) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * Rlm i l m * !![1, 0; 0, -1] = Rlm i m l := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Rlm, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem Rlm_det (hi : i * i = -1) (l m : F) : (Rlm i l m).det = l * m := by
  simp only [Rlm, Matrix.det_fin_two_of]
  field_simp
  linear_combination ((m - l) ^ 2) * hi

theorem Rlm_pow (hi : i * i = -1) (l m : F) (k : ℕ) : (Rlm i l m) ^ k = Rlm i (l ^ k) (m ^ k) := by
  induction k with
  | zero => simp [Rlm_one h2]
  | succ k ih => rw [pow_succ, ih, Rlm_mul h2 hi, ← pow_succ, ← pow_succ]

theorem Rlm_transpose (l m : F) : (Rlm i l m)ᵀ = Rlm i m l := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Rlm] <;> field_simp <;> ring

omit h2 in
theorem Rlm_map (σ : F →+* F) (hσ : σ i = i) (l m : F) :
    (Rlm i l m).map σ = Rlm i (σ l) (σ m) := by
  have h22 : σ 2 = 2 := map_ofNat σ 2
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Rlm, hσ, h22]

end Rlm

theorem arith_uni (q : ℕ) (h4 : q % 4 = 1) (h5 : 5 ≤ q) :
    ∃ s j a : ℕ, 2 ≤ s ∧ Odd j ∧ Odd a ∧ q + 1 = 2 * a ∧ q - 1 = 2 ^ s * j ∧
      q ^ 2 - 1 = (a * j) * 2 ^ (s + 1) := by
  obtain ⟨s, j, hj, hqs⟩ := Nat.exists_eq_two_pow_mul_odd (n := q - 1) (by omega)
  have hs : 2 ≤ s := by
    by_contra h
    replace h := not_le.1 h
    interval_cases s
    · obtain ⟨t, rfl⟩ := hj
      omega
    · obtain ⟨t, rfl⟩ := hj
      omega
  obtain ⟨a, ha⟩ : ∃ a, q + 1 = 2 * a := ⟨(q + 1) / 2, by omega⟩
  refine ⟨s, j, a, hs, hj, ⟨a / 2, by omega⟩, ha, hqs, ?_⟩
  have h1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨b, hb⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    subst hb
    simp only [Nat.add_sub_cancel]
    have e : (b + 1) ^ 2 = b * (b + 1 + 1) + 1 := by ring
    omega
  rw [h1, hqs, ha]
  ring

section UniCore

variable {F : Type} [Field F]

@[expose] noncomputable def rotUnit (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {ζ : F} (hζ : ζ ≠ 0) :
    GL (Fin 2) F where
  val := Rlm i ζ (-ζ⁻¹)
  inv := Rlm i ζ⁻¹ (-ζ)
  val_inv := by
    rw [Rlm_mul h2 hi, mul_inv_cancel₀ hζ, neg_mul_neg, inv_mul_cancel₀ hζ, Rlm_one h2]
  inv_val := by
    rw [Rlm_mul h2 hi, inv_mul_cancel₀ hζ, neg_mul_neg, mul_inv_cancel₀ hζ, Rlm_one h2]

theorem coe_rotUnit (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {ζ : F} (hζ : ζ ≠ 0) :
    ((rotUnit h2 hi hζ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Rlm i ζ (-ζ⁻¹) := rfl

theorem coe_rotUnit_inv (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {ζ : F} (hζ : ζ ≠ 0) :
    (((rotUnit h2 hi hζ)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Rlm i ζ⁻¹ (-ζ) := rfl

theorem rotUnit_det (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {ζ : F} (hζ : ζ ≠ 0) :
    ((rotUnit h2 hi hζ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
      ((rotUnit h2 hi hζ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [coe_rotUnit, Rlm_det h2 hi]
  field_simp

theorem rotUnit_refl (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {ζ : F} (hζ : ζ ≠ 0) :
    dRefl F * rotUnit h2 hi hζ * dRefl F = -(rotUnit h2 hi hζ)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_neg, coe_dRefl, coe_rotUnit, coe_rotUnit_inv,
    Rlm_refl h2, Rlm_neg h2, neg_neg]

theorem rotUnit_pow (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {ζ : F} (hζ : ζ ≠ 0) {s : ℕ}
    (hs : 1 ≤ s) (hζs : ζ ^ 2 ^ s = -1) : rotUnit h2 hi hζ ^ 2 ^ s = -1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_rotUnit, Rlm_pow h2 hi, hζs]
  have hev : Even (2 ^ s) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have h1 : (-ζ⁻¹) ^ 2 ^ s = -1 := by
    rw [hev.neg_pow, inv_pow, hζs]
    norm_num
  rw [h1, Units.val_neg, Units.val_one, ← Rlm_one h2 (i := i), Rlm_neg h2]

theorem rotUnit_unitary (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {ζ : F} (hζ : ζ ≠ 0)
    (σ : F ≃+* F) (hσi : σ i = i) (hσζ : σ ζ = -ζ) :
    conjTr σ ((rotUnit h2 hi hζ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((rotUnit h2 hi hζ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have hm : σ (-ζ⁻¹) = ζ⁻¹ := by
    rw [map_neg, map_inv₀, hσζ, inv_neg, neg_neg]
  have h1 : conjTr σ ((rotUnit h2 hi hζ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Rlm i ζ⁻¹ (-ζ) := by
    rw [coe_rotUnit, conjTr]
    have := Rlm_map (σ.toRingHom) hσi ζ (-ζ⁻¹)
    change ((Rlm i ζ (-ζ⁻¹)).map (σ.toRingHom))ᵀ = _
    rw [this, Rlm_transpose h2]
    show Rlm i (σ (-ζ⁻¹)) (σ ζ) = _
    rw [hm, hσζ]
  rw [h1, coe_rotUnit, Rlm_mul h2 hi, inv_mul_cancel₀ hζ, neg_mul_neg, mul_inv_cancel₀ hζ,
    Rlm_one h2]

end UniCore

section UniExist

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem unitaryInvolution_eq_of_pow (c : F) (hc : c ^ (p ^ f) = c) :
    unitaryInvolution F p f c = c := by
  rw [unitaryInvolution_apply]
  exact hc

theorem exists_rotData_uni (hF : Nat.card F = (p ^ f) ^ 2) (h4 : p ^ f % 4 = 1) (h5 : 5 ≤ p ^ f) :
    ∃ (n : ℕ) (D : RotData (ModelData.uni hF)), 3 ≤ n ∧ D.R ^ 2 ^ (n - 1) = -1 ∧
      ∃ h' : ℕ, Odd h' ∧ Nat.card ↥(ModelData.uni hF).H2 = 2 ^ n * h' := by
  have hqodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
  have hFodd : Odd (Nat.card F) := by rw [hF]; exact hqodd.pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hFodd
  obtain ⟨s, j, a, hs, hj, ha, hqa, hqs, hq2⟩ := arith_uni (p ^ f) h4 h5
  obtain ⟨i, hi⟩ : ∃ i : F, i * i = -1 := by
    have := Fintype.ofFinite F
    have hsq : IsSquare (-1 : F) := by
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF]
      obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
      rw [hk]
      ring_nf
      omega
    obtain ⟨i, hi⟩ := hsq
    exact ⟨i, hi.symm⟩
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
  have hi4 : i ^ 4 = 1 := by
    have : i ^ 4 = (i * i) * (i * i) := by ring
    rw [this, hi]
    norm_num
  have hσi : unitaryInvolution F p f i = i := by
    apply unitaryInvolution_eq_of_pow
    rw [hk, pow_succ, pow_mul, hi4, one_pow, one_mul]
  have hN : Nat.card F - 1 = (a * j) * 2 ^ (s + 1) := by rw [hF]; exact hq2
  obtain ⟨ζu, hζ⟩ := exists_pow_two_pow_eq_neg_one F (w := a * j) (t := s)
    (Nat.mul_pos ha.pos hj.pos) hN
  have hζ0 : (ζu : F) ≠ 0 := ζu.ne_zero
  have hζq1 : (ζu : F) ^ (p ^ f - 1) = -1 := by
    rw [hqs, pow_mul, hζ]
    exact Odd.neg_one_pow hj
  have hζq : (ζu : F) ^ (p ^ f) = -(ζu : F) := by
    have : p ^ f = (p ^ f - 1) + 1 := by omega
    rw [this, pow_succ, hζq1, neg_one_mul]
  have hσζ : unitaryInvolution F p f (ζu : F) = -(ζu : F) := by
    rw [unitaryInvolution_apply]
    exact hζq
  let R : GL (Fin 2) F := rotUnit h2 hi hζ0
  have hR : R ∈ (ModelData.uni hF).U2 := by
    show conjTr (unitaryInvolution F p f) (R : Matrix (Fin 2) (Fin 2) F) *
      (R : Matrix (Fin 2) (Fin 2) F) = 1
    exact rotUnit_unitary h2 hi hζ0 _ hσi hσζ
  have hRn : R ^ 2 ^ s = -1 := rotUnit_pow h2 hi hζ0 (by omega) hζ
  refine ⟨s + 1, ⟨R, hR, dRefl_mem_uni, rotUnit_det h2 hi hζ0, rotUnit_refl h2 hi hζ0⟩,
    by omega, ?_, ?_⟩
  · show R ^ 2 ^ (s + 1 - 1) = -1
    rw [Nat.add_sub_cancel]
    exact hRn
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · have := Finite.one_lt_card (α := F)
        rw [hF] at this
        simp at this
      · exact hf
    have hfld : UnitaryFieldData p f F := ⟨Fact.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩
    have hH : (Nat.card ↥(ModelData.uni hF).H2 : ℤ) =
        ((p ^ f : ℕ) : ℤ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
      have := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hfld (n := 2) (by norm_num)
      rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.prod_Icc_two_two,
        show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at this
      exact this
    refine ⟨(p ^ f) * (a * j), hqodd.mul (ha.mul hj), ?_⟩
    have hq1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    apply Nat.cast_injective (R := ℤ)
    rw [hH, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_mul]
    have : (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) = (a : ℤ) * j * 2 ^ (s + 1) := by
      rw [hq2]
      push_cast
      ring
    push_cast [Nat.cast_sub hq1] at this ⊢
    rw [show ((p : ℤ) ^ f) ^ 2 - 1 = a * j * 2 ^ (s + 1) from this]
    ring

theorem prop412_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (h4 : p ^ f % 4 = 1) : Prop412 (PG (ModelData.uni hF)) := by
  have hG := goodModel_uni hF hp2 h5
  have hZ := zsTwo_uni hF h4
  have hC := clsFacts_uni hF hp2 h5 h4
  obtain ⟨n, D, hn, hRn, h', hh', hH⟩ := exists_rotData_uni hF h4 h5
  obtain ⟨o, ho, hcard⟩ := card_PG_eq_of_good hG hZ (card_U2_uni hF hp2)
  obtain ⟨a', ha1, ha2⟩ : ∃ a', p ^ f + 1 = 2 * a' ∧ Odd a' :=
    ⟨(p ^ f + 1) / 2, by omega, ⟨p ^ f / 4, by omega⟩⟩
  rw [hH, ha1] at hcard
  refine prop412_of_rotData D hG hZ hC hn hRn (m := o * a' * h' ^ 2)
    ((ho.mul ha2).mul (hh'.pow)) ?_
  rw [hcard]
  ring

end UniExist

end CFSG.GH74.GLS.IVK.Proofs2
