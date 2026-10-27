module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsMatrix

public section

namespace CFSG.Wreathed.OriginalAllPrime.V4InputsW

open Matrix CFSG.Wreathed.CentralSL2Abelianization CFSG.Wreathed.OddFieldTorus
open CFSG.Semidihedral.ProjectiveSL2Cover CFSG.Wreathed.OriginalAllPrime.IVFacts

variable {F : Type} [Field F]

theorem charP_of_card_eq_pow [Finite F] {p f : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ f) :
    CharP F p := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, hs, k, hsp, hk⟩ := FiniteField.card' (K := F)
  rw [← Nat.card_eq_fintype_card, hcard] at hk
  have hsr : s = p := by
    have h1 : s ∣ p ^ f := by rw [hk]; exact dvd_pow_self s k.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hsp hp).mp (hsp.dvd_of_dvd_pow h1)
  rw [hsr] at hs
  exact hs

theorem trace_eq_two_of_mulVec_eq {Z : SpecialLinearGroup (Fin 2) F} {v : Fin 2 → F}
    (hv : v ≠ 0) (hZ : (Z : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) :
    (Z : Matrix (Fin 2) (Fin 2) F) 0 0 + (Z : Matrix (Fin 2) (Fin 2) F) 1 1 = 2 := by
  have hdet : ((Z : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hZ, Matrix.one_mulVec, sub_self]⟩
  have hZd : (Z : Matrix (Fin 2) (Fin 2) F).det = 1 := Z.2
  rw [Matrix.det_fin_two] at hdet hZd
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hdet
  linear_combination hZd - hdet

theorem pow_char_eq_one_of_mulVec_eq {p : ℕ} [CharP F p] {Z : SpecialLinearGroup (Fin 2) F}
    {v : Fin 2 → F} (hv : v ≠ 0) (hZ : (Z : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : Z ^ p = 1 := by
  have htr := trace_eq_two_of_mulVec_eq hv hZ
  have hZd : (Z : Matrix (Fin 2) (Fin 2) F).det = 1 := Z.2
  rw [Matrix.det_fin_two] at hZd
  set A : Matrix (Fin 2) (Fin 2) F := (Z : Matrix (Fin 2) (Fin 2) F) - 1 with hAdef
  have hA2 : A * A = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hAdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply] <;>
      first
      | linear_combination (Z : Matrix (Fin 2) (Fin 2) F) 0 0 * htr - hZd
      | linear_combination (Z : Matrix (Fin 2) (Fin 2) F) 0 1 * htr
      | linear_combination (Z : Matrix (Fin 2) (Fin 2) F) 1 0 * htr
      | linear_combination (Z : Matrix (Fin 2) (Fin 2) F) 1 1 * htr - hZd
  have hZA : (Z : Matrix (Fin 2) (Fin 2) F) = 1 + A := by rw [hAdef]; abel
  have hpow : ∀ k : ℕ, (Z : Matrix (Fin 2) (Fin 2) F) ^ k = 1 + (k : F) • A := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, hZA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
        Matrix.smul_mul, hA2, smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]
      abel
  have hcoe : ((Z ^ p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (Z : Matrix (Fin 2) (Fin 2) F) ^ p := Matrix.SpecialLinearGroup.coe_pow Z p
  apply SL_ext
  rw [hcoe, hpow p, CharP.cast_eq_zero, zero_smul, add_zero, SL_coe_one]

theorem exists_eq_smul_of_mulVec_eq_zero {A : Matrix (Fin 2) (Fin 2) F} (hA : A ≠ 0)
    {u v : Fin 2 → F} (hv : v ≠ 0) (hAv : A *ᵥ v = 0) (hAu : A *ᵥ u = 0) :
    ∃ c : F, u = c • v := by
  have ev : ∀ i, A i 0 * v 0 + A i 1 * v 1 = 0 := fun i => by
    have h := congrFun hAv i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have eu : ∀ i, A i 0 * u 0 + A i 1 * u 1 = 0 := fun i => by
    have h := congrFun hAu i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hD : v 0 * u 1 - v 1 * u 0 = 0 := by
    by_contra hD
    apply hA
    ext i j
    fin_cases j
    · have h : A i 0 * (v 0 * u 1 - v 1 * u 0) = 0 := by
        linear_combination u 1 * ev i - v 1 * eu i
      simpa [hD] using h
    · have h : A i 1 * (v 0 * u 1 - v 1 * u 0) = 0 := by
        linear_combination v 0 * eu i - u 0 * ev i
      simpa [hD] using h
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hu0 : u 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at hD
      exact (mul_eq_zero.mp hD).resolve_left h1
    refine ⟨u 1 / v 1, ?_⟩
    ext i
    fin_cases i
    · simp [h0, hu0]
    · simp [h1]
  · refine ⟨u 0 / v 0, ?_⟩
    ext i
    fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination hD

theorem SL_smul_eq_mulVec (Z : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    Z • v = (Z : Matrix (Fin 2) (Fin 2) F) *ᵥ v :=
  (Matrix.SpecialLinearGroup.smul_def Z v).trans (Matrix.smul_eq_mulVec _ _)

theorem exists_fixed_vector [Finite F] {p : ℕ} [Fact p.Prime] (hpF : p ∣ Nat.card F)
    {P : Subgroup (SpecialLinearGroup (Fin 2) F)} (hP : IsPGroup p P) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ z ∈ P, (z : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
  have h0 : (0 : Fin 2 → F) ∈ MulAction.fixedPoints P (Fin 2 → F) := fun z => by
    rw [Subgroup.smul_def, SL_smul_eq_mulVec, Matrix.mulVec_zero]
  have hcard : p ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    exact dvd_pow hpF two_ne_zero
  obtain ⟨v, hv, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F)
    hcard h0
  refine ⟨v, fun h => hne h.symm, fun z hz => ?_⟩
  have h := hv ⟨z, hz⟩
  rwa [Subgroup.smul_def, SL_smul_eq_mulVec] at h

theorem commutator_pow_char_eq_one_of_mem_normalizer [Finite F] {p : ℕ} [Fact p.Prime]
    [CharP F p] (hpF : p ∣ Nat.card F) {P : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hP : IsPGroup p P) (hP1 : P ≠ ⊥) {g h : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ Subgroup.normalizer (P : Set _)) (hh : h ∈ Subgroup.normalizer (P : Set _)) :
    (g * h * g⁻¹ * h⁻¹) ^ p = 1 := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector hpF hP
  obtain ⟨z₀, hz₀, hz₀1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hP1
  have hA : (z₀ : Matrix (Fin 2) (Fin 2) F) - 1 ≠ 0 := by
    intro h0
    apply hz₀1
    apply SL_ext
    rw [sub_eq_zero] at h0
    rw [h0, SL_coe_one]
  have hAv : ((z₀ : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hv z₀ hz₀, Matrix.one_mulVec, sub_self]
  have hline : ∀ k ∈ Subgroup.normalizer (P : Set (SpecialLinearGroup (Fin 2) F)),
      ∃ c : F, (k : Matrix (Fin 2) (Fin 2) F) *ᵥ v = c • v := by
    intro k hk
    apply exists_eq_smul_of_mulVec_eq_zero hA hv0 hAv
    have hk' : k⁻¹ * z₀ * k ∈ P := (Subgroup.mem_normalizer_iff''.mp hk z₀).mp hz₀
    have h1 := hv _ hk'
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, Matrix.mulVec_mulVec]
    have h2 : z₀ * k = k * (k⁻¹ * z₀ * k) := by group
    rw [← SL_coe_mul, h2, SL_coe_mul, ← Matrix.mulVec_mulVec, h1]
  have hinv : ∀ k ∈ Subgroup.normalizer (P : Set (SpecialLinearGroup (Fin 2) F)), ∀ c c' : F,
      (k : Matrix (Fin 2) (Fin 2) F) *ᵥ v = c • v →
        ((k⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = c' • v →
          c' * c = 1 := by
    intro k _ c c' hc hc'
    have h1 : v = (c' * c) • v := by
      calc v = ((k * k⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
            rw [mul_inv_cancel, SL_coe_one, Matrix.one_mulVec]
        _ = (c' * c) • v := by
            rw [SL_coe_mul, ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul, hc,
              smul_smul]
    have h2 : (c' * c - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv0
  obtain ⟨cg, hcg⟩ := hline g hg
  obtain ⟨ch, hch⟩ := hline h hh
  obtain ⟨cg', hcg'⟩ := hline g⁻¹ (Subgroup.inv_mem _ hg)
  obtain ⟨ch', hch'⟩ := hline h⁻¹ (Subgroup.inv_mem _ hh)
  have hgg := hinv g hg cg cg' hcg hcg'
  have hhh := hinv h hh ch ch' hch hch'
  apply pow_char_eq_one_of_mulVec_eq hv0
  simp only [SL_coe_mul]
  rw [← Matrix.mulVec_mulVec, hch', Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hcg',
    Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hch, Matrix.mulVec_smul, hcg, smul_smul,
    smul_smul, smul_smul]
  have h1 : ch' * cg' * ch * cg = (ch' * ch) * (cg' * cg) := by ring
  rw [h1, hgg, hhh, one_mul, one_smul]

theorem mem_torus_of_commute {w Z : SpecialLinearGroup (Fin 2) F} (hw : w ∈ torus F)
    (hw1 : w ≠ 1) (hw2 : w ≠ minusIdentity F) (hZ : Z * w = w * Z) : Z ∈ torus F := by
  obtain ⟨k1, k2⟩ := (mem_torus_coord_iff w).mp hw
  have hβ : (w : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    intro hβ
    have hdet : (w : Matrix (Fin 2) (Fin 2) F).det = 1 := w.2
    rw [Matrix.det_fin_two, k1, k2, hβ, neg_zero, zero_mul, sub_zero] at hdet
    have hsq : ((w : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * ((w : Matrix (Fin 2) (Fin 2) F) 0 0 + 1)
        = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp hsq with h | h
    · apply hw1
      apply SL_ext
      ext i j
      fin_cases i <;> fin_cases j
      · change (w : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
        linear_combination h
      · change (w : Matrix (Fin 2) (Fin 2) F) 0 1 = 0
        rw [k2, hβ, neg_zero]
      · change (w : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        exact hβ
      · change (w : Matrix (Fin 2) (Fin 2) F) 1 1 = 1
        rw [k1]
        linear_combination h
    · apply hw2
      apply SL_ext
      ext i j
      fin_cases i <;> fin_cases j
      · change (w : Matrix (Fin 2) (Fin 2) F) 0 0 = (minusIdentity F : Matrix (Fin 2) (Fin 2) F) 0 0
        rw [minusIdentity_coe]
        simp only [Matrix.neg_apply, Matrix.one_apply_eq]
        linear_combination h
      · change (w : Matrix (Fin 2) (Fin 2) F) 0 1 = (minusIdentity F : Matrix (Fin 2) (Fin 2) F) 0 1
        rw [minusIdentity_coe, k2, hβ]
        simp
      · change (w : Matrix (Fin 2) (Fin 2) F) 1 0 = (minusIdentity F : Matrix (Fin 2) (Fin 2) F) 1 0
        rw [minusIdentity_coe, hβ]
        simp
      · change (w : Matrix (Fin 2) (Fin 2) F) 1 1 = (minusIdentity F : Matrix (Fin 2) (Fin 2) F) 1 1
        rw [minusIdentity_coe, k1]
        simp only [Matrix.neg_apply, Matrix.one_apply_eq]
        linear_combination h
  have hm := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hZ
  simp only [SL_coe_mul] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  simp only [mul_apply_two, k1, k2] at h00 h01
  rw [mem_torus_coord_iff]
  constructor
  · have h : (w : Matrix (Fin 2) (Fin 2) F) 1 0 *
        ((Z : Matrix (Fin 2) (Fin 2) F) 1 1 - (Z : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
      linear_combination h01
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hβ)
  · have h : (w : Matrix (Fin 2) (Fin 2) F) 1 0 *
        ((Z : Matrix (Fin 2) (Fin 2) F) 0 1 + (Z : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 := by
      linear_combination h00
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h).resolve_left hβ)

end CFSG.Wreathed.OriginalAllPrime.V4InputsW
