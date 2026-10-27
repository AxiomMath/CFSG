module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd compInd_mul_apply mul_compInd_apply
  compInd_apply pairBlk PairDiag pairDiag_mul pairBlk_mul pairBlk_one pairBlk_pow pairDiag_pow
  pairDiag_of_commute tr2 sq_fin_two)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem trace_eq_two_of_odd_char3 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) = 0)
    {z : Matrix (Fin 2) (Fin 2) K} (hdet : z.det = 1) (ht : tr2 z = 0 ∨ tr2 z = 1 ∨ tr2 z = -1)
    {m : ℕ} (hm : Odd m) (hz : z ^ m = 1) : tr2 z = 2 := by
  have hCH := sq_fin_two z
  rw [hdet, one_smul] at hCH
  change z * z = tr2 z • z - 1 at hCH
  obtain ⟨k, rfl⟩ := hm
  rcases ht with h0 | h1 | hm1
  ·
    exfalso
    rw [h0, zero_smul, zero_sub] at hCH
    have hpow : z ^ (2 * k + 1) = (-1 : Matrix (Fin 2) (Fin 2) K) ^ k * z := by
      rw [pow_succ, pow_mul, pow_two, hCH]
    rw [hz] at hpow
    have hz' : z = (-1 : Matrix (Fin 2) (Fin 2) K) ^ k := by
      have hsq : ((-1 : Matrix (Fin 2) (Fin 2) K) ^ k) * ((-1) ^ k) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      calc z = ((-1 : Matrix (Fin 2) (Fin 2) K) ^ k * (-1) ^ k) * z := by rw [hsq, one_mul]
        _ = (-1) ^ k * ((-1) ^ k * z) := by rw [mul_assoc]
        _ = (-1) ^ k := by rw [← hpow, mul_one]
    have : z * z = 1 := by rw [hz', ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [this] at hCH
    have e := congrFun (congrFun hCH 0) 0
    simp at e
    exact h2 (by linear_combination e)
  ·
    exfalso
    rw [h1, one_smul] at hCH
    have h3' : z ^ 3 = -1 := by
      rw [pow_succ, pow_two, hCH, Matrix.sub_mul, hCH, Matrix.one_mul]
      abel
    have h6 : z ^ 6 = 1 := by
      rw [show 6 = 3 * 2 by rfl, pow_mul, h3', neg_one_sq]
    have hz1 : z ^ ((2 * k + 1) % 6) = 1 := by
      rw [← hz, ← Nat.div_add_mod (2 * k + 1) 6, pow_add, pow_mul, h6, one_pow, one_mul,
        Nat.div_add_mod]
    have hr : (2 * k + 1) % 6 = 1 ∨ (2 * k + 1) % 6 = 3 ∨ (2 * k + 1) % 6 = 5 := by omega
    have hzone : z = 1 → False := by
      intro e1
      rw [e1] at h1
      simp only [tr2, one_apply_eq] at h1
      exact one_ne_zero (α := K) (by linear_combination h1)
    rcases hr with hr | hr | hr
    · rw [hr, pow_one] at hz1
      exact hzone hz1
    · rw [hr, h3'] at hz1
      have e := congrFun (congrFun hz1 0) 0
      simp at e
      exact h2 (by linear_combination -e)
    · rw [hr] at hz1
      apply hzone
      calc z = 1 * z := (one_mul z).symm
        _ = z ^ 5 * z := by rw [hz1]
        _ = z ^ 6 := (pow_succ z 5).symm
        _ = 1 := h6
  · rw [hm1]
    linear_combination -h3

theorem bar_trace_of_unitary {z : Matrix (Fin 2) (Fin 2) K} (hdet : z.det = 1)
    (hz : (z.map h.bar)ᵀ * z = 1) : h.bar (tr2 z) = tr2 z := by
  have hinv : (z.map h.bar)ᵀ = adjugate z := by
    have e1 : (z.map h.bar)ᵀ = z⁻¹ := (Matrix.inv_eq_left_inv hz).symm
    rw [e1, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have e00 := congrFun (congrFun hinv 0) 0
  have e11 := congrFun (congrFun hinv 1) 1
  rw [adjugate_fin_two] at e00 e11
  simp only [transpose_apply, map_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at e00 e11
  rw [tr2, map_add, e00, e11, add_comm]

theorem mem_three_of_bar (h3 : p ^ f = 3) {t : K} (ht : h.bar t = t) :
    t = 0 ∨ t = 1 ∨ t = -1 := by
  rw [h.bar_apply, h3] at ht
  have e : t * ((t - 1) * (t + 1)) = 0 := by linear_combination ht
  rcases mul_eq_zero.1 e with e | e
  · exact Or.inl e
  rcases mul_eq_zero.1 e with e | e
  · exact Or.inr (Or.inl (sub_eq_zero.1 e))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left e))

theorem scalar_of_commutator_traces_u {ι : K} (hι : ι * ι = -1) (h2 : (2 : K) ≠ 0)
    {P Pi : Matrix (Fin 2) (Fin 2) K} (h1 : P * Pi = 1)
    (ht1 : tr2 (P * !![ι, 0; 0, -ι] * Pi * !![-ι, 0; 0, ι]) = 2)
    (ht2 : tr2 (P * !![(0 : K), 1; -1, 0] * Pi * !![(0 : K), -1; 1, 0]) = 2)
    (ht3 : tr2 (P * !![0, ι; ι, 0] * Pi * !![0, -ι; -ι, 0]) = 2) :
    P 0 1 = 0 ∧ P 1 0 = 0 ∧ P 0 0 = P 1 1 := by
  have hdet : P.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hPi : Pi = P⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  rw [Matrix.inv_def, Ring.inverse_eq_inv'] at hPi
  subst hPi
  set a := P 0 0
  set b := P 0 1
  set c := P 1 0
  set d := P 1 1
  have hP : P = !![a, b; c, d] := Matrix.eta_fin_two P
  rw [hP, det_fin_two_of] at hdet
  rw [hP, adjugate_fin_two_of, det_fin_two_of] at ht1 ht2 ht3
  simp only [tr2, Matrix.mul_fin_two, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty,
    smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at ht1 ht2 ht3
  have hΔ : (a * d - b * c) * (a * d - b * c)⁻¹ = 1 := mul_inv_cancel₀ hdet
  set e := (a * d - b * c)⁻¹ with he
  have he0 : e ≠ 0 := inv_ne_zero hdet
  have E1 : (4 * (b * c)) * e = 0 := by
    linear_combination ht1 + (2 * a * d * e + 2 * b * c * e) * hι - 2 * hΔ
  have E2 : ((a - d) ^ 2 + (b + c) ^ 2) * e = 0 := by linear_combination ht2 - 2 * hΔ
  have E3 : ((a - d) ^ 2 - (b - c) ^ 2) * e = 0 := by
    linear_combination ht3 + ((a ^ 2 - b ^ 2 + d ^ 2 - c ^ 2) * e) * hι - 2 * hΔ
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hbc : b * c = 0 := (mul_eq_zero.1 ((mul_eq_zero.1 E1).resolve_right he0)).resolve_left h4
  have F2 := (mul_eq_zero.1 E2).resolve_right he0
  have F3 := (mul_eq_zero.1 E3).resolve_right he0
  have hsq : (b + c) ^ 2 = 0 := by
    have : 2 * (b + c) ^ 2 = 0 := by linear_combination F2 - F3 + 4 * hbc
    exact (mul_eq_zero.1 this).resolve_left h2
  have had : (a - d) ^ 2 = 0 := by linear_combination F2 - hsq
  have hb2 : b ^ 2 + c ^ 2 = 0 := by linear_combination hsq - 2 * hbc
  have hb : b = 0 ∧ c = 0 := by
    rcases mul_eq_zero.1 hbc with hb | hc
    · refine ⟨hb, ?_⟩
      rw [hb] at hb2
      exact pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination hb2)
    · refine ⟨?_, hc⟩
      rw [hc] at hb2
      exact pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination hb2)
  exact ⟨hb.1, hb.2, sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 had)⟩

theorem exists_iota (h3 : p ^ f = 3) : ∃ ι : K, ι ≠ 0 ∧ h.norm ι = 1 ∧ ι * ι = -1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨l, hl, hlo⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq h.card_eq_sq
  rw [h3] at hlo
  refine ⟨l, l.ne_zero, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, mul_comm, h.bar_apply,
      ← CFSG.LieType.BorelTits.unitaryInvolution_apply]
    exact hl
  · have h4 : (l : K) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, show (4 : ℕ) = 3 + 1 by rfl, ← hlo, pow_orderOf_eq_one,
        Units.val_one]
    have h2 : (l : K) ^ 2 ≠ 1 := by
      intro e
      have : l ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one])
      have := orderOf_le_of_pow_eq_one (by norm_num) this
      omega
    have e : ((l : K) * l - 1) * ((l : K) * l + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 e with e | e
    · exact absurd (by linear_combination e) h2
    · linear_combination e

theorem pairDiag_of_mem_uBlock {i j : Fin n} {x : StatedSU n (p ^ f) K}
    (hx : x ∈ uBlock p f K {i, j}) :
    PairDiag i j ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro k l hkl
  have hkl' : k ≠ l := by
    rintro rfl
    tauto
  rw [mem_uBlock_iff.1 hx k l (by by_cases hk : k ∈ ({i, j} : Finset (Fin n)) <;> tauto)]
  simp [hkl']

theorem pairDiag_conjTr {i j : Fin n} {A : Matrix (Fin n) (Fin n) K} (hA : PairDiag i j A) :
    PairDiag i j ((A.map h.bar)ᵀ) := by
  intro k l hkl
  rw [transpose_apply, map_apply, hA l k (by tauto), map_zero]

theorem pairBlk_conjTr (i j : Fin n) (A : Matrix (Fin n) (Fin n) K) :
    pairBlk i j ((A.map h.bar)ᵀ) = ((pairBlk i j A).map h.bar)ᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairBlk]

include h in
theorem uThree_block (h3 : p ^ f = 3) {i j : Fin n} (hij : i ≠ j) {D : uU h n}
    (hD : compInd K {i, j} * ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {i, j})
    (hodd : ∀ x ∈ uBlock p f K {i, j},
      Odd (orderOf ((⟨_, uConjSU_mem h D x⟩ : StatedSU n (p ^ f) K) * x⁻¹))) :
    ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 ∧
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j i = 0 ∧
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
        ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j := by
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1
      (by rw [← h3]; exact dvd_pow_self p (by have := h.one_le; omega))
  have := h.charP
  have h3K : (3 : K) = 0 := by
    have := CharP.cast_eq_zero K p
    rw [hp3] at this
    exact_mod_cast this
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have : (1 : K) = 0 := by linear_combination h3K - e
    exact one_ne_zero this
  obtain ⟨ι, hι0, hιN, hι⟩ := exists_iota h h3
  set M := ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  set Mi := (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMi
  have h1 : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMd : PairDiag i j M := pairDiag_of_commute hD
  have hDi : compInd K {i, j} * Mi = Mi * compInd K {i, j} := by
    calc compInd K {i, j} * Mi = (Mi * M) * compInd K {i, j} * Mi := by rw [h1', Matrix.one_mul]
      _ = Mi * (M * compInd K {i, j}) * Mi := by simp only [Matrix.mul_assoc]
      _ = Mi * (compInd K {i, j} * M) * Mi := by rw [hD]
      _ = Mi * compInd K {i, j} := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hMid : PairDiag i j Mi := pairDiag_of_commute hDi
  set P := pairBlk i j M with hP
  set Pi := pairBlk i j Mi with hPi
  have hPP : P * Pi = 1 := by rw [hP, hPi, ← pairBlk_mul hij hMd, h1, pairBlk_one i j hij]
  have htr : ∀ x ∈ uBlock p f K {i, j}, tr2 (P * pairBlk i j ((x : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * Pi * pairBlk i j (((x⁻¹ : StatedSU n (p ^ f) K) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 2 := by
    intro x hx
    set z := (⟨_, uConjSU_mem h D x⟩ : StatedSU n (p ^ f) K) * x⁻¹ with hz
    have hxd := pairDiag_of_mem_uBlock hx
    have hxid := pairDiag_of_mem_uBlock (inv_mem hx)
    have hzM : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        M * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Mi *
          (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [hz, Subgroup.coe_mul, Units.val_mul]
      rfl
    have hzd : PairDiag i j ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [hzM]
      exact pairDiag_mul (pairDiag_mul (pairDiag_mul hMd hxd) hMid) hxid
    have hblk : pairBlk i j ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        P * pairBlk i j ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pi *
          pairBlk i j (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by
      rw [hzM, pairBlk_mul hij (pairDiag_mul (pairDiag_mul hMd hxd) hMid),
        pairBlk_mul hij (pairDiag_mul hMd hxd), pairBlk_mul hij hMd]
    have hxx' : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    have hxx : pairBlk i j ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        pairBlk i j (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← pairBlk_mul hij hxd, hxx', pairBlk_one i j hij]
    have hdet : (pairBlk i j ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1 := by
      rw [hblk, det_mul, det_mul, det_mul]
      have e1 := congrArg Matrix.det hPP
      have e2 := congrArg Matrix.det hxx
      rw [det_mul, det_one] at e1 e2
      linear_combination (pairBlk i j ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det *
        (pairBlk i j (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)).det * e1 + e2
    have hzu := ((mem_unitarySU_iff h).1 z.2).2
    have hunit : ((pairBlk i j ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ *
        pairBlk i j ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← pairBlk_conjTr h, ← pairBlk_mul hij (pairDiag_conjTr h hzd), hzu,
        pairBlk_one i j hij]
    rw [← hblk]
    obtain ⟨k, hk⟩ := hodd x hx
    have hzm : z ^ (2 * k + 1) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one z
    refine trace_eq_two_of_odd_char3 h2 h3K hdet
      (mem_three_of_bar h h3 (bar_trace_of_unitary h hdet hunit)) ⟨k, rfl⟩ ?_
    rw [← pairBlk_pow hij hzd]
    have : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ (2 * k + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hzm, Subgroup.coe_one, Units.val_one]
    rw [this, pairBlk_one i j hij]
  have hιinv : ι⁻¹ = -ι := (eq_inv_of_mul_eq_one_right (by linear_combination -hι)).symm
  have hinv : ∀ {X Y Y₀ : Matrix (Fin 2) (Fin 2) K}, X * Y = 1 → Y₀ * X = 1 → Y = Y₀ := by
    intro X Y Y₀ e1 e2
    calc Y = (Y₀ * X) * Y := by rw [e2, Matrix.one_mul]
      _ = Y₀ := by rw [Matrix.mul_assoc, e1, Matrix.mul_one]
  have hxx : ∀ x ∈ uBlock p f K {i, j}, pairBlk i j ((x : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * pairBlk i j (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
    intro x hx
    rw [← pairBlk_mul hij (pairDiag_of_mem_uBlock hx), ← Units.val_mul, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, Units.val_one, pairBlk_one i j hij]
  set Q₁ := uDiag2 h hij hι0 hιN with hQ₁
  set Q₂ := uRot h hij with hQ₂
  have hQ₁m : Q₁ ∈ uBlock p f K {i, j} := uDiag2_mem_uBlock h hij (by simp) (by simp) hι0 hιN
  have hQ₂m : Q₂ ∈ uBlock p f K {i, j} := uRot_mem_uBlock h hij (by simp) (by simp)
  have hQ₃m : Q₁ * Q₂ ∈ uBlock p f K {i, j} := mul_mem hQ₁m hQ₂m
  have hB₁ : pairBlk i j ((Q₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = !![ι, 0; 0, -ι] := by
    rw [hQ₁, coe_uDiag2]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [pairBlk, hij, Ne.symm hij, hιinv]
  have hB₂ : pairBlk i j ((Q₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      !![(0 : K), 1; -1, 0] := by
    rw [hQ₂, coe_uRot]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [pairBlk, hij, Ne.symm hij, one_apply]
  have hB₃ : pairBlk i j (((Q₁ * Q₂ : StatedSU n (p ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = !![0, ι; ι, 0] := by
    rw [Subgroup.coe_mul, Units.val_mul, pairBlk_mul hij (pairDiag_of_mem_uBlock hQ₁m), hB₁, hB₂]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  have hI₁ := hinv (hxx _ hQ₁m) (Y₀ := !![-ι, 0; 0, ι]) (by
    rw [hB₁]; ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination -hι)
  have hI₂ := hinv (hxx _ hQ₂m) (Y₀ := !![(0 : K), -1; 1, 0]) (by
    rw [hB₂]; ext a b; fin_cases a <;> fin_cases b <;> simp)
  have hI₃ := hinv (hxx _ hQ₃m) (Y₀ := !![0, -ι; -ι, 0]) (by
    rw [hB₃]; ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination -hι)
  have ht1 := htr _ hQ₁m
  have ht2 := htr _ hQ₂m
  have ht3 := htr _ hQ₃m
  rw [hB₁, hI₁] at ht1
  rw [hB₂, hI₂] at ht2
  rw [hB₃, hI₃] at ht3
  obtain ⟨e1, e2, e3⟩ := scalar_of_commutator_traces_u hι h2 hPP ht1 ht2 ht3
  exact ⟨e1, e2, e3⟩

end CFSG.ComponentClassification.Burgoyne.U
