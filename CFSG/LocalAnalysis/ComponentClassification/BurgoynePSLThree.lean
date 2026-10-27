module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLBlocks
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem three_elements [Finite K] (h3 : Nat.card K = 3) (x : K) : x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 2 := ringChar.dvd (by exact_mod_cast h)
    have hp : (ringChar K).Prime := CharP.char_is_prime K _
    have hc2 : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
    obtain ⟨f, -, hcard⟩ := FiniteField.card K (ringChar K)
    rw [← Nat.card_eq_fintype_card, h3, hc2] at hcard
    have : Even (2 ^ (f : ℕ)) := (Nat.even_pow' f.ne_zero).2 even_two
    rw [← hcard] at this
    exact absurd this (by decide)
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  have h0m : (0 : K) ≠ -1 := by intro h; exact h01 (by linear_combination -h)
  have h1m : (1 : K) ≠ -1 := by intro h; exact h2 (by linear_combination h)
  have hcard : ({0, 1, -1} : Finset K).card = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, h3, Finset.card_insert_of_notMem (by simp [h01, h0m]),
      Finset.card_pair h1m]
  have huniv : ({0, 1, -1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hx : x ∈ ({0, 1, -1} : Finset K) := huniv ▸ Finset.mem_univ x
  simpa using hx

theorem two_eq_neg_one_of_three [Finite K] (h3 : Nat.card K = 3) : (2 : K) = -1 := by
  have : Fintype K := Fintype.ofFinite K
  have h3' : (3 : K) = 0 := by
    have := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, h3] at this
    exact_mod_cast this
  linear_combination h3'

theorem two_ne_zero_of_three [Finite K] (h3 : Nat.card K = 3) : (2 : K) ≠ 0 := by
  rw [two_eq_neg_one_of_three h3]
  exact neg_ne_zero.2 one_ne_zero

theorem sq_fin_two (z : Matrix (Fin 2) (Fin 2) K) :
    z * z = (z 0 0 + z 1 1) • z - z.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, det_fin_two, Matrix.sub_apply, one_apply] <;> ring

theorem trace_eq_two_of_odd [Finite K] (h3 : Nat.card K = 3) {z : Matrix (Fin 2) (Fin 2) K}
    (hdet : z.det = 1) {m : ℕ} (hm : Odd m) (hz : z ^ m = 1) : z 0 0 + z 1 1 = 2 := by
  have h2 := two_ne_zero_of_three h3
  have hCH := sq_fin_two z
  rw [hdet, one_smul] at hCH
  set t := z 0 0 + z 1 1 with ht
  obtain ⟨k, rfl⟩ := hm
  rcases three_elements h3 t with h | h | h
  ·
    exfalso
    rw [h, zero_smul, zero_sub] at hCH
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
    rw [h, one_smul] at hCH
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
      intro h1
      rw [h1] at ht
      simp at ht
      rw [ht] at h
      exact one_ne_zero (α := K) (by linear_combination h)
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
  · rw [h, two_eq_neg_one_of_three h3]

abbrev tr2 (z : Matrix (Fin 2) (Fin 2) K) : K := z 0 0 + z 1 1

theorem scalar_of_commutator_traces {P Pi : Matrix (Fin 2) (Fin 2) K} (h1 : P * Pi = 1)
    (ht1 : tr2 (P * !![(1 : K), 1; 0, 1] * Pi * !![(1 : K), -1; 0, 1]) = 2)
    (ht2 : tr2 (P * !![(1 : K), 0; 1, 1] * Pi * !![(1 : K), 0; -1, 1]) = 2)
    (ht3 : tr2 (P * !![(0 : K), 1; -1, 0] * Pi * !![(0 : K), -1; 1, 0]) = 2) :
    P 0 1 = 0 ∧ P 1 0 = 0 ∧ P 0 0 = P 1 1 := by
  have hdet : P.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hPi : Pi = P⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  rw [Matrix.inv_def, Ring.inverse_eq_inv'] at hPi
  subst hPi
  set p := P 0 0
  set q := P 0 1
  set r := P 1 0
  set s := P 1 1
  have hP : P = !![p, q; r, s] := Matrix.eta_fin_two P
  rw [hP, det_fin_two_of] at hdet
  rw [hP, adjugate_fin_two_of, det_fin_two_of] at ht1 ht2 ht3
  simp only [tr2, Matrix.mul_fin_two, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty,
    smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at ht1 ht2 ht3
  have hΔ : (p * s - q * r) * (p * s - q * r)⁻¹ = 1 := mul_inv_cancel₀ hdet
  have hr : r = 0 := by
    have e : r ^ 2 * (p * s - q * r)⁻¹ = 0 := by linear_combination ht1 - 2 * hΔ
    rcases mul_eq_zero.1 e with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    · exact absurd h (inv_ne_zero hdet)
  have hq : q = 0 := by
    have e : q ^ 2 * (p * s - q * r)⁻¹ = 0 := by linear_combination ht2 - 2 * hΔ
    rcases mul_eq_zero.1 e with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    · exact absurd h (inv_ne_zero hdet)
  rw [hr, hq] at ht3 hdet ⊢
  refine ⟨rfl, rfl, ?_⟩
  have hp0 : p ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hs0 : s ≠ 0 := fun h => hdet (by rw [h]; ring)
  field_simp at ht3
  have : (p - s) ^ 2 = 0 := by linear_combination ht3
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

@[expose] def pairBlk (i j : Fin n) (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin 2) (Fin 2) K :=
  !![A i i, A i j; A j i, A j j]

@[expose] def PairDiag (i j : Fin n) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k l, (k ∈ ({i, j} : Finset (Fin n)) ↔ l ∉ ({i, j} : Finset (Fin n))) → A k l = 0

theorem pairDiag_mul {i j : Fin n} {A B : Matrix (Fin n) (Fin n) K} (hA : PairDiag i j A)
    (hB : PairDiag i j B) : PairDiag i j (A * B) := by
  intro k l hkl
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hk : k ∈ ({i, j} : Finset (Fin n))
  · have hl := hkl.1 hk
    by_cases hm : m ∈ ({i, j} : Finset (Fin n))
    · rw [hB m l (iff_of_true hm hl), mul_zero]
    · rw [hA k m (iff_of_true hk hm), zero_mul]
  · have hl : l ∈ ({i, j} : Finset (Fin n)) := by
      by_contra hl
      exact hk (hkl.2 hl)
    by_cases hm : m ∈ ({i, j} : Finset (Fin n))
    · rw [hA k m (iff_of_false hk (not_not.2 hm)), zero_mul]
    · rw [hB m l (iff_of_false hm (not_not.2 hl)), mul_zero]

theorem pairDiag_one (i j : Fin n) : PairDiag i j (1 : Matrix (Fin n) (Fin n) K) := by
  intro k l hkl
  rw [one_apply]
  have : k ≠ l := by
    rintro rfl
    tauto
  simp [this]

theorem pairDiag_pow {i j : Fin n} {A : Matrix (Fin n) (Fin n) K} (hA : PairDiag i j A)
    (m : ℕ) : PairDiag i j (A ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact pairDiag_one i j
  | succ m ih => rw [pow_succ]; exact pairDiag_mul ih hA

theorem pairDiag_of_mem_coordBlock {i j : Fin n} {g : Matrix.SpecialLinearGroup (Fin n) K}
    (hg : g ∈ coordBlock K {i, j}) : PairDiag i j (g : Matrix (Fin n) (Fin n) K) := by
  intro k l hkl
  rw [(mem_coordBlock_iff.1 hg) k l (by tauto)]
  have : k ≠ l := by
    rintro rfl
    tauto
  simp [this]

theorem pairDiag_of_commute {i j : Fin n} {A : Matrix (Fin n) (Fin n) K}
    (h : compInd K {i, j} * A = A * compInd K {i, j}) : PairDiag i j A :=
  (commute_compInd_iff _ A).1 h

theorem pairBlk_mul {i j : Fin n} (hij : i ≠ j) {A B : Matrix (Fin n) (Fin n) K}
    (hA : PairDiag i j A) :
    pairBlk i j (A * B) = pairBlk i j A * pairBlk i j B := by
  have hsum : ∀ k l, k ∈ ({i, j} : Finset (Fin n)) → l ∈ ({i, j} : Finset (Fin n)) →
      (A * B) k l = A k i * B i l + A k j * B j l := by
    intro k l hk hl
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_add i j hij (fun c _ hc => ?_) (by simp) (by simp)
    have hc' : c ∉ ({i, j} : Finset (Fin n)) := by simp [hc.1, hc.2]
    rw [hA k c (iff_of_true hk hc'), zero_mul]
  have hi : i ∈ ({i, j} : Finset (Fin n)) := by simp
  have hj : j ∈ ({i, j} : Finset (Fin n)) := by simp
  rw [pairBlk, pairBlk, pairBlk, Matrix.mul_fin_two, hsum i i hi hi, hsum i j hi hj,
    hsum j i hj hi, hsum j j hj hj]

theorem pairBlk_one (i j : Fin n) (hij : i ≠ j) :
    pairBlk i j (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [pairBlk]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [one_apply, hij, hij.symm]

theorem pairBlk_pow {i j : Fin n} (hij : i ≠ j) {A : Matrix (Fin n) (Fin n) K}
    (hA : PairDiag i j A) (m : ℕ) : pairBlk i j (A ^ m) = pairBlk i j A ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pairBlk_one i j hij]
  | succ m ih => rw [pow_succ, pow_succ, pairBlk_mul hij (pairDiag_pow hA m), ih]

theorem pairBlk_transvection {i j : Fin n} (hij : i ≠ j) (c : K) :
    pairBlk i j ((Matrix.SpecialLinearGroup.transvection hij c :
      Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = !![1, c; 0, 1] := by
  rw [pairBlk, Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [one_apply, hij, hij.symm]

theorem pairBlk_transvection' {i j : Fin n} (hij : i ≠ j) (c : K) :
    pairBlk i j ((Matrix.SpecialLinearGroup.transvection hij.symm c :
      Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = !![1, 0; c, 1] := by
  rw [pairBlk, Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [one_apply, hij, hij.symm]

theorem three_block_commute [Finite K] (h3 : Nat.card K = 3) {i j : Fin n} (hij : i ≠ j)
    {D : GL (Fin n) K}
    (hD : compInd K {i, j} * (D : Matrix (Fin n) (Fin n) K) = D * compInd K {i, j})
    (hodd : ∀ x ∈ coordBlock K {i, j},
      Odd (orderOf (CatalogueBHigherLinearAction.slConjugation n K D x * x⁻¹))) :
    (D : Matrix (Fin n) (Fin n) K) * single i j 1 =
      single i j 1 * (D : Matrix (Fin n) (Fin n) K) := by
  set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hMdef
  set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMidef
  have h1 : M * Mi = 1 := by rw [hMdef, hMidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1' : Mi * M = 1 := by rw [hMdef, hMidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hM : PairDiag i j M := pairDiag_of_commute hD
  have hDi : compInd K {i, j} * Mi = Mi * compInd K {i, j} := by
    calc compInd K {i, j} * Mi = (Mi * M) * compInd K {i, j} * Mi := by rw [h1', Matrix.one_mul]
      _ = Mi * (M * compInd K {i, j}) * Mi := by simp only [Matrix.mul_assoc]
      _ = Mi * (compInd K {i, j} * M) * Mi := by rw [hD]
      _ = Mi * compInd K {i, j} := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hMi : PairDiag i j Mi := pairDiag_of_commute hDi
  set P := pairBlk i j M with hP
  set Pi := pairBlk i j Mi with hPi
  have hPP : P * Pi = 1 := by
    rw [hP, hPi, ← pairBlk_mul hij hM, h1, pairBlk_one i j hij]
  have htrace : ∀ x ∈ coordBlock K {i, j},
      tr2 (P * pairBlk i j x * Pi * pairBlk i j
        ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 2 := by
    intro x hx
    set z := CatalogueBHigherLinearAction.slConjugation n K D x * x⁻¹ with hz
    have hxd := pairDiag_of_mem_coordBlock hx
    have hxid := pairDiag_of_mem_coordBlock (inv_mem hx)
    have hzM : (z : Matrix (Fin n) (Fin n) K) =
        M * x * Mi * ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [hz, Matrix.SpecialLinearGroup.coe_mul, CatalogueBHigherLinearAction.slConjugation_matrix]
    have hzd : PairDiag i j (z : Matrix (Fin n) (Fin n) K) := by
      rw [hzM]
      exact pairDiag_mul (pairDiag_mul (pairDiag_mul hM hxd) hMi) hxid
    have hblk : pairBlk i j (z : Matrix (Fin n) (Fin n) K) = P * pairBlk i j x * Pi * pairBlk i j
        ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [hzM, pairBlk_mul hij (pairDiag_mul (pairDiag_mul hM hxd) hMi),
        pairBlk_mul hij (pairDiag_mul hM hxd), pairBlk_mul hij hM]
    have hxx : pairBlk i j x * pairBlk i j
        ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← pairBlk_mul hij hxd, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, pairBlk_one i j hij]
    have hdet : (pairBlk i j (z : Matrix (Fin n) (Fin n) K)).det = 1 := by
      rw [hblk, det_mul, det_mul, det_mul]
      have e1 := congrArg Matrix.det hPP
      have e2 := congrArg Matrix.det hxx
      rw [det_mul, det_one] at e1 e2
      linear_combination (pairBlk i j x).det * (pairBlk i j
        ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)).det * e1 + e2
    rw [← hblk]
    obtain ⟨k, hk⟩ := hodd x hx
    have hzm : z ^ (2 * k + 1) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one z
    refine trace_eq_two_of_odd h3 hdet ⟨k, rfl⟩ ?_
    rw [← pairBlk_pow hij hzd, ← Matrix.SpecialLinearGroup.coe_pow, hzm,
      Matrix.SpecialLinearGroup.coe_one, pairBlk_one i j hij]
  have hmem : ∀ {a b : Fin n} (hab : a ≠ b), a ∈ ({i, j} : Finset (Fin n)) →
      b ∈ ({i, j} : Finset (Fin n)) → ∀ c : K,
      Matrix.SpecialLinearGroup.transvection hab c ∈ coordBlock K {i, j} := by
    intro a b hab ha hb c
    rw [mem_coordBlock_iff]
    intro k l hkl
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply, single_apply]
    have : ¬ (a = k ∧ b = l) := by
      rintro ⟨rfl, rfl⟩
      tauto
    simp [this]
  have hi : i ∈ ({i, j} : Finset (Fin n)) := by simp
  have hj : j ∈ ({i, j} : Finset (Fin n)) := by simp
  set x₁ := Matrix.SpecialLinearGroup.transvection hij (1 : K) with hx₁
  set y₁ := Matrix.SpecialLinearGroup.transvection hij.symm (-1 : K) with hy₁
  have hx₁m := hmem hij hi hj 1
  have hy₁m := hmem hij.symm hj hi (-1)
  have hx₁i : x₁⁻¹ = Matrix.SpecialLinearGroup.transvection hij (-1 : K) :=
    Matrix.SpecialLinearGroup.transvection_inv hij 1
  have hy₁i : y₁⁻¹ = Matrix.SpecialLinearGroup.transvection hij.symm (1 : K) := by
    rw [hy₁, Matrix.SpecialLinearGroup.transvection_inv hij.symm (-1), neg_neg]
  have ht1 := htrace x₁ hx₁m
  have ht2 := htrace _ (hmem hij.symm hj hi 1)
  have ht3 := htrace (x₁ * y₁ * x₁) (mul_mem (mul_mem hx₁m hy₁m) hx₁m)
  rw [hx₁i, pairBlk_transvection hij 1, pairBlk_transvection hij (-1)] at ht1
  rw [Matrix.SpecialLinearGroup.transvection_inv hij.symm 1, pairBlk_transvection' hij 1,
    pairBlk_transvection' hij (-1)] at ht2
  have hblk3 : ∀ {g₁ g₂ g₃ : Matrix.SpecialLinearGroup (Fin n) K}, g₁ ∈ coordBlock K {i, j} →
      g₂ ∈ coordBlock K {i, j} →
      pairBlk i j ((g₁ * g₂ * g₃ : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = pairBlk i j g₁ * pairBlk i j g₂ * pairBlk i j g₃ := by
    intro g₁ g₂ g₃ h₁ h₂
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      pairBlk_mul hij
        (pairDiag_mul (pairDiag_of_mem_coordBlock h₁) (pairDiag_of_mem_coordBlock h₂)),
      pairBlk_mul hij (pairDiag_of_mem_coordBlock h₁)]
  have hinv3 : (x₁ * y₁ * x₁)⁻¹ = x₁⁻¹ * y₁⁻¹ * x₁⁻¹ := by group
  rw [hinv3, hblk3 hx₁m hy₁m, hblk3 (inv_mem hx₁m) (inv_mem hy₁m), hx₁i, hy₁i,
    pairBlk_transvection hij 1, pairBlk_transvection' hij (-1), pairBlk_transvection hij (-1),
    pairBlk_transvection' hij 1] at ht3
  have e3 : (!![(1 : K), 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1]) =
      !![(0 : K), 1; -1, 0] := by
    simp
  have e3' : (!![(1 : K), -1; 0, 1] * !![1, 0; 1, 1] * !![1, -1; 0, 1]) =
      !![(0 : K), -1; 1, 0] := by
    simp
  rw [e3, e3'] at ht3
  obtain ⟨hPij, hPji, hPd⟩ := scalar_of_commutator_traces hPP ht1 ht2 ht3
  simp only [hP, pairBlk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at hPij hPji hPd
  ext k l
  by_cases hl : l = j
  · subst hl
    rw [mul_single_apply_same, mul_one]
    by_cases hk : k = i
    · subst hk
      rw [single_mul_apply_same, one_mul, hPd]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hk]
      by_cases hkj : k = l
      · rw [hkj]
        exact hPji
      · exact hM k i (iff_of_false (by simp [hk, hkj]) (by simp))
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl]
    by_cases hk : k = i
    · subst hk
      rw [single_mul_apply_same, one_mul]
      by_cases hli : l = k
      · rw [hli]
        exact hPji.symm
      · exact (hM j l (iff_of_true (by simp) (by simp [hl, hli]))).symm
    · rw [single_mul_apply_of_ne _ _ _ _ _ hk]

end CFSG.ComponentClassification.Burgoyne.PSL