module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeCheck

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

theorem codeVec_zero : codeVec 0 = 0 := by
  funext i
  simp [codeVec]

theorem codeVec_xor (a b : ℕ) : codeVec (a ^^^ b) = codeVec a + codeVec b := by
  funext i
  simp only [codeVec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> simp <;> decide

theorem codeVec_mod (c : ℕ) : codeVec (c % 2 ^ 10) = codeVec c := by
  funext i
  have hi : (i : ℕ) < 10 := i.2
  simp only [codeVec, Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]

theorem codeVec_xorCols (cols : Array ℕ) (c : ℕ) :
    ∀ (n : ℕ) (i : Fin 10), codeVec (xorCols cols c n) i =
      ∑ j ∈ Finset.range n, (if c.testBit j then codeVec cols[j]! i else 0)
  | 0, i => by simp [xorCols, codeVec_zero]
  | n + 1, i => by
    rw [xorCols, codeVec_xor, Pi.add_apply, codeVec_xorCols cols c n i, Finset.sum_range_succ]
    by_cases h : c.testBit n <;> simp [h, codeVec_zero]

theorem codeVec_applyCols (k : Fin 10) (c : ℕ) :
    codeVec (applyCols (actCols k) c) = (actMat k).mulVec (codeVec c) := by
  funext i
  rw [applyCols, codeVec_xorCols, Matrix.mulVec, dotProduct,
    ← Fin.sum_univ_eq_sum_range (fun j => if c.testBit j then codeVec (actCols k)[j]! i else 0) 10]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (actCols k)[(j : ℕ)]! = actCodes.getD (10 * k + j) 0 % 2 ^ 10 := by
    rw [actCols, getElem!_ofFn_arr _ j.2]
  rw [hj, codeVec_mod]
  by_cases hb : c.testBit j
  · simp [hb, actMat, actVec, actCode, codeVec]
  · simp [hb, actMat, actVec, actCode, codeVec]

theorem dotN_eq (m y : ℕ) :
    ∀ n : ℕ, (if dotN m y n then 1 else 0 : ZMod 2) =
      ∑ j ∈ Finset.range n, (if m.testBit j then 1 else 0) * (if y.testBit j then 1 else 0)
  | 0 => by simp [dotN]
  | n + 1 => by
    rw [Finset.sum_range_succ, ← dotN_eq m y n, dotN]
    by_cases h1 : m.testBit n <;> by_cases h2 : y.testBit n <;> by_cases h3 : dotN m y n <;>
      simp [h1, h2, h3] <;> decide

@[expose] def dotForm (m : ℕ) : (Fin 10 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i : Fin 10, codeVec m i * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem dotForm_codeVec (m y : ℕ) :
    dotForm m (codeVec y) = if dotM m y then 1 else 0 := by
  rw [dotM, dotN_eq, dotForm, LinearMap.coe_mk, AddHom.coe_mk,
    ← Fin.sum_univ_eq_sum_range (fun j => (if m.testBit j then 1 else 0) *
      (if y.testBit j then 1 else 0) : ℕ → ZMod 2) 10]
  rfl

theorem codeVec_injOn : Set.InjOn codeVec (Set.Iio 1024) := by
  intro a ha b hb h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · have h1 := congrFun h ⟨i, hi⟩
    simp only [codeVec] at h1
    by_cases h2 : a.testBit i <;> by_cases h3 : b.testBit i <;> simp_all
  · have h1 : a < 2 ^ i := lt_of_lt_of_le ha (by
      have : 2 ^ 10 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this)
    have h2 : b < 2 ^ i := lt_of_lt_of_le hb (by
      have : 2 ^ 10 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem exists_codeVec (v : Fin 10 → ZMod 2) : ∃ c < 1024, codeVec c = v := by
  have hmaps : ∀ c ∈ Finset.range 1024, codeVec c ∈ (Finset.univ : Finset (Fin 10 → ZMod 2)) :=
    fun _ _ => Finset.mem_univ _
  have hinj : Set.InjOn codeVec (Finset.range 1024 : Set ℕ) := by
    intro a ha b hb h
    exact codeVec_injOn (by simpa using ha) (by simpa using hb) h
  have hcard : (Finset.univ : Finset (Fin 10 → ZMod 2)).card ≤ (Finset.range 1024).card := by
    simp [Fintype.card_fun]
  obtain ⟨c, hc, hcv⟩ := Finset.surj_on_of_inj_on_of_card_le (fun c _ => codeVec c) hmaps
    (fun a b ha hb h => hinj ha hb h) hcard v (Finset.mem_univ _)
  exact ⟨c, by simpa using hc, hcv.symm⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
