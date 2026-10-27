module

public import CFSG.LargeExtraspecial.SMod20Basic

public section

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6 Matrix
open scoped MatrixGroups
open CFSG.LargeExtraspecial.SMod20 (bit bit_and bit_foldl bit_xor)

@[expose] def dec6 (n : ℕ) : Fin 6 → ZMod 2 := fun i => if n.testBit i.val then 1 else 0

theorem dec6_apply (n : ℕ) (i : Fin 6) : dec6 n i = if n.testBit i.val then 1 else 0 := rfl

theorem dec6_zero : dec6 0 = 0 := by
  funext i
  simp [dec6_apply]

theorem dec6_xor (a b : ℕ) : dec6 (a ^^^ b) = dec6 a + dec6 b := by
  funext m
  simp only [dec6_apply, Pi.add_apply, Nat.testBit_xor]
  cases a.testBit m.val <;> cases b.testBit m.val <;> decide

theorem dec6_inj {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : dec6 a = dec6 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · have h1 := congrFun h ⟨i, hi⟩
    simp only [dec6_apply] at h1
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have h6 : (64 : ℕ) ≤ 2 ^ i := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h6),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h6)]

theorem dec6_surj (v : Fin 6 → ZMod 2) : ∃ n < 64, dec6 n = v := by
  have hf : Function.Injective (fun n : Fin 64 => dec6 n.val) := by
    intro m n hmn
    exact Fin.ext (dec6_inj m.isLt n.isLt hmn)
  have hcard : Fintype.card (Fin 64) = Fintype.card (Fin 6 → ZMod 2) := by
    simp [Fintype.card_fun, ZMod.card]
  obtain ⟨n, hn⟩ := ((Fintype.bijective_iff_injective_and_card
    (fun n : Fin 64 => dec6 n.val)).2 ⟨hf, hcard⟩).2 v
  exact ⟨n.val, n.isLt, hn⟩

theorem bit_form (φ x : ℕ) : bit (form φ x) = dec6 φ ⬝ᵥ dec6 x := by
  have key : ∀ y : ℕ, bit (par y) = ∑ k ∈ Finset.range 6, bit (y.testBit k) :=
    fun y => bit_foldl (fun k => y.testBit k) 6
  rw [show form φ x = par (φ &&& x) from rfl, key, dotProduct,
    ← Fin.sum_univ_eq_sum_range (fun k => bit ((φ &&& x).testBit k)) 6]
  refine Finset.sum_congr rfl fun i _ => ?_
  show bit ((φ &&& x).testBit i.val) = dec6 φ i * dec6 x i
  rw [Nat.testBit_and, bit_and]
  rfl

@[expose] def TvSet : Type :=
  {p : (Fin 6 → ZMod 2) × (Fin 6 → ZMod 2) // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ⬝ᵥ p.1 = 0}

@[expose] def tvVec (k : ℕ) : Fin 6 → ZMod 2 := dec6 (tvPair k).1

@[expose] def tvForm (k : ℕ) : Fin 6 → ZMod 2 := dec6 (tvPair k).2

theorem transvec_mulVec (v φ x : Fin 6 → ZMod 2) :
    (1 + vecMulVec v φ) *ᵥ x = x + (φ ⬝ᵥ x) • v := by
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec]
  funext i
  simp [mul_comm]

theorem vecMul_transvec (v φ y : Fin 6 → ZMod 2) :
    y ᵥ* (1 + vecMulVec v φ) = y + (y ⬝ᵥ v) • φ := by
  rw [vecMul_add, vecMul_one, vecMul_vecMulVec]

theorem transvec_mul_self {v φ : Fin 6 → ZMod 2} (h : φ ⬝ᵥ v = 0) :
    (1 + vecMulVec v φ) * (1 + vecMulVec v φ) = 1 := by
  have key3 : ∀ a : ZMod 2, a + a = 0 := by decide
  have hadd : vecMulVec v φ + vecMulVec v φ = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact key3 _
  have hsq : vecMulVec v φ * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, h, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  have e : (1 + vecMulVec v φ) * (1 + vecMulVec v φ)
      = 1 + (vecMulVec v φ + vecMulVec v φ) + vecMulVec v φ * vecMulVec v φ := by
    simp only [add_mul, mul_add, one_mul, mul_one, add_assoc]
  rw [e, hadd, hsq]
  simp

theorem det_transvec {v φ : Fin 6 → ZMod 2} (h : φ ⬝ᵥ v = 0) :
    (1 + vecMulVec v φ).det = 1 := by
  have h2 := congrArg Matrix.det (transvec_mul_self h)
  rw [Matrix.det_mul, Matrix.det_one] at h2
  have key : ∀ x : ZMod 2, x * x = 1 → x = 1 := by decide
  exact key _ h2

theorem conj_transvec (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hAB : A * B = 1)
    (v φ : Fin 6 → ZMod 2) :
    A * (1 + vecMulVec v φ) * B = 1 + vecMulVec (A *ᵥ v) (φ ᵥ* B) := by
  rw [mul_add, mul_one, add_mul, hAB, mul_vecMulVec, vecMulVec_mul]

theorem transvec_inj {v φ w ψ : Fin 6 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0)
    (h : 1 + vecMulVec v φ = 1 + vecMulVec w ψ) : v = w ∧ φ = ψ := by
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have key2 : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide
  have hN : vecMulVec v φ = vecMulVec w ψ := add_left_cancel h
  have hent : ∀ a b : Fin 6, v a * φ b = w a * ψ b := by
    intro a b
    have := congrFun (congrFun hN a) b
    simpa only [vecMulVec_apply] using this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hφ
  have hvi : v i = 1 := key _ hi
  have hφj : φ j = 1 := key _ hj
  have hwψ : w i * ψ j = 1 := by
    rw [← hent i j, hvi, hφj, mul_one]
  have hwi : w i = 1 := (key2 _ _ hwψ).1
  have hψj : ψ j = 1 := (key2 _ _ hwψ).2
  constructor
  · funext a
    have ha := hent a j
    rw [hφj, hψj, mul_one, mul_one] at ha
    exact ha
  · funext b
    have hb := hent i b
    rw [hvi, hwi, one_mul, one_mul] at hb
    exact hb

theorem eq_top_of_elementary (S : Subgroup SL(6, ZMod 2))
    (h : ∀ i j : Fin 6, ∀ hij : i ≠ j, SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ S) :
    S = ⊤ := by
  refine (Subgroup.eq_top_iff' S).mpr fun M => ?_
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun A => A ∈ S) M ?_ ?_ ?_
  ·
    intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) c hc
    subst hc1
    have hone : SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
      apply Subtype.ext
      ext k l
      by_cases hkl : k = l <;>
        simp [SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply, Matrix.one_apply, hkl]
    rw [hone]
    exact S.one_mem
  ·
    intro i j hij a
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a with rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero]
      exact S.one_mem
    · exact h i j hij
  · intro A B hA hB
    exact S.mul_mem hA hB

end CFSG.GF2Type.SmithTypeE.LMod
