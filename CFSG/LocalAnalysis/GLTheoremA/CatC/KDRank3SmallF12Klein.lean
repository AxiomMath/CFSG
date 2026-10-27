module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Klein

open Matrix Module CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Mat
  CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Core

variable {K : Type} [Field K]

theorem klein_core (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0)
    {g₁ g₂ k : Matrix (Fin 3) (Fin 3) K}
    (hg1 : g₁ * g₁ = 1) (hg2 : g₂ * g₂ = 1) (hd1 : g₁.det = 1) (hd2 : g₂.det = 1)
    (hg1ne : g₁ ≠ 1) (hg2ne : g₂ ≠ 1) (hne : g₁ ≠ g₂) (hcomm : g₁ * g₂ = g₂ * g₁)
    (hk3 : k ^ 3 = 1) (hk1 : k * g₁ = g₁ * k) (hk2 : k * g₂ = g₂ * k) : k = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hg1m : g₁ ≠ -1 := by
    intro h
    rw [h, Matrix.det_neg, Matrix.det_one] at hd1
    have : (2 : K) = 0 := by
      have h' := hd1
      norm_num at h'
      linear_combination -h'
    exact h2 this
  obtain ⟨Q, Qi, s, hQQi, hQiQ, hss, hQiBQ, hblk⟩ := frame_block hK hg1 hg1ne hg1m
  have hgen : ∀ y : Matrix (Fin 3) (Fin 3) K, Q * (Qi * y * Q) * Qi = y := fun y => by
    calc Q * (Qi * y * Q) * Qi = (Q * Qi) * y * (Q * Qi) := by simp only [mul_assoc]
      _ = y := by rw [hQQi, one_mul, mul_one]
  have hconj_mul : ∀ y z : Matrix (Fin 3) (Fin 3) K,
      (Qi * y * Q) * (Qi * z * Q) = Qi * (y * z) * Q := by
    intro y z
    calc (Qi * y * Q) * (Qi * z * Q) = Qi * y * (Q * Qi) * z * Q := by simp only [mul_assoc]
      _ = Qi * (y * z) * Q := by rw [hQQi]; simp only [mul_one, mul_assoc]
  have hconj_pow : ∀ (x : Matrix (Fin 3) (Fin 3) K) (n : ℕ),
      (Qi * x * Q) ^ (n + 1) = Qi * x ^ (n + 1) * Q := by
    intro x n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (Qi * x * Q) (k + 1), ih, hconj_mul, pow_succ x (k + 1)]
  have hX2blk : IsBlk (Qi * g₂ * Q) := hblk g₂ hcomm.symm
  have hX3blk : IsBlk (Qi * k * Q) := hblk k hk1
  have hX2sq : (Qi * g₂ * Q) * (Qi * g₂ * Q) = 1 := by
    rw [hconj_mul, hg2, mul_one, hQiQ]
  have hX3pow : (Qi * k * Q) ^ 3 = 1 := by
    calc (Qi * k * Q) ^ 3 = (Qi * k * Q) ^ (2 + 1) := rfl
      _ = Qi * k ^ (2 + 1) * Q := hconj_pow k 2
      _ = Qi * 1 * Q := by rw [show k ^ (2 + 1) = k ^ 3 from rfl, hk3]
      _ = 1 := by rw [mul_one, hQiQ]
  set X2 := Qi * g₂ * Q with hX2def
  set X3 := Qi * k * Q with hX3def
  have hdetX2 : X2.det = 1 := by
    have : X2.det = g₂.det := by
      rw [hX2def, Matrix.det_mul, Matrix.det_mul]
      have h := congrArg Matrix.det hQiQ
      rw [Matrix.det_mul, Matrix.det_one] at h
      linear_combination g₂.det * h
    rw [this, hd2]
  have hX3_00 : X3 0 0 = 1 := by
    apply eq_one_of_pow_three h3
    rw [← pow3_entry00 hX3blk, hX3pow]
    simp
  have hX2_00 : X2 0 0 * X2 0 0 = 1 := by
    have := congrFun (congrFun hX2sq 0) 0
    obtain ⟨x1, x2, x3, x4⟩ := hX2blk
    simpa [Matrix.mul_apply, Fin.sum_univ_three, x1, x2, x3, x4] using this
  have hG₂sq : blk X2 * blk X2 = 1 := by
    rw [← blk_mul hX2blk hX2blk, hX2sq, blk_one]
  have hG₂ne : blk X2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hG₂sq
    exact zero_ne_one hG₂sq
  have hdetG : X2 0 0 * (blk X2).det = 1 := by
    have h1 := det_of_isBlk hX2blk
    have h2' : (blk X2).det = X2 1 1 * X2 2 2 - X2 1 2 * X2 2 1 := by
      simp [blk, Matrix.det_fin_two]
    rw [h2', ← h1, hdetX2]
  by_cases hsc : ∃ c : K, blk X2 = c • (1 : Matrix (Fin 2) (Fin 2) K)
  ·
    obtain ⟨c, hc⟩ := hsc
    have hc2 : c * c = 1 := by
      have := congrFun (congrFun hG₂sq 0) 0
      rw [hc] at this
      simpa using this
    have hdetc : (blk X2).det = c * c := by
      rw [hc, Matrix.det_smul, Matrix.det_one]
      simp [sq]
    have hε : X2 0 0 = 1 := by
      rw [hdetc, hc2, mul_one] at hdetG
      exact hdetG
    have hcases : c = 1 ∨ c = -1 := by
      have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    rcases hcases with rfl | rfl
    ·
      have hX2one : X2 = 1 :=
        eq_of_isBlk hX2blk isBlk_one hε (by rw [hc, blk_one, one_smul])
      exfalso
      apply hg2ne
      have e := hgen g₂
      rw [← hX2def, hX2one, mul_one, hQQi] at e
      exact e.symm
    ·
      have hX2s : X2 = signD 1 := by
        apply eq_of_isBlk hX2blk (by
          obtain ⟨x1, x2, x3, x4⟩ : IsBlk (signD (1 : K)) := by
            refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [signD]
          exact ⟨x1, x2, x3, x4⟩)
        · simp [signD, hε]
        · rw [hc]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [blk, signD, Matrix.one_apply]
      have hsa : (s - 1) * (s + 1) = 0 := by linear_combination hss
      rcases mul_eq_zero.1 hsa with hs1 | hs1
      ·
        have hs' : s = 1 := by linear_combination hs1
        exfalso
        apply hne
        have e1 := hgen g₁
        rw [hQiBQ, hs'] at e1
        have e2 := hgen g₂
        rw [← hX2def, hX2s] at e2
        exact e1.symm.trans e2
      ·
        have hs' : s = -1 := by linear_combination hs1
        exfalso
        have hsig : signD s = -(signD 1) := by
          rw [hs']
          ext i j
          fin_cases i <;> fin_cases j <;> simp [signD, Matrix.diagonal_apply]
        have e1 := hgen g₁
        rw [hQiBQ, hsig] at e1
        have e2 := hgen g₂
        rw [← hX2def, hX2s] at e2
        have hg1eq : g₁ = -g₂ := by
          rw [← e1, ← e2]
          simp [mul_neg, neg_mul]
        have hprod : g₁ * g₂ = -1 := by rw [hg1eq, neg_mul, hg2]
        have hd := congrArg Matrix.det hprod
        rw [Matrix.det_mul, hd1, hd2, Matrix.det_neg, Matrix.det_one] at hd
        have : (2 : K) = 0 := by
          norm_num at hd
          linear_combination hd
        exact h2 this
  ·
    have hnon : (blk X2) 0 1 ≠ 0 ∨ (blk X2) 1 0 ≠ 0 ∨ (blk X2) 0 0 ≠ (blk X2) 1 1 := by
      by_contra hcon
      push Not at hcon
      apply hsc
      refine ⟨(blk X2) 0 0, ?_⟩
      obtain ⟨c1, c2, c3⟩ := hcon
      ext i j
      fin_cases i <;> fin_cases j <;> simp [c1, c2, c3]
    have hGtr : (blk X2) 0 0 + (blk X2) 1 1 = 0 := by
      have hC := cayley2 (blk X2)
      rw [hG₂sq] at hC
      by_contra ht
      apply hsc
      set G := blk X2 with hG
      set t := G 0 0 + G 1 1 with ht'
      set Dd := G 0 0 * G 1 1 - G 0 1 * G 1 0 with hDd
      have hC' : t • G = (1 + Dd) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        calc t • G = (t • G - Dd • (1 : Matrix (Fin 2) (Fin 2) K)) + Dd • 1 := by abel
          _ = 1 + Dd • 1 := by rw [← hC]
          _ = (1 + Dd) • 1 := by rw [add_smul, one_smul]
      refine ⟨t⁻¹ * (1 + Dd), ?_⟩
      calc G = t⁻¹ • (t • G) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • ((1 + Dd) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [hC']
        _ = (t⁻¹ * (1 + Dd)) • 1 := by rw [smul_smul]
    have hcommX : X2 * X3 = X3 * X2 := by
      rw [hX2def, hX3def, hconj_mul, hconj_mul, hk2]
    have hcommG : blk X2 * blk X3 = blk X3 * blk X2 := by
      have := congrArg blk hcommX
      rwa [blk_mul hX2blk hX3blk, blk_mul hX3blk hX2blk] at this
    have hNG : (blk X3 - 1) * blk X2 = blk X2 * (blk X3 - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hcommG]
    have hN3 : (blk X3 - 1) * (blk X3 - 1) * (blk X3 - 1) = 0 := by
      have hM := isBlk_sub_one hX3blk
      rw [← blk_sub_one, ← blk_cube hM, ← pow_three', sub_one_pow3 _ h3, hX3pow, sub_self,
        blk_zero]
    have hNtr : (blk X3 - 1) 0 0 + (blk X3 - 1) 1 1 = 0 := trace2_of_pow3_eq_zero hN3
    obtain ⟨β, hβ⟩ := comm_block_scalar h2 hG₂ne hGtr hNG hNtr
    have hβ0 : β = 0 := by
      have h3' := hN3
      rw [hβ] at h3'
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hG₂sq, Matrix.one_mul,
        Matrix.mul_one] at h3'
      have hb0 : β * (β * β) = 0 := (smul_eq_zero.1 h3').resolve_right hG₂ne
      have hb3 : β ^ 3 = 0 := by rw [show β ^ 3 = β * (β * β) by ring]; exact hb0
      exact pow_eq_zero_iff (by norm_num) |>.1 hb3
    have hN0 : blk X3 - 1 = 0 := by rw [hβ, hβ0, zero_smul]
    have hbX3 : blk X3 = blk 1 := by
      rw [blk_one]
      exact sub_eq_zero.1 hN0
    have hX3one : X3 = 1 := eq_of_isBlk hX3blk isBlk_one hX3_00 hbX3
    have e := hgen k
    rw [← hX3def, hX3one, mul_one, hQQi] at e
    exact e.symm

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Klein

end
