module

public import Certificates.Data.Kernel.F2Rank34.Defs

public section

namespace CFSG.KC.F2R34

open CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22 CFSG.Quasithin.H.Mathieu
  CFSG.CharacterTheory.SteinbergBY Matrix

@[expose] def bitF (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

@[expose] def vecF (n x : ℕ) : Fin n → ZMod 2 := fun j => bitF x j

theorem bitF_xor (a b j : ℕ) : bitF (a ^^^ b) j = bitF a j + bitF b j := by
  unfold bitF
  rw [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem bitF_two_pow (i j : ℕ) : bitF (2 ^ i) j = if i = j then 1 else 0 := by
  unfold bitF
  rw [Nat.testBit_two_pow]
  by_cases h : i = j <;> simp [h]

theorem xorSel_succ (m r : ℕ) (g : ℕ → ℕ) :
    xorSel (m + 1) r g = bif r.testBit m then xorSel m r g ^^^ g m else xorSel m r g := by
  simp only [xorSel, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bitF_xorSel (m r : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    bitF (xorSel m r g) j = ∑ l : Fin m, bitF r l * bitF (g l) j := by
  induction m with
  | zero => simp [xorSel, bitF]
  | succ m ih =>
    rw [xorSel_succ, Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← ih]
    cases hr : r.testBit m
    · have h0 : bitF r m = 0 := by simp [bitF, hr]
      simp only [cond_false, h0, zero_mul, add_zero]
    · have h1 : bitF r m = 1 := by simp [bitF, hr]
      simp only [cond_true, bitF_xor, h1, one_mul]

theorem bitF_kronRow (a b j₁ j₂ : ℕ) (h₁ : j₁ < 10) (h₂ : j₂ < 10) :
    bitF (kronRow a b) (10 * j₁ + j₂) = bitF a j₁ * bitF b j₂ := by
  rw [kronRow, bitF_xorSel, Finset.sum_eq_single (⟨j₁, h₁⟩ : Fin 10)]
  · congr 1
    unfold bitF
    rw [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    have e : 10 * j₁ + j₂ - 10 * j₁ = j₂ := by omega
    simp [e, h₂]
  · intro l _ hl
    have hl' : (l : ℕ) ≠ j₁ := fun e => hl (Fin.ext e)
    have hb : bitF ((b % 2 ^ 10) <<< (10 * (l : ℕ))) (10 * j₁ + j₂) = 0 := by
      unfold bitF
      rw [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
      rw [if_neg]
      intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc₁, hc₂, -⟩ := hc
      have hl₁ := l.2
      omega
    rw [hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem untab_decF2 (m n : ℕ) (R : List ℕ) (i : Fin m) (j : Fin n) :
    untab (decF2 m n R) i j = bitF (R.getD i 0) j := by
  simp [untab, decF2, bitF]

theorem vecF_xorSel (m n r : ℕ) (S : List ℕ) :
    vecF n (xorSel m r fun l => S.getD l 0) = vecF m r ᵥ* untab (decF2 m n S) := by
  funext j
  simp only [vecF, bitF_xorSel, vecMul, dotProduct, untab_decF2]

theorem vecF_xor (n a b : ℕ) : vecF n (a ^^^ b) = vecF n a + vecF n b := by
  funext j
  simp [vecF, bitF_xor]

theorem untab_kronTab_apply {m n : ℕ} (A : Vector (Vector (ZMod 2) m) m)
    (B : Vector (Vector (ZMod 2) n) n) (i j : Fin (m * n)) :
    untab (kronTab A B) i j = A[i.divNat][j.divNat] * B[i.modNat][j.modNat] := by
  simp [kronTab, untab]

theorem untab_kronTab_rows (tR : List ℕ) (t : Vector (Vector (ZMod 2) 10) 10)
    (ht : ∀ i j : Fin 10, t[i][j] = bitF (tR.getD i 0) j) (i j : Fin (10 * 10)) :
    untab (kronTab t t) i j = bitF (kronRow (tR.getD (i / 10) 0) (tR.getD (i % 10) 0)) j := by
  have hj : (j : ℕ) = 10 * ((j : ℕ) / 10) + (j : ℕ) % 10 := (Nat.div_add_mod _ _).symm
  have hk := bitF_kronRow (tR.getD (i / 10) 0) (tR.getD (i % 10) 0) (j / 10) (j % 10)
    (Nat.div_lt_of_lt_mul j.2) (Nat.mod_lt _ (by norm_num))
  rw [← hj] at hk
  rw [hk, untab_kronTab_apply, ht, ht]
  have e₁ : ((i.divNat : Fin 10) : ℕ) = i / 10 := rfl
  have e₂ : ((i.modNat : Fin 10) : ℕ) = i % 10 := rfl
  have e₃ : ((j.divNat : Fin 10) : ℕ) = j / 10 := rfl
  have e₄ : ((j.modNat : Fin 10) : ℕ) = j % 10 := rfl
  rw [e₁, e₂, e₃, e₄]

theorem vecF_xK (tR : List ℕ) (t : Vector (Vector (ZMod 2) 10) 10)
    (ht : ∀ i j : Fin 10, t[i][j] = bitF (tR.getD i 0) j) (x : ℕ) :
    vecF 100 (xK tR x) = vecF 100 x ᵥ* untab (kronTab t t) := by
  funext j
  simp only [vecF, xK, bitF_xorSel, vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [untab_kronTab_rows tR t ht i j]

theorem untab_subIdT {n : ℕ} (A : Vector (Vector (ZMod 2) n) n) :
    untab (subIdT A) = untab A - 1 := by
  ext i j
  simp [subIdT, untab, Matrix.one_apply, Vector.get_eq_getElem]

theorem untab_injective {m n : ℕ} {A B : Vector (Vector (ZMod 2) n) m}
    (h : untab A = untab B) : A = B := by
  refine Vector.ext fun i hi => Vector.ext fun j hj => ?_
  exact congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩

theorem vecF_rowF (h : Equiv.Perm (Fin 22)) (tR QR : List ℕ)
    (ht : ∀ i j : Fin 10, (maskTab 10 (actC10 (psiArr h)))[i][j] = bitF (tR.getD i 0) j)
    (r : ℕ) :
    vecF 24 (rowF tR QR r) =
      vecF 34 r ᵥ* ((untab (tab34P h) - 1) * untab (decF2 34 24 QR)) := by
  have key : ∀ (v : Fin 34 → ZMod 2) (M : Matrix (Fin 34) (Fin 34) (ZMod 2))
      (N : Matrix (Fin 34) (Fin 24) (ZMod 2)), (v ᵥ* M + v) ᵥ* N = v ᵥ* ((M - 1) * N) := by
    intro v M N
    rw [← Matrix.vecMul_vecMul, Matrix.vecMul_sub, Matrix.vecMul_one, CharTwo.sub_eq_add]
  rw [rowF, vecF_xorSel, vecF_xor, vecF_xorSel, vecF_xK _ _ ht, vecF_xorSel,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, key]
  simp only [tab34P, untab_mulT, P34, B34, Matrix.mul_assoc]

theorem check34_sound (h : Equiv.Perm (Fin 22)) (cols tR PR QR : List ℕ)
    (hc : check34 h cols tR PR QR = true) :
    mulT (mulT (decF2 24 34 PR) (subIdT (tab34P h))) (decF2 34 24 QR) = idT 24 := by
  simp only [check34, colsOK, trOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hc
  obtain ⟨⟨hcols, htr⟩, hrow⟩ := hc
  have ht : ∀ i j : Fin 10, (maskTab 10 (actC10 (psiArr h)))[i][j] = bitF (tR.getD i 0) j := by
    intro i j
    simp only [maskTab, Fin.getElem_fin, Vector.getElem_ofFn, bitF]
    rw [hcols j j.2, htr i i.2 j j.2]
  refine untab_injective ?_
  rw [untab_mulT, untab_mulT, untab_subIdT, untab_idT]
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]
  have hrow' : (untab (decF2 24 34 PR) i : Fin 34 → ZMod 2) = vecF 34 (PR.getD i 0) :=
    funext fun c => untab_decF2 _ _ _ _ _
  rw [hrow', ← vecF_rowF h tR QR ht, hrow i i.2]
  simp only [vecF, bitF_two_pow, Matrix.one_apply, Fin.ext_iff]

end CFSG.KC.F2R34
