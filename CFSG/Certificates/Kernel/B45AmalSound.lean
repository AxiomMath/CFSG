module

public import Certificates.Data.Kernel.B45Ind.Amal
public import CFSG.Certificates.Kernel.B45IndSound
public import CFSG.Certificates.Kernel.F2Rank34.Sound

public section

namespace CFSG.KC.B45Ind

open CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.Ind CFSG.Quasithin.B45Mat.M22
  CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X3E CFSG.KC.F2R34
  CFSG.CharacterTheory.SteinbergBY Matrix

theorem psiArr_eq (g : Equiv.Perm (Fin 22)) : (psiArr g).toList = psiL g := by
  apply List.ext_getElem
  · simp [psiArr, psiL]
  · intro m h1 h2
    simp only [psiArr, psiL, Array.toList_ofFn, List.getElem_ofFn, List.getElem_map,
      List.getElem_range, get!_nat]

theorem rows10L_spec (a : List ℕ) (i j : Fin 10) :
    (maskTab 10 (actC10 a.toArray))[i][j] = bitF ((rows10L a).getD i 0) j := by
  simp only [maskTab, Fin.getElem_fin, Vector.getElem_ofFn, bitF, rows10L,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2, Option.map_some,
    Option.getD_some, ofBits_testBit, j.2, decide_true, Bool.true_and]

theorem vecF_two_pow_vecMul {n m : ℕ} (i : ℕ) (hi : i < n) (M : Matrix (Fin n) (Fin m) (ZMod 2)) :
    vecF n (2 ^ i) ᵥ* M = M ⟨i, hi⟩ := by
  funext j
  simp only [vecMul, dotProduct, vecF, bitF_two_pow]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · simp
  · intro l _ hl
    have hl' : i ≠ (l : ℕ) := fun e => hl (Fin.ext e.symm)
    simp [hl']
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem rows34L_spec (tR : List ℕ) (t : Vector (Vector (ZMod 2) 10) 10)
    (ht : ∀ i j : Fin 10, t[i][j] = bitF (tR.getD i 0) j) (i j : Fin 34) :
    untab (mulT (mulT P34 (kronTab t t)) B34) i j = bitF ((rows34L tR).getD i 0) j := by
  have hR : (rows34L tR).getD i 0 =
      xorSel 100 (xK tR (xorSel 34 (2 ^ (i : ℕ)) fun l => P34Rows.getD l 0))
        fun l => B34Rows.getD l 0 := by
    simp only [rows34L, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2,
      Option.map_some, Option.getD_some]
  have hv : vecF 34 ((rows34L tR).getD i 0) =
      vecF 34 (2 ^ (i : ℕ)) ᵥ* untab (mulT (mulT P34 (kronTab t t)) B34) := by
    rw [hR, vecF_xorSel, vecF_xK _ _ ht, vecF_xorSel, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
    simp only [untab_mulT, P34, B34, Matrix.mul_assoc]
  rw [vecF_two_pow_vecMul _ i.2] at hv
  exact (congrFun hv j).symm

theorem bitF_beq_one (x j : ℕ) : (bitF x j == 1) = x.testBit j := by
  unfold bitF
  cases x.testBit j <;> decide

theorem packCols_tab34P (p : Equiv.Perm (Fin 22)) : packCols (tab34P p) = cols34L p := by
  have ht : ∀ i j : Fin 10, (maskTab 10 (actC10 (psiArr p)))[i][j] =
      bitF ((rows10L (psiL p)).getD i 0) j := by
    intro i j
    have h := rows10L_spec (psiArr p).toList i j
    rwa [Array.toArray_toList, psiArr_eq] at h
  apply List.ext_getElem
  · simp [packCols, cols34L]
  · intro j h1 h2
    have hj : j < 34 := by simpa [cols34L] using h2
    simp only [packCols, cols34L, List.getElem_map, List.getElem_finRange, List.getElem_range]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [ofBits_testBit, ofBits_testBit]
    by_cases hi : i < 34
    · have h := rows34L_spec (rows10L (psiL p)) _ ht ⟨i, hi⟩ ⟨j, hj⟩
      rw [untab_apply] at h
      simp only [hi, decide_true, Bool.true_and, dif_pos, Fin.getElem_fin] at h ⊢
      change (tab34P p)[i][j] = _ at h
      simp only [Fin.coe_cast, h, bitF_beq_one]
    · simp [hi]

theorem packCols_tab34 (g : G22) : packCols (tab34 g) = cols34L (g : Equiv.Perm (Fin 22)) :=
  packCols_tab34P g

theorem beq_arr (a b : Array ℕ) : (a == b) = (a.toList == b.toList) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]

theorem amalRelOK_eq : amalRelOK = amalRelL := by
  simp only [amalRelOK, amalRelL, beq_arr, comp24_eq, wordArr_eq, psiArr_eq]

theorem amalOK_eq : amalOK = amalOKL := by
  simp only [amalOK, amalOKL, amalRelOK_eq, packCols_tab34]

end CFSG.KC.B45Ind
