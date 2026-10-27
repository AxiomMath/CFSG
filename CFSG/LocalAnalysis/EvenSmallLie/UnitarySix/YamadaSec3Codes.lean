module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Data

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer CFSG.F4.Native Matrix

theorem codesOf_get (A : Matrix (Fin 6) (Fin 6) F4) (r c : Fin 6) :
    (codesOf A)[6 * r.val + c.val]! = (A r c).code.val := by
  have h : 6 * r.val + c.val < 36 := by omega
  rw [codesOf, getElem!_pos _ _ (by simpa using h), Array.getElem_ofFn]
  congr 3
  · apply Fin.ext; simp only; omega
  · apply Fin.ext; simp only; omega

theorem rowC_eq (A : Matrix (Fin 6) (Fin 6) F4) (w : Fin 6 → F4) (r : Fin 6) :
    rowC (codesOf A) (codeOf w) r.val = ((A *ᵥ w) r).code.val := by
  have e0 := codesOf_get A r 0
  have e1 := codesOf_get A r 1
  have e2 := codesOf_get A r 2
  have e3 := codesOf_get A r 3
  have e4 := codesOf_get A r 4
  have e5 := codesOf_get A r 5
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at e0 e1 e2 e3 e4 e5
  have e3' : (6 * r.val + 3) = 6 * r.val + ((3 : Fin 6) : ℕ) := rfl
  rw [rowC, mulVec, dotProduct, code_sum_six, code_mul, code_mul, code_mul, code_mul, code_mul,
    code_mul, e0, e1, e2, ← coord_codeOf w 0, ← coord_codeOf w 1, ← coord_codeOf w 2,
    ← coord_codeOf w 3, ← coord_codeOf w 4, ← coord_codeOf w 5]
  rw [show (6 * r.val + 3) = 6 * r.val + ((3 : Fin 6) : ℕ) from rfl, e3,
    show (6 * r.val + 4) = 6 * r.val + ((4 : Fin 6) : ℕ) from rfl, e4,
    show (6 * r.val + 5) = 6 * r.val + ((5 : Fin 6) : ℕ) from rfl, e5]
  rfl

theorem codeOf_mulVec (A : Matrix (Fin 6) (Fin 6) F4) (w : Fin 6 → F4) :
    codeOf (A *ᵥ w) = mulVecC (codesOf A) (codeOf w) := by
  rw [mulVecC, codeOf]
  rw [← rowC_eq A w 0, ← rowC_eq A w 1, ← rowC_eq A w 2, ← rowC_eq A w 3, ← rowC_eq A w 4,
    ← rowC_eq A w 5]
  rfl

theorem codesOf_Qm : codesOf Qm = qmCodes := by decide +kernel

theorem codesOf_Qim : codesOf Qim = qimCodes := by decide +kernel

theorem codesOf_yamMat0 : codesOf (yamMat 0) = yamCode0 := by decide +kernel

theorem codesOf_yamMat1 : codesOf (yamMat 1) = yamCode1 := by decide +kernel

theorem codesOf_yamMat2 : codesOf (yamMat 2) = yamCode2 := by decide +kernel

theorem codesOf_yamMat3 : codesOf (yamMat 3) = yamCode3 := by decide +kernel

theorem codesOf_yamMat4 : codesOf (yamMat 4) = yamCode4 := by decide +kernel

theorem codesOf_yamMat5 : codesOf (yamMat 5) = yamCode5 := by decide +kernel

theorem codesOf_yamMat6 : codesOf (yamMat 6) = yamCode6 := by decide +kernel

theorem codesOf_yamMat7 : codesOf (yamMat 7) = yamCode7 := by decide +kernel

theorem codesOf_yamMat8 : codesOf (yamMat 8) = yamCode8 := by decide +kernel

theorem codesOf_yamMat9 : codesOf (yamMat 9) = yamCode9 := by decide +kernel

theorem codesOf_yamMat10 : codesOf (yamMat 10) = yamCode10 := by decide +kernel

theorem codesOf_yamMat11 : codesOf (yamMat 11) = yamCode11 := by decide +kernel

theorem codesOf_yamMat12 : codesOf (yamMat 12) = yamCode12 := by decide +kernel

theorem codesOf_yamMat13 : codesOf (yamMat 13) = yamCode13 := by decide +kernel

theorem codesOf_yamMat14 : codesOf (yamMat 14) = yamCode14 := by decide +kernel

theorem codesOf_yamMat15 : codesOf (yamMat 15) = yamCode15 := by decide +kernel

theorem codesOf_yamMat16 : codesOf (yamMat 16) = yamCode16 := by decide +kernel

theorem codesOf_yamMat17 : codesOf (yamMat 17) = yamCode17 := by decide +kernel

theorem codesOf_yamMat {k : ℕ} (hk : k < 18) : codesOf (yamMat k) = yamCodes[k]! := by
  interval_cases k
  · exact codesOf_yamMat0
  · exact codesOf_yamMat1
  · exact codesOf_yamMat2
  · exact codesOf_yamMat3
  · exact codesOf_yamMat4
  · exact codesOf_yamMat5
  · exact codesOf_yamMat6
  · exact codesOf_yamMat7
  · exact codesOf_yamMat8
  · exact codesOf_yamMat9
  · exact codesOf_yamMat10
  · exact codesOf_yamMat11
  · exact codesOf_yamMat12
  · exact codesOf_yamMat13
  · exact codesOf_yamMat14
  · exact codesOf_yamMat15
  · exact codesOf_yamMat16
  · exact codesOf_yamMat17

theorem tabOfMat_eq_tabC (hP : PtsFacts) (M : Matrix (Fin 6) (Fin 6) F4) :
    tabOfMat M = tabC (codesOf M) := by
  have h : ∀ i : Fin 693, ptIdx ((Qm * M * Qim) *ᵥ uVec i.val) =
      uPts.toList.idxOf (normC (mulVecC qmCodes (mulVecC (codesOf M)
        (mulVecC qimCodes uPts[i.val]!)))) := by
    intro i
    rw [ptIdx, ← mulVec_mulVec, ← mulVec_mulVec, codeOf_mulVec, codeOf_mulVec, codeOf_mulVec,
      codeOf_uVec hP i.2, codesOf_Qm, codesOf_Qim]
  exact congrArg (Array.ofFn (n := 693)) (funext h)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
