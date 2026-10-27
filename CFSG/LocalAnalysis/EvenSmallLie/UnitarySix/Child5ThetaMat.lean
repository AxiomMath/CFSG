module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5ThetaData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModel

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaD

theorem thetaCheck_parts :
    bmul 8 8 PBits PinvBits = id8 ∧ bmul 8 8 PinvBits PBits = id8 ∧
    (∀ j < 5, wordBits (wordA j) = cBits j) ∧ (∀ j < 5, bmul 8 8 (cBits j) (cBits j) = id8) ∧
    cWord (wordB 0) = genBits 0 ∧ cWord (wordB 1) = genBits 1 ∧
    (∀ m < 4, termsProd (eDec m) = eBits m) ∧
    (∀ j < 2, bmul 8 8 (termsProd (nuDec j).1) (cWord (nuDec j).2) = nuBits j) := by
  have h := thetaCheck_eq_true
  simp only [thetaCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem toMat_cBits (j : Fin 5) :
    toMat 8 8 (cBits j) = toMat 8 8 PBits * wedgeMatN j * toMat 8 8 PinvBits := by
  rw [cBits, toMat_bmul, toMat_bmul]
  rfl

theorem toMat_cWord_cons (j : ℕ) (w : List ℕ) :
    toMat 8 8 (cWord (j :: w)) = toMat 8 8 (cBits j) * toMat 8 8 (cWord w) := by
  rw [cWord, toMat_bmul]


theorem toMat_P_mul : toMat 8 8 PBits * toMat 8 8 PinvBits = 1 := by
  rw [← toMat_bmul, thetaCheck_parts.1, toMat_id8]

theorem toMat_Pinv_mul : toMat 8 8 PinvBits * toMat 8 8 PBits = 1 := by
  rw [← toMat_bmul, thetaCheck_parts.2.1, toMat_id8]

theorem coe_wordGL_wordA {j : ℕ} (hj : j < 5) :
    ((wordGL (wordA j) : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      toMat 8 8 (cBits j) := by
  rw [coe_wordGL, thetaCheck_parts.2.2.1 j hj]

theorem toMat_cBits_sq {j : ℕ} (hj : j < 5) : toMat 8 8 (cBits j) * toMat 8 8 (cBits j) = 1 := by
  rw [← toMat_bmul, thetaCheck_parts.2.2.2.1 j hj, toMat_id8]

theorem toMat_cWord_nil : toMat 8 8 (cWord []) = 1 := toMat_id8

theorem toMat_cWord_mul_reverse : ∀ w : List ℕ, (∀ j ∈ w, j < 5) →
    toMat 8 8 (cWord w) * toMat 8 8 (cWord w.reverse) = 1
  | [], _ => by rw [List.reverse_nil, toMat_cWord_nil, one_mul]
  | j :: w, hw => by
    have hcw : ∀ v : List ℕ, toMat 8 8 (cWord (v ++ [j])) =
        toMat 8 8 (cWord v) * toMat 8 8 (cBits j) := by
      intro v
      induction v with
      | nil => rw [List.nil_append, toMat_cWord_cons, toMat_cWord_nil, mul_one, one_mul]
      | cons i v ih => rw [List.cons_append, toMat_cWord_cons, ih, toMat_cWord_cons, mul_assoc]
    rw [List.reverse_cons, hcw, toMat_cWord_cons]
    have h1 := toMat_cWord_mul_reverse w fun i hi => hw i (List.mem_cons_of_mem j hi)
    calc toMat 8 8 (cBits j) * toMat 8 8 (cWord w) * (toMat 8 8 (cWord w.reverse) *
          toMat 8 8 (cBits j))
        = toMat 8 8 (cBits j) * (toMat 8 8 (cWord w) * toMat 8 8 (cWord w.reverse)) *
          toMat 8 8 (cBits j) := by simp only [mul_assoc]
      _ = 1 := by rw [h1, mul_one, toMat_cBits_sq (hw j List.mem_cons_self)]

end CFSG.EvenSmallLie.UnitarySix.Child5
