module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Rot

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

open Matrix CFSG.SectionRank.ClassicalEven

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]

@[expose] def pairMatrix (i j : ι) (a b c d : K) : Matrix ι ι K :=
  Matrix.of fun r s =>
    if r = i then (if s = i then a else if s = j then b else 0)
    else if r = j then (if s = i then c else if s = j then d else 0)
    else if r = s then 1 else 0

theorem pairMatrix_mulVec_left {i j : ι} (a b c d : K) (hij : i ≠ j) :
    pairMatrix i j a b c d *ᵥ Pi.single i 1 = a • Pi.single i 1 + c • Pi.single j 1 := by
  rw [mulVec_single_one]
  ext r
  simp only [pairMatrix, col_apply, of_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]
  split_ifs <;> simp_all

theorem pairMatrix_mulVec_right {i j : ι} (a b c d : K) (hij : i ≠ j) :
    pairMatrix i j a b c d *ᵥ Pi.single j 1 = b • Pi.single i 1 + d • Pi.single j 1 := by
  rw [mulVec_single_one]
  ext r
  simp only [pairMatrix, col_apply, of_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]
  split_ifs <;> simp_all

theorem pairMatrix_mulVec_of_ne {i j t : ι} (a b c d : K) (hi : t ≠ i) (hj : t ≠ j) :
    pairMatrix i j a b c d *ᵥ Pi.single t 1 = Pi.single t 1 := by
  rw [mulVec_single_one]
  ext r
  simp only [pairMatrix, col_apply, of_apply, Pi.single_apply]
  split_ifs <;> simp_all

omit [Fintype ι] in
theorem pairMatrix_one (i j : ι) : pairMatrix i j (1 : K) 0 0 1 = 1 := by
  ext r s
  simp only [pairMatrix, of_apply, one_apply]
  split_ifs <;> simp_all

theorem pairMatrix_mul {i j : ι} (hij : i ≠ j) (a b c d a' b' c' d' : K) :
    pairMatrix i j a b c d * pairMatrix i j a' b' c' d' =
      pairMatrix i j (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  refine ext_of_mulVec_single fun t => ?_
  rw [← mulVec_mulVec]
  by_cases hti : t = i
  · subst hti
    rw [pairMatrix_mulVec_left _ _ _ _ hij, pairMatrix_mulVec_left _ _ _ _ hij, mulVec_add,
      mulVec_smul, mulVec_smul, pairMatrix_mulVec_left _ _ _ _ hij,
      pairMatrix_mulVec_right _ _ _ _ hij]
    module
  by_cases htj : t = j
  · subst htj
    rw [pairMatrix_mulVec_right _ _ _ _ hij, pairMatrix_mulVec_right _ _ _ _ hij, mulVec_add,
      mulVec_smul, mulVec_smul, pairMatrix_mulVec_left _ _ _ _ hij,
      pairMatrix_mulVec_right _ _ _ _ hij]
    module
  · rw [pairMatrix_mulVec_of_ne _ _ _ _ hti htj, pairMatrix_mulVec_of_ne _ _ _ _ hti htj,
      pairMatrix_mulVec_of_ne _ _ _ _ hti htj]

omit [Fintype ι] in
theorem pairMatrix_transpose {i j : ι} (_hij : i ≠ j) (a b c d : K) :
    (pairMatrix i j a b c d)ᵀ = pairMatrix i j a c b d := by
  ext r s
  simp only [transpose_apply, pairMatrix, of_apply]
  split_ifs <;> grind

omit [Fintype ι] in
theorem pairMatrix_map {i j : ι} {L : Type*} [CommRing L] (f : K → L) (hf0 : f 0 = 0)
    (hf1 : f 1 = 1) (a b c d : K) :
    (pairMatrix i j a b c d).map f = pairMatrix i j (f a) (f b) (f c) (f d) := by
  ext r s
  simp only [map_apply, pairMatrix, of_apply]
  split_ifs <;> simp [hf0, hf1]

theorem det_pairMatrix {i j : ι} (hij : i ≠ j) (a b c d : K) :
    (pairMatrix i j a b c d).det = a * d - b * c := by
  rw [det_eq_of_eq_one_off_pair hij]
  · simp [pairMatrix, hij.symm]
  · intro r hri hrj s
    simp [pairMatrix, one_apply, hri, hrj]

theorem pairMatrix_commute {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (a b c d a' b' c' d' : K) :
    Commute (pairMatrix i j a b c d) (pairMatrix k l a' b' c' d') := by
  refine ext_of_mulVec_single fun t => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  by_cases hti : t = i
  · subst hti
    rw [pairMatrix_mulVec_of_ne _ _ _ _ hik hil, pairMatrix_mulVec_left _ _ _ _ hij, mulVec_add,
      mulVec_smul, mulVec_smul, pairMatrix_mulVec_of_ne _ _ _ _ hik hil,
      pairMatrix_mulVec_of_ne _ _ _ _ hjk hjl]
  by_cases htj : t = j
  · subst htj
    rw [pairMatrix_mulVec_of_ne _ _ _ _ hjk hjl, pairMatrix_mulVec_right _ _ _ _ hij, mulVec_add,
      mulVec_smul, mulVec_smul, pairMatrix_mulVec_of_ne _ _ _ _ hik hil,
      pairMatrix_mulVec_of_ne _ _ _ _ hjk hjl]
  by_cases htk : t = k
  · subst htk
    rw [pairMatrix_mulVec_of_ne _ _ _ _ hti htj, pairMatrix_mulVec_left _ _ _ _ hkl, mulVec_add,
      mulVec_smul, mulVec_smul, pairMatrix_mulVec_of_ne _ _ _ _ (Ne.symm hik) (Ne.symm hjk),
      pairMatrix_mulVec_of_ne _ _ _ _ (Ne.symm hil) (Ne.symm hjl)]
  by_cases htl : t = l
  · subst htl
    rw [pairMatrix_mulVec_of_ne _ _ _ _ hti htj, pairMatrix_mulVec_right _ _ _ _ hkl, mulVec_add,
      mulVec_smul, mulVec_smul, pairMatrix_mulVec_of_ne _ _ _ _ (Ne.symm hil) (Ne.symm hjl),
      pairMatrix_mulVec_of_ne _ _ _ _ (Ne.symm hik) (Ne.symm hjk)]
  · simp only [pairMatrix_mulVec_of_ne _ _ _ _ htk htl, pairMatrix_mulVec_of_ne _ _ _ _ hti htj]

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls
