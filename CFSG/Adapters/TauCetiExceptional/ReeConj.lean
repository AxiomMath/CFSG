module

public import CFSG.Adapters.TauCetiExceptional.ReeTable
public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U TauCeti

variable {A : Type*} [CommRing A]

abbrev rootPointMat (k : Fin 2 ⊕ Fin 2) (t : A) : Matrix (Fin 7) (Fin 7) A :=
  ((G2ShortRoot.IntegralToralClosure.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
    Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)

theorem rootPointMat_eq (k : Fin 2 ⊕ Fin 2) (t : A) :
    rootPointMat k t = 1 + t • (tcE k).map (Int.cast : ℤ → A) +
      t ^ 2 • (tcE2 k).map (Int.cast : ℤ → A) := by
  rw [rootPointMat, G2ShortRoot.IntegralToralClosure.coe_rootSubgroupPoints, toAdd_ofAdd,
    rootMatrix_eq_tcE, rootDividedSquareMatrix_eq_tcE2]

theorem coe_rootPoint_inv (k : Fin 2 ⊕ Fin 2) (t : A) :
    (((G2ShortRoot.IntegralToralClosure.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) = rootPointMat k (-t) := by
  rw [rootPointMat, ofAdd_neg, map_inv, Subgroup.coe_inv]

theorem conj_expand_aux (t : A) (e f x : Matrix (Fin 7) (Fin 7) A) :
    (1 + t • e + t ^ 2 • f) * x * (1 + (-t) • e + (-t) ^ 2 • f) =
      x + t • (e * x - x * e) + t ^ 2 • (f * x - e * x * e + x * f) +
        t ^ 3 • (e * x * f - f * x * e) + t ^ 4 • (f * x * f) := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_add,
    smul_sub, smul_smul, Matrix.mul_assoc, neg_smul, mul_neg]
  module

theorem map_intCast_eq_mapMatrix (M : Matrix (Fin 7) (Fin 7) ℤ) :
    M.map (Int.cast : ℤ → A) = (Int.castRingHom A).mapMatrix M := by
  rw [RingHom.mapMatrix_apply, Int.coe_castRingHom]

theorem conj_expand (E E2 X : Matrix (Fin 7) (Fin 7) ℤ) (t : A) :
    (1 + t • E.map (Int.cast : ℤ → A) + t ^ 2 • E2.map (Int.cast : ℤ → A)) *
        X.map (Int.cast : ℤ → A) *
        (1 + (-t) • E.map (Int.cast : ℤ → A) + (-t) ^ 2 • E2.map (Int.cast : ℤ → A)) =
      ∑ j ∈ Finset.range 5, t ^ j • (conjCoeff E E2 X j).map (Int.cast : ℤ → A) := by
  simp only [map_intCast_eq_mapMatrix]
  rw [conj_expand_aux]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, conjCoeff, map_sub, map_add, map_mul,
    pow_zero, pow_one, one_smul, zero_add]

theorem colXc_four (i : Fin Tag.G2.rank) (b x : Label .G2) : colXc 4 i b x = 0 := by
  rcases b with l | α
  · simp [colXc]
  · have hle := su_le_three α.1 (mem_rootList_of_isRoot α.2) i
    simp only [colXc, show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide,
      show (4 : ℕ) ≠ 2 by decide, show ¬4 ≤ su i α.1 by omega, ite_false, ite_self]

theorem colYc_four (i : Fin Tag.G2.rank) (b x : Label .G2) : colYc 4 i b x = 0 := by
  rcases b with l | α
  · simp [colYc]
  · have hle := sd_le_three α.1 (mem_rootList_of_isRoot α.2) i
    simp only [colYc, show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide,
      show (4 : ℕ) ≠ 2 by decide, show ¬4 ≤ sd i α.1 by omega, ite_false, ite_self]

theorem map_sum_smul_basisMat (a : Fin 14 → ℤ) :
    (∑ u, a u • basisMat u).map (Int.cast : ℤ → A) = ∑ u, (a u : A) • basisMatR A u := by
  rw [map_intCast_eq_mapMatrix, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_zsmul, ← map_intCast_eq_mapMatrix, Int.cast_smul_eq_zsmul]

theorem conj_rootPoint_inl (i : Fin 2) (t : A) (s : Fin 14) :
    rootPointMat (.inl i) t * basisMatR A s * rootPointMat (.inl i) (-t) =
      ∑ u : Fin 14, colX A (nodeMap i) t (lab s) (lab u) • basisMatR A u := by
  rw [rootPointMat_eq, rootPointMat_eq, conj_expand]
  have h : ∀ j ∈ Finset.range 5, t ^ j •
      (conjCoeff (tcE (.inl i)) (tcE2 (.inl i)) (basisMat s) j).map (Int.cast : ℤ → A) =
        ∑ u, (t ^ j * (colXc j (nodeMap i) (lab s) (lab u) : A)) • basisMatR A u := by
    intro j hj
    rw [conjCoeff_inl i s ⟨j, Finset.mem_range.1 hj⟩, map_sum_smul_basisMat, Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_smul, colX_eq_sum, Finset.sum_range_succ _ 4, colXc_four, Int.cast_zero,
    mul_zero, add_zero]

theorem conj_rootPoint_inr (i : Fin 2) (t : A) (s : Fin 14) :
    rootPointMat (.inr i) t * basisMatR A s * rootPointMat (.inr i) (-t) =
      ∑ u : Fin 14, colY A (nodeMap i) t (lab s) (lab u) • basisMatR A u := by
  rw [rootPointMat_eq, rootPointMat_eq, conj_expand]
  have h : ∀ j ∈ Finset.range 5, t ^ j •
      (conjCoeff (tcE (.inr i)) (tcE2 (.inr i)) (basisMat s) j).map (Int.cast : ℤ → A) =
        ∑ u, (t ^ j * (colYc j (nodeMap i) (lab s) (lab u) : A)) • basisMatR A u := by
    intro j hj
    rw [conjCoeff_inr i s ⟨j, Finset.mem_range.1 hj⟩, map_sum_smul_basisMat, Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_smul, colY_eq_sum, Finset.sum_range_succ _ 4, colYc_four, Int.cast_zero,
    mul_zero, add_zero]

end CFSG.TauCetiBridge.Ree
