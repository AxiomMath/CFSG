module

public import CFSG.LieType.SpecialLinear.TwoEnd.Radical
public import CFSG.LieType.SpecialLinear.EndNode.Radicals
public import CFSG.LieType.SpecialLinear.TwoEnd.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear

noncomputable section

section Coeffs

variable {m : ℕ} {F : Type} [Field F]

@[expose] def twoEndRowCoeff (G : Matrix (Fin (m+3)) (Fin (m+3)) F) : Fin (m+3) → F :=
  fun j => if j = 0 then 0 else if j = Fin.last (m+2) then
    G 0 (Fin.last (m+2)) -
      ∑ q ∈ Finset.univ.filter (fun q : Fin (m+3) => q ≠ 0 ∧ q ≠ Fin.last (m+2)),
        G 0 q * G q (Fin.last (m+2))
    else G 0 j

@[expose] def twoEndColCoeff (G : Matrix (Fin (m+3)) (Fin (m+3)) F) : Fin (m+3) → F :=
  fun i => if i = 0 then 0 else if i = Fin.last (m+2) then 0 else G i (Fin.last (m+2))

@[expose] def twoEndColCoeffLast (G : Matrix (Fin (m+3)) (Fin (m+3)) F) : Fin (m+3) → F :=
  fun i => if i = Fin.last (m+2) then 0 else G i (Fin.last (m+2))

@[expose] def twoEndRowCoeffLast (G : Matrix (Fin (m+3)) (Fin (m+3)) F) : Fin (m+3) → F :=
  fun j => if j = 0 then 0 else if j = Fin.last (m+2) then 0 else G 0 j

@[simp] theorem twoEndRowCoeff_zero (G : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    twoEndRowCoeff G 0 = 0 := by
  simp [twoEndRowCoeff]

@[simp] theorem twoEndColCoeff_zero (G : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    twoEndColCoeff G 0 = 0 := by
  simp [twoEndColCoeff]

@[simp] theorem twoEndColCoeff_last (G : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    twoEndColCoeff G (Fin.last (m+2)) = 0 := by
  simp [twoEndColCoeff]

@[simp] theorem twoEndColCoeffLast_last (G : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    twoEndColCoeffLast G (Fin.last (m+2)) = 0 := by
  simp [twoEndColCoeffLast]

@[simp] theorem twoEndRowCoeffLast_zero (G : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    twoEndRowCoeffLast G 0 = 0 := by
  simp [twoEndRowCoeffLast]

@[simp] theorem twoEndRowCoeffLast_last (G : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    twoEndRowCoeffLast G (Fin.last (m+2)) = 0 := by
  simp [twoEndRowCoeffLast]

theorem sum_twoEndRowCoeff_mul_twoEndColCoeff
    (G : Matrix (Fin (m+3)) (Fin (m+3)) F) :
    ∑ q, twoEndRowCoeff G q * twoEndColCoeff G q =
      ∑ q ∈ Finset.univ.filter (fun q : Fin (m+3) => q ≠ 0 ∧ q ≠ Fin.last (m+2)),
        G 0 q * G q (Fin.last (m+2)) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq0 : q = 0
  · simp [twoEndRowCoeff, twoEndColCoeff, hq0]
  · by_cases hql : q = Fin.last (m+2)
    · simp [twoEndRowCoeff, twoEndColCoeff, hql]
    · simp [twoEndRowCoeff, twoEndColCoeff, hq0, hql]

theorem apply_one_add_row_add_col (a b : Fin (m+3) → F) (i j : Fin (m+3)) :
    ((1 + rowSupportMat (n := m+2) a + colSupportMat (n := m+2) b +
        rowSupportMat (n := m+2) a * colSupportMat (n := m+2) b :
          Matrix (Fin (m+3)) (Fin (m+3)) F) i j) =
      (1 : Matrix (Fin (m+3)) (Fin (m+3)) F) i j + (if i = 0 then a j else 0) +
        (if j = Fin.last (m+2) then b i else 0) +
        (if i = 0 ∧ j = Fin.last (m+2) then ∑ q, a q * b q else 0) := by
  simp only [Matrix.add_apply, rowSupportMat_apply, colSupportMat_apply,
    rowSupportMat_mul_colSupportMat_apply]

end Coeffs

section Decomposition

variable {m : ℕ} {F : Type} [Field F]

theorem twoEndRowCoeff_of_ne {G : Matrix (Fin (m+3)) (Fin (m+3)) F} {j : Fin (m+3)}
    (hj0 : j ≠ 0) (hjl : j ≠ Fin.last (m+2)) : twoEndRowCoeff G j = G 0 j := by
  simp [twoEndRowCoeff, hj0, hjl]

theorem twoEndColCoeff_of_ne {G : Matrix (Fin (m+3)) (Fin (m+3)) F} {i : Fin (m+3)}
    (hi0 : i ≠ 0) (hil : i ≠ Fin.last (m+2)) :
    twoEndColCoeff G i = G i (Fin.last (m+2)) := by
  simp [twoEndColCoeff, hi0, hil]

theorem twoEnd_decomp_first {G : Matrix (Fin (m+3)) (Fin (m+3)) F}
    (hdiag : ∀ i, G i i = 1)
    (hoff : ∀ i j, i ≠ 0 → j ≠ Fin.last (m+2) →
      G i j = (1 : Matrix (Fin (m+3)) (Fin (m+3)) F) i j) :
    G = 1 + rowSupportMat (n := m+2) (twoEndRowCoeff G) +
        colSupportMat (n := m+2) (twoEndColCoeff G) +
        rowSupportMat (n := m+2) (twoEndRowCoeff G) *
          colSupportMat (n := m+2) (twoEndColCoeff G) := by
  ext i j
  rw [apply_one_add_row_add_col, sum_twoEndRowCoeff_mul_twoEndColCoeff]
  have hl0 : (Fin.last (m+2) : Fin (m+3)) ≠ 0 := by
    intro h
    have hv : m + 2 = 0 := by simpa using congrArg Fin.val h
    omega
  have hl0' : (0 : Fin (m+3)) ≠ Fin.last (m+2) := hl0.symm
  by_cases hi : i = 0
  · rw [hi]
    by_cases hj : j = 0
    · rw [hj, hdiag 0]
      simp [twoEndRowCoeff, hl0']
    · by_cases hjl : j = Fin.last (m+2)
      · rw [hjl]
        simp only [twoEndRowCoeff, twoEndColCoeff, Matrix.one_apply, hl0, hl0', if_false,
          if_true, zero_add, and_self]
        ring
      · rw [twoEndRowCoeff_of_ne hj hjl]
        simp [hj, hjl, eq_comm]
  · by_cases hil : i = Fin.last (m+2)
    · rw [hil]
      by_cases hj : j = Fin.last (m+2)
      · rw [hj, hdiag (Fin.last (m+2))]
        simp [twoEndColCoeff, hl0]
      · rw [hoff (Fin.last (m+2)) j (by simp) hj]
        simp [hj, hl0, eq_comm]
    · by_cases hj : j = Fin.last (m+2)
      · rw [hj, twoEndColCoeff_of_ne hi hil]
        simp [hi, hil]
      · rw [hoff i j hi hj]
        simp [hi, hj, Matrix.one_apply]

end Decomposition

section Factors

theorem upperUnit_rowSupportMat_mem_firstRow {m : ℕ} {F : Type} [Field F]
    {a : Fin (m+2) → F} (ha0 : a 0 = 0) :
    upperUnit (rowSupportMat (n := m+1) a) (rowSupportMat_isUpperTriangular ha0)
      (rowSupportMat_diag ha0) ∈ firstRowRadical m F := by
  change _ ∈ rowRadical m F 0
  rw [mem_rowRadical]
  refine ⟨?_, ?_⟩
  · simp [Matrix.add_apply, rowSupportMat_apply, ha0, Matrix.one_apply_eq]
  · intro i j hi
    simp [Matrix.add_apply, rowSupportMat_apply, hi]

theorem upperUnit_colSupportMat_mem_lastCol {m : ℕ} {F : Type} [Field F]
    {b : Fin (m+2) → F} (hbl : b (Fin.last (m+1)) = 0) :
    upperUnit (colSupportMat (n := m+1) b) (colSupportMat_isUpperTriangular hbl)
      (colSupportMat_diag hbl) ∈ lastColRadical m F := by
  change _ ∈ colRadical m F (Fin.last (m+1))
  rw [mem_colRadical]
  refine ⟨?_, ?_⟩
  · simp [Matrix.add_apply, colSupportMat_apply, hbl, Matrix.one_apply_eq]
  · intro i j hj
    simp [Matrix.add_apply, colSupportMat_apply, hj]

theorem upperUnit_colSupportMat_mem_map_embedSucc {m : ℕ} {F : Type} [Field F]
    {b : Fin (m+3) → F} (hb0 : b 0 = 0) (hbl : b (Fin.last (m+2)) = 0) :
    upperUnit (colSupportMat (n := m+2) b) (colSupportMat_isUpperTriangular hbl)
      (colSupportMat_diag hbl) ∈
      (lastColRadical m F).map (embedSucc (m+1) F) := by
  let b' : Fin (m+2) → F := fun j => b j.succ
  have hb'last : b' (Fin.last (m+1)) = 0 := hbl
  refine Subgroup.mem_map.mpr ⟨upperUnit (colSupportMat (n := m+1) b')
    (colSupportMat_isUpperTriangular hb'last) (colSupportMat_diag hb'last), ?_, ?_⟩
  · exact upperUnit_colSupportMat_mem_lastCol hb'last
  · apply Subtype.ext
    rw [coe_embedSucc, coe_upperUnit]
    exact (one_add_colSupportMat_eq_embedSucc (b := b) hb0 hbl).symm

end Factors

section Generation

variable (m : ℕ) (F : Type) [Field F]

theorem firstRowRadical_le_twoEndRadical :
    firstRowRadical (m+1) F ≤ twoEndRadical m F := by
  intro g hg
  rw [mem_twoEndRadical]
  change g ∈ rowRadical (m+1) F 0 at hg
  rw [mem_rowRadical] at hg
  refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
  · by_cases hi : i = 0
    · subst hi
      exact hg.1
    · rw [hg.2 i i hi, Matrix.one_apply_eq]
  · exact hg.2 i j hi

theorem lastColRadical_map_embedSucc_le_twoEndRadical :
    (lastColRadical m F).map (embedSucc (m+1) F) ≤ twoEndRadical m F := by
  rintro x ⟨h, hh, rfl⟩
  rw [mem_twoEndRadical]
  change h ∈ colRadical m F (Fin.last (m+1)) at hh
  rw [mem_colRadical] at hh
  refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [coe_embedSucc, embedSuccMat, fromBlocksFirst_apply_zero_zero]
      simp
    · rw [coe_embedSucc, embedSuccMat_apply_succ_succ]
      by_cases hi : i = Fin.last (m+1)
      · subst hi
        exact hh.1
      · rw [hh.2 i i hi, Matrix.one_apply_eq]
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · exact absurd rfl hi
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · rw [coe_embedSucc, embedSuccMat_apply_succ_zero, Matrix.one_apply_ne (by simp)]
      · rw [coe_embedSucc, embedSuccMat_apply_succ_succ]
        rw [hh.2 i j (by intro h; exact hj (by rw [h]; rfl))]
        simp [Matrix.one_apply, Fin.succ_inj]

theorem twoEndRadical_le_first_sup :
    twoEndRadical m F ≤
      firstRowRadical (m+1) F ⊔ (lastColRadical m F).map (embedSucc (m+1) F) := by
  intro g hg
  have hg' := (mem_twoEndRadical (m := m) (F := F)).mp hg
  let G : Matrix (Fin (m+3)) (Fin (m+3)) F := (g : Matrix (Fin (m+3)) (Fin (m+3)) F)
  have hmat : G = 1 + rowSupportMat (n := m+2) (twoEndRowCoeff G) +
      colSupportMat (n := m+2) (twoEndColCoeff G) +
      rowSupportMat (n := m+2) (twoEndRowCoeff G) *
        colSupportMat (n := m+2) (twoEndColCoeff G) :=
    twoEnd_decomp_first hg'.1 hg'.2
  have hr := upperUnit_rowSupportMat_mem_firstRow
    (a := twoEndRowCoeff G) (twoEndRowCoeff_zero G)
  have hC := upperUnit_colSupportMat_mem_map_embedSucc
    (b := twoEndColCoeff G) (twoEndColCoeff_zero G) (twoEndColCoeff_last G)
  have hprod : upperUnit (rowSupportMat (n := m+2) (twoEndRowCoeff G))
        (rowSupportMat_isUpperTriangular (twoEndRowCoeff_zero G))
        (rowSupportMat_diag (twoEndRowCoeff_zero G)) *
      upperUnit (colSupportMat (n := m+2) (twoEndColCoeff G))
        (colSupportMat_isUpperTriangular (twoEndColCoeff_last G))
        (colSupportMat_diag (twoEndColCoeff_last G)) = g := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_upperUnit, coe_upperUnit]
    change (1 + rowSupportMat (n := m+2) (twoEndRowCoeff G)) *
        (1 + colSupportMat (n := m+2) (twoEndColCoeff G)) = G
    conv_rhs => rw [hmat]
    noncomm_ring
  rw [← hprod]
  exact Subgroup.mul_mem_sup hr hC

theorem twoEndRadical_eq_first_sup :
    twoEndRadical m F =
      firstRowRadical (m+1) F ⊔ (lastColRadical m F).map (embedSucc (m+1) F) :=
  le_antisymm (twoEndRadical_le_first_sup m F)
    (sup_le (firstRowRadical_le_twoEndRadical m F)
      (lastColRadical_map_embedSucc_le_twoEndRadical m F))

end Generation

end

end CFSG.LieType.SpecialLinear
