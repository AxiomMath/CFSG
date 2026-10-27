module

public import CFSG.ClassicalInvolution.Asc77.AscC25X6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

namespace C25X

section Matrix

variable {F : Type} [Field F]

@[expose] noncomputable def diagSL4 (a b c d : F) (h : a * b * c * d = 1) : SL(4, F) :=
  ⟨Matrix.diagonal ![a, b, c, d], by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]; simpa using h⟩

theorem coe_diagSL4 (a b c d : F) (h : a * b * c * d = 1) :
    ((diagSL4 a b c d h : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![a, b, c, d] :=
  rfl

theorem zMat_pair01 : zMat F 4 ({0, 1} : Finset (Fin 4)) = Matrix.diagonal ![-1, -1, 1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [zMat]

theorem zMat_pair02 : zMat F 4 ({0, 2} : Finset (Fin 4)) = Matrix.diagonal ![-1, 1, -1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [zMat]

theorem nc4_sl4_matrix (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    ∃ R₁ ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num),
      ∃ R₂ ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num), ∃ y ∈ R₁, ∃ x₂ ∈ R₂,
        y * y * y * y = 1 ∧ y * y ≠ 1 ∧ x₂ * x₂ = 1 ∧ x₂ ≠ 1 ∧ x₂ * y = y * x₂ ∧
          (y * y) * x₂ ∉ Subgroup.center SL(4, F) := by
  let T₁ : Pair 4 := ⟨{0, 1}, by decide⟩
  let T₂ : Pair 4 := ⟨{0, 2}, by decide⟩
  have hy1 : i * -i * 1 * 1 = 1 := by linear_combination -hi
  have hm1 : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hi4 : i * i * i * i = 1 := by linear_combination (i * i - 1) * hi
  have hx2c : ((zElt F T₂ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![-1, 1, -1, 1] := zMat_pair02
  refine ⟨Lc F T₁, Lc_mem_longRootSet h2 (by norm_num) T₁, Lc F T₂,
    Lc_mem_longRootSet h2 (by norm_num) T₂, diagSL4 i (-i) 1 1 hy1, ?_, zElt F T₂, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_Lc]
    show _ ∧ _
    rw [coe_diagSL4]
    show Matrix.diagonal ![i, -i, 1, 1] * zMat F 4 ({0, 1} : Finset (Fin 4)) = _ ∧ _
    rw [zMat_pair01]
    constructor
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · rw [mem_Lc]
    refine ⟨rfl, ?_⟩
    rw [Matrix.mul_add, Matrix.mul_one]
    show zMat F 4 T₂.1 + zMat F 4 T₂.1 * zMat F 4 T₂.1 = _
    rw [zMat_mul_self, add_comm]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_diagSL4, Matrix.SpecialLinearGroup.coe_one]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, hi4]
  · intro h
    have h' := congrArg (fun m : SL(4, F) => (m : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL4, Matrix.mul_apply,
      Matrix.diagonal_apply] at h'
    exact hm1 (by rw [← hi]; exact h')
  · exact zElt_mul_self T₂
  · intro h
    have h' := congrArg (fun m : SL(4, F) => (m : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp only [hx2c, Matrix.SpecialLinearGroup.coe_one] at h'
    simp at h'
    exact hm1 h'
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx2c,
      coe_diagSL4]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · intro h
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
    obtain ⟨r, -, hr⟩ := h
    have h00 := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 0 0) hr
    have h11 := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 1 1) hr
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL4, hx2c, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.scalar_apply] at h00 h11
    have h3 : (2 : F) * (i * i) = 0 := by linear_combination h00 - h11
    rw [hi] at h3
    exact h2 (by linear_combination -h3)

end Matrix

section Row

variable (p : ℕ) [Fact p.Prime]

theorem nc4SL : NC4SL p := by
  intro e hadm hp2 hq h4
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  obtain ⟨i, hi⟩ : ∃ i : GaloisField p e, i * i = -1 := by
    have : Fintype (GaloisField p e) := Fintype.ofFinite _
    have hc : Fintype.card (GaloisField p e) = p ^ e := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p e he
    have : IsSquare (-1 : GaloisField p e) := by
      rw [FiniteField.isSquare_neg_one_iff, hc]
      omega
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi.symm⟩
  obtain ⟨R₁, hR₁, R₂, hR₂, y, hy, x₂, hx₂, h1, h2', h3, h4', h5, h6⟩ := nc4_sl4_matrix h2 hi
  exact ⟨R₁, longRootSet_subset_fundamentalSubgroups_psl (m := 3) (by norm_num) hR₁, R₂,
    longRootSet_subset_fundamentalSubgroups_psl (m := 3) (by norm_num) hR₂, y, hy, x₂, hx₂, h1,
    h2', h3, h4', h5, h6⟩

end Row

end C25X

end CFSG.ClassicalInvolution.Asc77
