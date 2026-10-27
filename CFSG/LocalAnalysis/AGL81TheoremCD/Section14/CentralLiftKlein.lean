module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftDefs
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open Matrix

section Conj

variable {G : Type*} [Group G]

theorem FixesKleinFour.conj {θ : MulAut G} (hθ : FixesKleinFour θ) (φ : MulAut G) :
    FixesKleinFour (φ * θ * φ⁻¹) := by
  obtain ⟨a, b, ha, hb, ha2, hb2, hab, ha1, hb1, hne⟩ := hθ
  refine ⟨φ a, φ b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, φ.injective.ne hne⟩
  · simp [MulAut.mul_apply, ha]
  · simp [MulAut.mul_apply, hb]
  · rw [← map_pow, ha2, map_one]
  · rw [← map_pow, hb2, map_one]
  · rw [← map_mul, ← map_mul, hab]
  · exact fun h1 => ha1 (φ.injective (h1.trans (map_one φ).symm))
  · exact fun h1 => hb1 (φ.injective (h1.trans (map_one φ).symm))

end Conj

section Signs

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def signMatA : Matrix (Fin 3) (Fin 3) K := diagonal ![1, -1, -1]

@[expose] def signMatB : Matrix (Fin 3) (Fin 3) K := diagonal ![-1, 1, -1]

theorem signMatA_mul_self : (signMatA : Matrix (Fin 3) (Fin 3) K) * signMatA = 1 := by
  rw [signMatA, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem signMatB_mul_self : (signMatB : Matrix (Fin 3) (Fin 3) K) * signMatB = 1 := by
  rw [signMatB, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[expose] def signGLA : GL (Fin 3) K := ⟨signMatA, signMatA, signMatA_mul_self, signMatA_mul_self⟩

@[expose] def signGLB : GL (Fin 3) K := ⟨signMatB, signMatB, signMatB_mul_self, signMatB_mul_self⟩

theorem map_diagonal_sign {F : Type*} [FunLike F K K] [RingHomClass F K K] {d : Fin 3 → K}
    (hd : ∀ i, d i = 1 ∨ d i = -1) (σ : F) :
    (diagonal d).map σ = diagonal d := by
  rw [diagonal_map (map_zero σ)]
  congr 1
  ext i
  rcases hd i with h1 | h1 <;> simp [h1]

theorem signMatA_entries (i : Fin 3) :
    (![1, -1, -1] : Fin 3 → K) i = 1 ∨ (![1, -1, -1] : Fin 3 → K) i = -1 := by
  fin_cases i <;> simp

theorem signMatB_entries (i : Fin 3) :
    (![-1, 1, -1] : Fin 3 → K) i = 1 ∨ (![-1, 1, -1] : Fin 3 → K) i = -1 := by
  fin_cases i <;> simp

theorem signGLA_mem (h : UnitaryFieldData p f K) : signGLA ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨by simp [signGLA, signMatA, Fin.prod_univ_three], ?_⟩
  change ((signMatA : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * signMatA = 1
  rw [signMatA, map_diagonal_sign signMatA_entries, diagonal_transpose, ← signMatA,
    signMatA_mul_self]

theorem signGLB_mem (h : UnitaryFieldData p f K) : signGLB ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨by simp [signGLB, signMatB, Fin.prod_univ_three], ?_⟩
  change ((signMatB : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * signMatB = 1
  rw [signMatB, map_diagonal_sign signMatB_entries, diagonal_transpose, ← signMatB,
    signMatB_mul_self]

@[expose] def kleinA (h : UnitaryFieldData p f K) : unitarySU p f K 3 := ⟨signGLA, signGLA_mem h⟩

@[expose] def kleinB (h : UnitaryFieldData p f K) : unitarySU p f K 3 := ⟨signGLB, signGLB_mem h⟩

variable (h : UnitaryFieldData p f K)

theorem coe_kleinA : (((kleinA h : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    signMatA := rfl

theorem coe_kleinB : (((kleinB h : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    signMatB := rfl

theorem kleinA_sq : kleinA h ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [pow_two, coe_kleinA, signMatA_mul_self]

theorem kleinB_sq : kleinB h ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [pow_two, coe_kleinB, signMatB_mul_self]

theorem kleinA_mul_kleinB : kleinA h * kleinB h = kleinB h * kleinA h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_kleinA, coe_kleinB, signMatA, signMatB,
    diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem entry_eq_of_eq {x y : unitarySU p f K 3} (hxy : x = y) (i : Fin 3) :
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i := by
  rw [hxy]

theorem kleinA_ne_one (h2 : (2 : K) ≠ 0) : kleinA h ≠ 1 := by
  intro h1
  have := entry_eq_of_eq h1 1
  simp only [coe_kleinA, signMatA, diagonal_apply_eq, OneMemClass.coe_one, Units.val_one,
    one_apply_eq, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at this
  exact h2 (by linear_combination -this)

theorem kleinB_ne_one (h2 : (2 : K) ≠ 0) : kleinB h ≠ 1 := by
  intro h1
  have := entry_eq_of_eq h1 0
  simp only [coe_kleinB, signMatB, diagonal_apply_eq, OneMemClass.coe_one, Units.val_one,
    one_apply_eq, Matrix.cons_val_zero] at this
  exact h2 (by linear_combination -this)

theorem kleinA_ne_kleinB (h2 : (2 : K) ≠ 0) : kleinA h ≠ kleinB h := by
  intro h1
  have := entry_eq_of_eq h1 0
  simp only [coe_kleinA, coe_kleinB, signMatA, signMatB, diagonal_apply_eq,
    Matrix.cons_val_zero] at this
  exact h2 (by linear_combination this)

theorem fixesKleinFour_of_fixes (h2 : (2 : K) ≠ 0) {θ : MulAut (unitarySU p f K 3)}
    (hA : θ (kleinA h) = kleinA h) (hB : θ (kleinB h) = kleinB h) : FixesKleinFour θ :=
  ⟨kleinA h, kleinB h, hA, hB, kleinA_sq h, kleinB_sq h, kleinA_mul_kleinB h, kleinA_ne_one h h2,
    kleinB_ne_one h h2, kleinA_ne_kleinB h h2⟩

theorem fixesKleinFour_suField (h2 : (2 : K) ≠ 0) (σ : K ≃+* K) :
    FixesKleinFour (suField h σ) := by
  refine fixesKleinFour_of_fixes h h2 (Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
  · rw [coe_suField, UnitaryHigher.coe_glAut, coe_kleinA, signMatA,
      map_diagonal_sign signMatA_entries σ]
  · rw [coe_suField, UnitaryHigher.coe_glAut, coe_kleinB, signMatB,
      map_diagonal_sign signMatB_entries σ]

theorem conj_diagonal_of_isDiag {D : GL (Fin 3) K} (hD : (D : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (d : Fin 3 → K) (g : GL (Fin 3) K) (hg : (g : Matrix (Fin 3) (Fin 3) K) = diagonal d) :
    D * g * D⁻¹ = g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, ← hD.diagonal_diag, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem fixesKleinFour_suConj_of_isDiag (h2 : (2 : K) ≠ 0) {D : unitaryIsom3 h}
    (hD : (((D : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    FixesKleinFour (suConj h D) := by
  refine fixesKleinFour_of_fixes h h2 (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [coe_suConj]
    exact conj_diagonal_of_isDiag hD _ _ (coe_kleinA h)
  · rw [coe_suConj]
    exact conj_diagonal_of_isDiag hD _ _ (coe_kleinB h)

end Signs

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
