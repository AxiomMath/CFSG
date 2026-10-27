module

public import CFSG.ClassicalGroups.SpecialLinear.Transitive
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type} [Field K]

@[expose] def crossMatrix (a : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, -a 2, a 1; a 2, 0, -a 0; -a 1, a 0, 0]

theorem mul_crossMatrix_mul_transpose (A : Matrix (Fin 3) (Fin 3) K) (a : Fin 3 → K) :
    A * crossMatrix a * Aᵀ = crossMatrix ((adjugate A)ᵀ *ᵥ a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMatrix, Matrix.mul_apply, Fin.sum_univ_three, adjugate_fin_three,
      Matrix.mulVec, dotProduct] <;> ring

theorem eq_crossMatrix {S : Matrix (Fin 3) (Fin 3) K} (hS : Sᵀ = -S) (hd : ∀ i, S i i = 0) :
    S = crossMatrix ![S 2 1, S 0 2, S 1 0] := by
  have hskew : ∀ i j, S j i = -S i j := fun i j => by
    have := congrFun (congrFun hS i) j
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMatrix, hd, hskew 1 0, hskew 2 0, hskew 2 1]

theorem crossMatrix_eq_zero_iff (a : Fin 3 → K) : crossMatrix a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congrFun (congrFun h 1) 2
    have h1 := congrFun (congrFun h 0) 2
    have h2 := congrFun (congrFun h 1) 0
    simp [crossMatrix] at h0 h1 h2
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [crossMatrix]

theorem mem_of_specialLinear_invariant (X : AddSubgroup (Matrix (Fin 3) (Fin 3) K))
    (hinv : ∀ A : SpecialLinearGroup (Fin 3) K, ∀ S ∈ X,
      (A : Matrix (Fin 3) (Fin 3) K) * S * (A : Matrix (Fin 3) (Fin 3) K)ᵀ ∈ X)
    {S₀ : Matrix (Fin 3) (Fin 3) K} (hS₀ : S₀ ∈ X) (hS₀t : S₀ᵀ = -S₀) (hS₀d : ∀ i, S₀ i i = 0)
    (hS₀ne : S₀ ≠ 0) {S : Matrix (Fin 3) (Fin 3) K} (hS : Sᵀ = -S) (hd : ∀ i, S i i = 0) :
    S ∈ X := by
  set a₀ : Fin 3 → K := ![S₀ 2 1, S₀ 0 2, S₀ 1 0]
  set a : Fin 3 → K := ![S 2 1, S 0 2, S 1 0]
  have hS₀eq : S₀ = crossMatrix a₀ := eq_crossMatrix hS₀t hS₀d
  have hSeq : S = crossMatrix a := eq_crossMatrix hS hd
  have ha₀ : a₀ ≠ 0 := fun h => hS₀ne (by rw [hS₀eq, h, (crossMatrix_eq_zero_iff 0).mpr rfl])
  by_cases ha : a = 0
  · rw [hSeq, ha, (crossMatrix_eq_zero_iff 0).mpr rfl]
    exact X.zero_mem
  obtain ⟨g, hg, hga⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq
    (by norm_num) ha₀ ha
  set gs := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm ⟨g, hg⟩
  have hgs : (gs : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) := by
    have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 K gs
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← hgs]
    exact gs.prop
  set Am : Matrix (Fin 3) (Fin 3) K := adjugate (g : Matrix (Fin 3) (Fin 3) K)ᵀ
  have hAdet : Am.det = 1 := by
    simp [Am, det_adjugate, det_transpose, hdet]
  have hadj : (adjugate Am)ᵀ = (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [adjugate_adjugate _ (by simp), det_transpose, hdet]
    simp
  have h := hinv ⟨Am, hAdet⟩ S₀ hS₀
  rw [show ((⟨Am, hAdet⟩ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Am from rfl,
    hS₀eq, mul_crossMatrix_mul_transpose, hadj, hga] at h
  rw [hSeq]
  exact h

private theorem exists_specialLinear_coe {g : GL (Fin 3) K}
    (hg : g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 K) :
    ∃ A : SpecialLinearGroup (Fin 3) K,
      (A : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨(CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm ⟨g, hg⟩, ?_⟩
  have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 K
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm ⟨g, hg⟩)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem eq_zero_of_forall_specialLinear_mulVec_eq {v : Fin 3 → K}
    (h : ∀ A : SpecialLinearGroup (Fin 3) K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) :
    v = 0 := by
  by_contra hv
  obtain ⟨w, hw0, hwv⟩ : ∃ w : Fin 3 → K, w ≠ 0 ∧ w ≠ v := by
    by_cases h0 : (Pi.single 0 1 : Fin 3 → K) = v
    · refine ⟨Pi.single 1 1, fun h1 => ?_, fun h1 => ?_⟩
      · simpa using congrFun h1 1
      · simpa using congrFun (h1.trans h0.symm) 1
    · exact ⟨Pi.single 0 1, fun h1 => by simpa using congrFun h1 0, h0⟩
  obtain ⟨g, hg, hgv⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq
    (by norm_num) hv hw0
  obtain ⟨A, hA⟩ := exists_specialLinear_coe hg
  have h1 := h A
  rw [hA, hgv] at h1
  exact hwv h1

theorem eq_bot_or_eq_top_of_specialLinear_invariant (S : AddSubgroup (Fin 3 → K))
    (hS : ∀ A : SpecialLinearGroup (Fin 3) K, ∀ s ∈ S,
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ s ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  refine Or.inr ((AddSubgroup.eq_top_iff' S).mpr fun w => ?_)
  obtain ⟨⟨s, hsS⟩, hs0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hbot
  have hs0' : s ≠ 0 := fun h => hs0 (Subtype.ext h)
  by_cases hw : w = 0
  · rw [hw]
    exact S.zero_mem
  obtain ⟨g, hg, hgs⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq
    (by norm_num) hs0' hw
  obtain ⟨A, hA⟩ := exists_specialLinear_coe hg
  have h1 := hS A s hsS
  rwa [hA, hgs] at h1

theorem exists_ne_zero_dotProduct_eq_zero (β : Fin 3 → K) :
    ∃ a : Fin 3 → K, a ≠ 0 ∧ a ⬝ᵥ β = 0 := by
  by_cases h0 : β 0 = 0
  · exact ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0, by simp [h0]⟩
  · refine ⟨![β 1, -β 0, 0], fun h => h0 (by simpa using congrFun h 1), ?_⟩
    simp [dotProduct, Fin.sum_univ_three] <;> ring

theorem one_add_vecMulVec_mul_crossMatrix (β l a : Fin 3 → K) :
    (1 + vecMulVec β l) * crossMatrix a * (1 + vecMulVec β l)ᵀ =
      crossMatrix (a - (β ⬝ᵥ a) • l) + (l ⬝ᵥ β) • crossMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMatrix, vecMulVec, Matrix.mul_apply, Fin.sum_univ_three, dotProduct,
      Matrix.one_apply] <;> ring

end CFSG.LinearAlgebra
