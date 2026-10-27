module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUc
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem exists_hyp_of_sq (hp2 : p ≠ 2) {W : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h W α) (hα1 : α ≠ 1)
    (hα2 : α ^ 2 = 1) {l₀ : K} (hl₀ : h.bar l₀ * l₀ = -1)
    (hWW : (W : Matrix (Fin 4) (Fin 4) K) * W = (l₀ ^ 2) • (1 : Matrix (Fin 4) (Fin 4) K)) :
    ∃ (l : K) (P : GL (Fin 4) K), h.bar l * l = -1 ∧
      uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG ∧
      (W : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l := by
  classical
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set Asq := toSesqU h hα.1 with hAsq
  have hA2 := orderOf_mk_toSesqU h hp2 hα hα1 hα2
  have hfin : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  obtain ⟨l, hl0, hAA, hN, hP, hM, hcompl, -, hpair, -, -, -, -, -, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2 (by omega)
      (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) (A := Asq) hA2
  set M := (W : Matrix (Fin 4) (Fin 4) K) with hMdef
  have hAv : ∀ v, unitaryOp Asq v = M *ᵥ v := fun v => rfl
  have hl2 : l ^ 2 = l₀ ^ 2 := by
    have e1 := congrArg (fun T : Module.End K (Fin 4 → K) => T (Pi.single 0 1)) hAA
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, hAv,
      Matrix.mulVec_mulVec, hWW, Matrix.smul_mulVec, Matrix.one_mulVec] at e1
    have e2 := congrFun e1 0
    simpa using e2.symm
  have hN1 : h.norm l = -1 := by
    rcases hN with hN1 | hN1
    · exfalso
      have hb : h.bar l * l = h.bar l₀ * l₀ := by
        have e : (l - l₀) * (l + l₀) = 0 := by linear_combination hl2
        rcases mul_eq_zero.1 e with e1 | e1
        · rw [sub_eq_zero.1 e1]
        · rw [eq_neg_of_add_eq_zero_left e1, map_neg]
          ring
      rw [UnitaryFieldData.norm] at hN1
      apply h2K
      linear_combination -hN1 + hb + hl₀
    · exact hN1
  have hdimP : 1 ≤ Module.finrank K (eigenPlus l (unitaryOp Asq)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hP
  have hdimM : 1 ≤ Module.finrank K (eigenMinus l (unitaryOp Asq)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hM
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hfin] at hsum
  obtain ⟨hisoP, hisoM, -, h2d, -, hpairM, -⟩ := hpair hN1
  rw [hfin] at h2d
  have hdP : Module.finrank K (eigenPlus l (unitaryOp Asq)) = 2 := by omega
  have hdM : Module.finrank K (eigenMinus l (unitaryOp Asq)) = 2 := by omega
  have heig1 : ∀ v ∈ eigenPlus l (unitaryOp Asq), M *ᵥ v = l • v := fun v hv => by
    rw [← hAv]; exact apply_eq_of_mem_eigenPlus hl0 hv
  have heig2 : ∀ w ∈ eigenMinus l (unitaryOp Asq), M *ᵥ w = -l • w := fun w hw => by
    rw [← hAv]; exact apply_eq_of_mem_eigenMinus hl0 hw
  obtain ⟨e, g', he, hg', hdual⟩ := exists_dual_pair h _ _ hdP hdM hpairM
  set col : Fin 4 → Fin 4 → K := ![e 0, e 1, g' 0, g' 1] with hcol
  set Q : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => col j i with hQ
  have hQcol : ∀ j, (fun k => Q k j) = col j := fun j => rfl
  have hQQ : uStar h Q * Q = stdG := by
    ext a b
    rw [uStar_mul_apply, hQcol, hQcol]
    have hge : ∀ a b, stdHermForm h 4 (g' a) (e b) = if a = b then 1 else 0 := by
      intro a b
      rw [← (stdHermForm_isSymm h 4).eq, hdual]
      by_cases hab : b = a
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    have hee : ∀ a b, stdHermForm h 4 (e a) (e b) = 0 := fun a b => hisoP _ (he a) _ (he b)
    have hgg : ∀ a b, stdHermForm h 4 (g' a) (g' b) = 0 := fun a b =>
      hisoM _ (hg' a) _ (hg' b)
    fin_cases a <;> fin_cases b <;> simp [hcol, stdG, hdual, hge, hee, hgg]
  have hMQ : M * Q = Q * X1 l := by
    rw [X1_eq_stdDl]
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change (M *ᵥ col j) i = _
    fin_cases j <;> simp [hcol, stdDl, hQ, heig1 _ (he _), heig2 _ (hg' _),
      Matrix.diagonal_apply, mul_comm]
  have hdet : Q.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hQQ
    have hs' : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
    rw [det_mul, h0, mul_zero, hs'] at this
    exact zero_ne_one this
  refine ⟨l, GeneralLinearGroup.mkOfDetNeZero Q hdet, ?_, ?_, ?_⟩
  · rw [UnitaryFieldData.norm] at hN1
    rw [mul_comm]
    exact hN1
  · rw [GeneralLinearGroup.val_mkOfDetNeZero]
    exact hQQ
  · rw [GeneralLinearGroup.val_mkOfDetNeZero]
    exact hMQ

end OFU

end CFSG.ComponentClassification.CatFactsL4U4
