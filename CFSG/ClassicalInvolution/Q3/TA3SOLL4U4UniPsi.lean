module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniPair
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUc

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open CFSG.ComponentClassification.CatFactsL4U4
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem pairD_eq_diagonal (l : K) :
    pairD l = diagonal (Sum.elim (fun _ : Fin 2 => l) (fun _ : Fin 2 => -l)) := by
  rw [pairD, smul_one_eq_diagonal, smul_one_eq_diagonal, fromBlocks_diagonal]

theorem exists_pairFrame {A : hypSU h 2 0} {l : K} {e g : Fin 2 → HypIndex 2 0 → K}
    (hAe : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e i =
      l • e i)
    (hAg : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g i =
      (-l) • g i)
    (hee : ∀ i j, hypForm h 2 0 (e i) (e j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g i) (g j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0) :
    PairFrame h ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) l
      (colMat (Sum.elim e g)) := by
  have hge : ∀ i j, hypForm h 2 0 (g i) (e j) = if i = j then 1 else 0 := fun i j => by
    rw [← (hypForm_isSymm h).eq (e j) (g i), heg]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hG : ((colMat (Sum.elim e g)).map h.bar)ᵀ * hypGram 2 0 K * colMat (Sum.elim e g) =
      pairGram K := by
    rw [gram_colMat_eq_hypForm]
    ext (i | i) (j | j) <;> simp [pairGram, hee, hgg, heg, hge, one_apply]
  have hFE : pairF h (colMat (Sum.elim e g)) * colMat (Sum.elim e g) = 1 := by
    rw [pairF, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (hypGram 2 0 K), hG,
      pairGram_mul_self]
  have hAE : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      colMat (Sum.elim e g) = colMat (Sum.elim e g) * pairD l := by
    rw [pairD_eq_diagonal]
    refine InvClassU.mul_colMat_of_eigen fun i => ?_
    rcases i with i | i
    · exact hAe i
    · exact hAg i
  have hGi : pairGram K * (((colMat (Sum.elim e g)).map h.bar)ᵀ * hypGram 2 0 K *
      colMat (Sum.elim e g)) = 1 := by rw [hG, pairGram_mul_self]
  have hGi' : (((colMat (Sum.elim e g)).map h.bar)ᵀ * hypGram 2 0 K *
      colMat (Sum.elim e g)) * pairGram K = 1 := by rw [hG, pairGram_mul_self]
  exact ⟨hG, InvClassU.mul_eq_one_comm_of_card (by simp) hFE, hAE,
    suppF_mul_of_isometry (mem_hypSU.mp A.2).1 hAE hGi hGi'⟩

theorem exists_smul_of_hypProj_comm {X Z : hypSU h 2 0}
    (hc : hypProj h 2 0 X * hypProj h 2 0 Z = hypProj h 2 0 Z * hypProj h 2 0 X) :
    ∃ c : K, ((X : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      ((Z : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      c • (((Z : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((X : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
  have h1 : hypProj h 2 0 (X * Z * (Z * X)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
  obtain ⟨c, hc'⟩ := (InvClassU.hypProj_eq_one_iff h _).mp h1
  refine ⟨c, ?_⟩
  have h2 : X * Z = X * Z * (Z * X)⁻¹ * (Z * X) := by group
  have h3 := congrArg (fun y : hypSU h 2 0 =>
    ((y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) h2
  simp only [Subgroup.coe_mul, Units.val_mul] at h3 hc'
  rw [h3, hc', Matrix.smul_mul, Matrix.one_mul]

variable {h} {A : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {l : K}
  {E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K}

theorem PairFrame.exists_psi (hE : PairFrame h A l E) :
    ∃ ψ : SL(2, K) →* hypSU h 2 0, ∀ B, ((ψ B : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = E * pairLevi h (B : Matrix (Fin 2) (Fin 2) K) *
        pairF h E := by
  have hGi : pairGram K * ((E.map h.bar)ᵀ * hypGram 2 0 K * E) = 1 := by
    rw [hE.gram, pairGram_mul_self]
  have hGi' : ((E.map h.bar)ᵀ * hypGram 2 0 K * E) * pairGram K = 1 := by
    rw [hE.gram, pairGram_mul_self]
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h hGi hGi' (pairHom h)
    (fun x => by rw [hE.gram]; exact pairHom_isometry h x) (det_pairHom h)
  refine ⟨ψ, fun B => ?_⟩
  rw [hψ B, pairHom_apply, suppMat, show pairGram K * (E.map h.bar)ᵀ * hypGram 2 0 K =
    pairF h E from rfl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hE.EF]
  abel

namespace PairFrame

variable (hE : PairFrame h A l E)

include hE

theorem ker_psi {ψ : SL(2, K) →* hypSU h 2 0}
    (hψ : ∀ B, ((ψ B : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      E * pairLevi h (B : Matrix (Fin 2) (Fin 2) K) * pairF h E) :
    ((hypProj h 2 0).comp ψ).ker = Subgroup.center SL(2, K) := by
  ext B
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, InvClassU.hypProj_eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff, hψ]
  constructor
  · rintro ⟨c, hc⟩
    have h1 := congrArg (pairFrm h E) hc
    rw [hE.frm_conj, pairFrm_smul, pairFrm, Matrix.mul_one, hE.FE] at h1
    have h2 := congrArg Matrix.toBlocks₁₁ h1
    rw [pairLevi, toBlocks_fromBlocks₁₁, ← fromBlocks_one, fromBlocks_smul,
      toBlocks_fromBlocks₁₁] at h2
    refine ⟨c, ?_, ?_⟩
    · have := B.2
      rw [h2, det_smul, det_one, mul_one, Fintype.card_fin] at this
      simpa using this
    · rw [h2, scalar_apply, smul_one_eq_diagonal]
  · rintro ⟨r, hr, hB⟩
    have hr1 : r = 1 ∨ r = -1 := by
      rw [Fintype.card_fin] at hr
      exact mul_self_eq_one_iff.mp (by rw [← sq]; exact hr)
    have hbar : h.bar r = r := by rcases hr1 with rfl | rfl <;> simp
    refine ⟨r, ?_⟩
    have hBm : (B : Matrix (Fin 2) (Fin 2) K) = r • 1 := by
      rw [← hB, scalar_apply, smul_one_eq_diagonal]
    have hLS : leviStar h (r • (1 : Matrix (Fin 2) (Fin 2) K)) = r • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [leviStar, adjugate_fin_two, hbar]
    have hL : pairLevi h (B : Matrix (Fin 2) (Fin 2) K) = r • 1 := by
      rw [pairLevi, hBm, hLS, ← fromBlocks_one, fromBlocks_smul, smul_zero]
    rw [hL, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hE.EF]

end PairFrame

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
