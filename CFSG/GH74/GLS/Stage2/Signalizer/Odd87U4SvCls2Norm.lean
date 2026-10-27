module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2Frame
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open scoped MatrixGroups commutatorElement

section Norm

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def pairVecs (e g : Fin 2 → HypIndex 2 0 → K) : HypIndex 2 0 → HypIndex 2 0 → K :=
  Sum.elim e (Sum.elim (fun k : Fin 0 => (k.elim0 : HypIndex 2 0 → K)) g)

theorem pairMat_isometry (h : UnitaryFieldData p f K) {e g : Fin 2 → HypIndex 2 0 → K}
    (hee : ∀ i j, hypForm h 2 0 (e i) (e j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g i) (g j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0) :
    ((colMat (pairVecs e g)).map h.bar)ᵀ * hypGram 2 0 K * colMat (pairVecs e g) =
      hypGram 2 0 K := by
  have hge : ∀ i j, hypForm h 2 0 (g i) (e j) = if i = j then 1 else 0 := fun i j => by
    rw [← (hypForm_isSymm h).eq (e j) (g i), heg]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [gram_colMat_eq_hypForm]
  ext a b
  rcases a with i | k | i <;> rcases b with j | k' | j
  · simp [pairVecs, hee]
  · exact k'.elim0
  · simp [pairVecs, heg]
  · exact k.elim0
  · exact k.elim0
  · exact k.elim0
  · simp [pairVecs, hge]
  · exact k'.elim0
  · simp [pairVecs, hgg]

theorem det_pairMat_ne_zero (h : UnitaryFieldData p f K) {e g : Fin 2 → HypIndex 2 0 → K}
    (hee : ∀ i j, hypForm h 2 0 (e i) (e j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g i) (g j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0) :
    (colMat (pairVecs e g)).det ≠ 0 := by
  intro hd
  have := congrArg Matrix.det (pairMat_isometry h hee hgg heg)
  rw [det_mul, det_mul, hd, mul_zero] at this
  exact det_hypGram_ne_zero this.symm

theorem A_mul_pairMat (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (l : K)
    {e g : Fin 2 → HypIndex 2 0 → K} (hAe : ∀ i, A *ᵥ e i = l • e i)
    (hAg : ∀ i, A *ᵥ g i = (-l) • g i) :
    A * colMat (pairVecs e g) = colMat (pairVecs e g) * a0Mat l := by
  rw [a0Mat]
  ext a b
  rw [mul_diagonal]
  change (A *ᵥ pairVecs e g b) a = _
  rcases b with j | k | j
  · simp [pairVecs, hAe, colMat, dSign, mul_comm]
  · exact k.elim0
  · simp [pairVecs, hAg, colMat, dSign, mul_comm]

theorem exists_normal_form_u4 (h : UnitaryFieldData p f K) (hp : p ≠ 2) {A : GL (HypIndex 2 0) K}
    (hA : A ∈ hypUnitary h 2 0) {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = -1) :
    ∃ P : ↥(hypUnitary h 2 0),
      hypPhi h (a0U h hl0 hN) = hypPhi h P * hypPhi h ⟨A, hA⟩ * (hypPhi h P)⁻¹ := by
  obtain ⟨e, g, hAe, hAg, hee, hgg, heg⟩ :=
    exists_paired_eigen_basis h hp (by norm_num) hA hl0 hAA hN
  have hdet := det_pairMat_ne_zero h hee hgg heg
  let Pu : ↥(hypUnitary h 2 0) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (colMat (pairVecs e g)) hdet,
      pairMat_isometry h hee hgg heg⟩
  refine ⟨Pu⁻¹, ?_⟩
  have hrel : (⟨A, hA⟩ : ↥(hypUnitary h 2 0)) * Pu = Pu * a0U h hl0 hN :=
    Subtype.ext (Units.ext (A_mul_pairMat _ l hAe hAg))
  have h2 : a0U h hl0 hN = Pu⁻¹ * ⟨A, hA⟩ * Pu := by
    rw [mul_assoc, hrel, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h2, map_mul, map_mul, map_inv, inv_inv]

end Norm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
