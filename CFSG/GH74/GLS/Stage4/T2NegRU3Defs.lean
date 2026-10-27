module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Mat
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3 Matrix

variable {p n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def tzMat (K : Type) [Field K] : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  blk3 (-1) 0 0 1 0 (-1)

theorem det_tzMat : (tzMat K).det = 1 := by
  simp [tzMat, det_blk3]

theorem tzMat_gram (h : UnitaryFieldData p n K) :
    ((tzMat K).map h.bar)ᵀ * hypGram 1 1 K * tzMat K = hypGram 1 1 K := by
  refine (blk3_gram_iff h _ _ _ _ _ _).mpr ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    (obtain rfl := Subsingleton.elim i 0) <;> (obtain rfl := Subsingleton.elim j 0) <;>
    simp [Matrix.mul_apply]

@[expose] noncomputable def tzU (h : UnitaryFieldData p n K) : hypSU h 1 1 :=
  mkHypSU h (tzMat K) (tzMat_gram h) det_tzMat

@[expose] noncomputable def X0U (h : UnitaryFieldData p n K) : Subgroup (hypSU h 1 1) :=
  (Subgroup.center (UHeis h)).map uSU

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3
