module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.SLnFamily

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

section Conj

variable {L : Type} [Field L] {ν : ℕ}

theorem conjSLn_one_apply (X : SL(ν, L)) : conjSLn (1 : GL (Fin ν) L) X = X := by
  apply Subtype.ext
  rw [coe_conjSLn]
  simp

theorem conjSLn_mul_apply (M N : GL (Fin ν) L) (X : SL(ν, L)) :
    conjSLn (M * N) X = conjSLn M (conjSLn N X) := by
  apply Subtype.ext
  rw [coe_conjSLn, coe_conjSLn, coe_conjSLn, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem conjSLn_toGL_apply (S X : SL(ν, L)) :
    conjSLn (Matrix.SpecialLinearGroup.toGL S) X = S * X * S⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSLn, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem conjDiagn_eq_conjSLn (d : Fin ν → Lˣ) (X : SL(ν, L)) :
    conjDiagn d X = conjSLn (diagGLn d) X :=
  Subtype.ext rfl

end Conj

section Acts

variable {L : Type} [Field L] {ν : ℕ} {G : Type*} [Group G]

@[expose] def actsOn (ψ : SL(ν, L) →* G) : Subgroup G where
  carrier := {g | ∃ W : GL (Fin ν) L, ∀ X, g * ψ X * g⁻¹ = ψ (conjSLn W X)}
  one_mem' := ⟨1, fun X => by simp [conjSLn_one_apply]⟩
  mul_mem' := by
    rintro g h ⟨W, hW⟩ ⟨V, hV⟩
    refine ⟨W * V, fun X => ?_⟩
    rw [conjSLn_mul_apply, ← hW, ← hV]
    group
  inv_mem' := by
    rintro g ⟨W, hW⟩
    refine ⟨W⁻¹, fun X => ?_⟩
    have h1 := hW (conjSLn W⁻¹ X)
    rw [← conjSLn_mul_apply, mul_inv_cancel, conjSLn_one_apply] at h1
    rw [← h1]
    group

theorem mem_actsOn {ψ : SL(ν, L) →* G} {g : G} :
    g ∈ actsOn ψ ↔ ∃ W : GL (Fin ν) L, ∀ X, g * ψ X * g⁻¹ = ψ (conjSLn W X) := Iff.rfl

theorem range_le_actsOn (ψ : SL(ν, L) →* G) : ψ.range ≤ actsOn ψ := by
  rintro _ ⟨W, rfl⟩
  refine ⟨Matrix.SpecialLinearGroup.toGL W, fun X => ?_⟩
  rw [conjSLn_toGL_apply]
  simp

theorem mem_actsOn_of_commute {ψ : SL(ν, L) →* G} {g : G} (h : ∀ X, g * ψ X = ψ X * g) :
    g ∈ actsOn ψ := by
  refine ⟨1, fun X => ?_⟩
  rw [conjSLn_one_apply, h X]
  group

end Acts

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
