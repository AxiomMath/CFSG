module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.LinearGroups.Elementary
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup Matrix

namespace GenLocL4Ext

variable {F : Type} [Field F]

@[expose] def i0 (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, c, 0, 0; 1, 0, 0, 0; 0, 0, 0, c; 0, 0, 1, 0]

@[expose] def xs : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal ![1, 1, -1, -1]

theorem exists_scalar_of_commute_sl {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (h : ∀ g : SpecialLinearGroup (Fin n) F,
      (g : Matrix (Fin n) (Fin n) F) * M = M * (g : Matrix (Fin n) (Fin n) F)) :
    ∃ l : F, M = l • (1 : Matrix (Fin n) (Fin n) F) := by
  have hs : M ∈ Set.range (Matrix.scalar (Fin n) : F → Matrix (Fin n) (Fin n) F) := by
    refine Matrix.mem_range_scalar_of_commute_single (fun i j hij => ?_)
    have h1 := h (SpecialLinearGroup.transvection hij 1)
    rw [CFSG.LinearGroups.coe_transvection hij 1, add_mul, mul_add, one_mul, mul_one] at h1
    exact (add_right_injective _ h1 : _)
  obtain ⟨l, hl⟩ := hs
  exact ⟨l, by rw [← hl]; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]⟩

theorem slConjugation_congr {n : ℕ} (A A' : GL (Fin n) F) {ν : F} (hν : ν ≠ 0)
    (h : (A : Matrix (Fin n) (Fin n) F) = ν • (A' : Matrix (Fin n) (Fin n) F)) :
    CatalogueBHigherLinearAction.slConjugation n F A =
      CatalogueBHigherLinearAction.slConjugation n F A' := by
  have h1 : (A : Matrix (Fin n) (Fin n) F) * (ν⁻¹ • ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      1 := by
    rw [h, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hν, one_smul]
    exact A'.mul_inv
  have hinv : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ν⁻¹ • ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := Units.inv_eq_of_mul_eq_one_right h1
  ext g : 1
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, LinearFlag.coe_slConjugation, h, hinv]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hν, one_smul]

theorem index_le_two_of_cover {A : Type} [Group A] (H : Subgroup A) (b₀ : A)
    (h : ∀ b : A, b ∈ H ∨ b * b₀ ∈ H) : H.index ≤ 2 := by
  by_cases hb : b₀ ∈ H
  · have : H = ⊤ := eq_top_iff.2 fun b _ => (h b).elim id fun hb' => by
      simpa using H.mul_mem hb' (H.inv_mem hb)
    rw [this, index_top]
    omega
  · have : H.index = 2 := by
      refine index_eq_two_iff.2 ⟨b₀, fun b => ?_⟩
      by_cases hbH : b ∈ H
      · exact Or.inr ⟨hbH, fun hh => hb (by simpa using H.mul_mem (H.inv_mem hbH) hh)⟩
      · exact Or.inl ⟨(h b).resolve_left hbH, hbH⟩
    omega

end GenLocL4Ext

end CFSG.GH74.Generic.BProg.B2
