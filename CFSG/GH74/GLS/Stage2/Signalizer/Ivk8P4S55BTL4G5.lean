module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4G2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4L

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open scoped commutatorElement

variable {F : Type} [Field F]

theorem transpose_mul_mul_apply (G β : Matrix (Fin 4) (Fin 4) F) (a b : Fin 4) :
    (Gᵀ * β * G) a b = (β *ᵥ (G *ᵥ Pi.single b 1)) ⬝ᵥ (G *ᵥ Pi.single a 1) := by
  rw [mulVec_single_one, mulVec_single_one]
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, col_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem caseG2 {H : Subgroup (GL (Fin 4) F)}
    {N : Submodule F (Fin 4 → F)} (hN0 : N ≠ ⊥) (hNt : N ≠ ⊤)
    (hHN : ∀ x ∈ H, ∀ v ∈ N, (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N) {B : GL (Fin 4) F}
    (hBN : ∀ v ∈ N, (B : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N) (hBH : ∀ x ∈ H, B * x = x * B)
    {c : Fˣ} (hc : B * B = GeneralLinearGroup.scalar (Fin 4) c) (hns : ¬ IsSquare (c : F))
    {β : Matrix (Fin 4) (Fin 4) F} (hβd : β.det ≠ 0)
    (hHβ : ∀ x ∈ H, (x : Matrix (Fin 4) (Fin 4) F)ᵀ * β * x = β)
    (hNβ : ∀ u ∈ N, ∀ v ∈ N, (β *ᵥ u) ⬝ᵥ v = 0) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq N
  set G : GL (Fin 4) F := SpecialLinearGroup.toGL g with hG
  have hst : ∀ M : Matrix (Fin 4) (Fin 4) F, (∀ v ∈ N, M *ᵥ v ∈ N) →
      StabF (finrank F N) (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * M *
        (G : Matrix (Fin 4) (Fin 4) F)) := fun M hM => stabF_conj hg hM
  have hcB : (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) *
      (G : Matrix (Fin 4) (Fin 4) F)) * (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (B : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) = (c : F) • 1 := by
    rw [conj_mul_conj, ← Units.val_mul, hc, GeneralLinearGroup.coe_scalar, scalar_apply,
      ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, inv_mul_self]
  have hd0 : finrank F N ≠ 0 := fun h => hN0 (Submodule.finrank_eq_zero.mp h)
  have hd4 : finrank F N ≠ 4 := fun h => hNt (Submodule.eq_top_of_finrank_eq (by
    rw [h, finrank_fin_fun]))
  have hdle : finrank F N ≤ 4 := by simpa using Submodule.finrank_le N
  rcases (show finrank F N = 1 ∨ finrank F N = 2 ∨ finrank F N = 3 by omega) with h1 | h2 | h3
  · rw [h1] at hst
    exact absurd (isSquare_of_eigvec hcB ee0_ne_zero (mulVec_e0_of_stabF1 (hst _ hBN))) hns
  · rw [h2] at hst
    have hmem : ∀ b : Fin 4, (b : ℕ) < 2 →
        (G : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single b 1 ∈ N := by
      intro b hb
      rw [← h2] at hb
      rw [← hg]
      refine ⟨Pi.single b 1, mem_flagSpace.mpr fun j hj => ?_, rfl⟩
      have hjb : j ≠ b := fun h => by subst h; omega
      simp [hjb]
    have hBx : ∀ x ∈ H, (B : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) := fun x hx => by
      rw [← Units.val_mul, ← Units.val_mul, hBH x hx]
    refine comm_of_map (cbv_injective G) (comm_of_lagr_blocks
      (β := bv ((G : Matrix (Fin 4) (Fin 4) F)ᵀ * β * (G : Matrix (Fin 4) (Fin 4) F)))
      (Bm := bv (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (B : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F))) ?_ ?_
      (toBlocks₂₁_bv_of_stabF2 (hst _ hBN)) ?_ ?_ ?_ ?_)
    · rw [det_bv]
      exact det_transpose_mul_ne_zero G hβd
    · ext i j
      rw [toBlocks₁₁, of_apply, bv_apply, transpose_mul_mul_apply, Matrix.zero_apply]
      exact hNβ _ (hmem _ (by rw [val_e4_inl]; exact j.isLt)) _
        (hmem _ (by rw [val_e4_inl]; exact i.isLt))
    · intro ν hν
      exact hns (isSquare_of_eigvec hcB ee0_ne_zero
        (mulVec_e0_of_bv (toBlocks₂₁_bv_of_stabF2 (hst _ hBN)) hν))
    · rintro _ ⟨x, hx, rfl⟩
      rw [coe_cbv]
      exact toBlocks₂₁_bv_of_stabF2 (hst _ (hHN x hx))
    · rintro _ ⟨x, hx, rfl⟩
      rw [coe_cbv, ← map_mul, ← map_mul, conj_mul_conj, conj_mul_conj, hBx x hx]
    · rintro _ ⟨x, hx, rfl⟩
      rw [coe_cbv, ← bv_transpose, ← map_mul, ← map_mul]
      exact congrArg bv (transpose_conj_mul (mul_inv_self G) (hHβ x hx))
  · rw [h3] at hst
    exact absurd (isSquare_of_roweig hcB ee3_ne_zero (vecMul_e3_of_stabF3 (hst _ hBN))) hns

theorem caseG (hK : ringChar F ≠ 2) {H : Subgroup (GL (Fin 4) F)}
    {N : Submodule F (Fin 4 → F)} (hN0 : N ≠ ⊥) (hNt : N ≠ ⊤)
    (hHN : ∀ x ∈ H, ∀ v ∈ N, (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N) {B : GL (Fin 4) F}
    (hBN : ∀ v ∈ N, (B : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N) (hBH : ∀ x ∈ H, B * x = x * B)
    (hT : IsT12 B) {β : Matrix (Fin 4) (Fin 4) F} (hβs : βᵀ = β) (hβd : β.det ≠ 0)
    (hHβ : ∀ x ∈ H, (x : Matrix (Fin 4) (Fin 4) F)ᵀ * β * x = β)
    (hBβ : (B : Matrix (Fin 4) (Fin 4) F)ᵀ * β = β * B)
    (hNβ : ∀ u ∈ N, ∀ v ∈ N, (β *ᵥ u) ⬝ᵥ v = 0) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  rcases hT with ⟨hB2, hfr⟩ | ⟨c, hc, hns⟩
  · exact caseG1 hK hB2 hfr hBH hβs hβd hHβ hBβ
  · exact caseG2 hN0 hNt hHN hBN hBH hc hns hβd hHβ hNβ

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
