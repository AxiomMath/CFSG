module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Hom
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Frame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

section Perm

variable {p f : ℕ} {K : Type} [Field K]

theorem submatrix_perm_mul_mul {m : Type} [Fintype m] [DecidableEq m] (M : Matrix (Fin 4) m K)
    (R : Matrix m m K) (N : Matrix m (Fin 4) K) (σ : Equiv.Perm (Fin 4)) :
    M.submatrix σ id * R * N.submatrix id σ = (M * R * N).submatrix σ σ := by
  have h1 := Matrix.submatrix_mul_equiv M R σ (Equiv.refl m) (Equiv.refl m)
  have h2 := Matrix.submatrix_mul_equiv (M * R) N σ (Equiv.refl m) σ
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at h1 h2
  rw [h1, h2]

theorem u4_cls3_frame_three (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hq : p ^ f = 3)
    {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1) :
    ∃ (E : Matrix (HypIndex 2 0) (Fin 4) K) (d : Fin 4 → h.fixedField),
      U4Frame h A E d ∧ d 0 = d 1 := by
  classical
  have := h.finite
  obtain ⟨E, d, hd, hgram, hfix⟩ := u4_cls3_frame h hp hA hAA
  have hcardF : Nat.card ↥h.fixedField = 3 := h.card_fixedField.trans hq
  have hpm : ∀ i, d i = 1 ∨ d i = -1 := by
    intro i
    have := Fintype.ofFinite ↥h.fixedField
    have hq' : Fintype.card ↥h.fixedField = 3 := by rw [← Nat.card_eq_fintype_card, hcardF]
    have h1 := FiniteField.pow_card_sub_one_eq_one (d i) (hd i)
    rw [hq'] at h1
    exact mul_self_eq_one_iff.mp (by simpa [sq] using h1)
  obtain ⟨i, j, hij, hdij⟩ : ∃ i j : Fin 4, i ≠ j ∧ d i = d j := by
    obtain ⟨i, j, hij, hh⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin 4 => decide (d i = 1)) (by simp)
    refine ⟨i, j, hij, ?_⟩
    simp only [decide_eq_decide] at hh
    by_cases hi : d i = 1
    · rw [hi, hh.mp hi]
    · have hj : d j ≠ 1 := fun hj => hi (hh.mpr hj)
      rcases hpm i with h1 | h1
      · exact absurd h1 hi
      · rcases hpm j with h2 | h2
        · exact absurd h2 hj
        · rw [h1, h2]
  have hperm : ∀ i j : Fin 4, i ≠ j → ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by decide
  obtain ⟨σ, hσ0, hσ1⟩ := hperm i j hij
  refine ⟨E.submatrix id σ, d ∘ σ, ⟨fun k => hd (σ k), ?_, fun k => hfix (σ k)⟩, ?_⟩
  · have e1 : ((E.submatrix id σ).map h.bar)ᵀ = ((E.map h.bar)ᵀ).submatrix σ id := by
      rw [← Matrix.submatrix_map, Matrix.transpose_submatrix]
    rw [e1, submatrix_perm_mul_mul, hgram, Matrix.submatrix_diagonal_equiv]
    rfl
  · simp [hσ0, hσ1, hdij]

end Perm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
