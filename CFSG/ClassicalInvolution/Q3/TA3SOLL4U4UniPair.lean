module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniFrame
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

variable (K) in
abbrev pairGram : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 1 0

abbrev pairD (l : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (l • 1) 0 0 ((-l) • 1)

noncomputable abbrev pairLevi (B : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks B 0 0 (leviStar h B)

theorem pairGram_mul_self : pairGram K * pairGram K = 1 := by
  rw [fromBlocks_multiply]
  simp [fromBlocks_one]

theorem barT_pairGram : ((pairGram K).map h.bar)ᵀ = pairGram K := by
  rw [fromBlocks_map, fromBlocks_transpose, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
    Matrix.map_zero _ (map_zero h.bar), transpose_one, transpose_zero]

theorem pairLevi_mul_pairD (B : Matrix (Fin 2) (Fin 2) K) (l : K) :
    pairLevi h B * pairD l = pairD l * pairLevi h B := by
  rw [pairLevi, pairD, fromBlocks_multiply, fromBlocks_multiply]
  simp

@[expose] noncomputable def pairF (E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (HypIndex 2 0) K :=
  pairGram K * (E.map h.bar)ᵀ * hypGram 2 0 K

@[expose] noncomputable def pairFrm (E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K)
    (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  pairF h E * Y * E

theorem pairFrm_smul (E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K) (c : K)
    (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : pairFrm h E (c • Y) = c • pairFrm h E Y := by
  rw [pairFrm, pairFrm, Matrix.mul_smul, Matrix.smul_mul]

theorem barT_pairF (E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K) :
    ((pairF h E).map h.bar)ᵀ = hypGram 2 0 K * E * pairGram K := by
  rw [pairF, barT_mul, barT_mul, hypGram_conjTranspose, barT_barT, barT_pairGram,
    Matrix.mul_assoc]

structure PairFrame (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (l : K)
    (E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K) : Prop where
  gram : (E.map h.bar)ᵀ * hypGram 2 0 K * E = pairGram K
  EF : E * pairF h E = 1
  AE : A * E = E * pairD l
  FA : pairF h E * A = pairD l * pairF h E

namespace PairFrame

variable {h} {A : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {l : K}
  {E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K} (hE : PairFrame h A l E)

include hE

theorem FE : pairF h E * E = 1 := by
  have := hE.gram
  rw [pairF, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (E.map h.bar)ᵀ, this,
    pairGram_mul_self]

theorem eq_frm (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :
    Y = E * pairFrm h E Y * pairF h E := by
  calc Y = (E * pairF h E) * Y * (E * pairF h E) := by
        rw [hE.EF, Matrix.one_mul, Matrix.mul_one]
    _ = E * pairFrm h E Y * pairF h E := by simp only [pairFrm, Matrix.mul_assoc]

theorem frm_conj (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    pairFrm h E (E * M * pairF h E) = M := by
  calc pairFrm h E (E * M * pairF h E) = (pairF h E * E) * M * (pairF h E * E) := by
        simp only [pairFrm, Matrix.mul_assoc]
    _ = M := by rw [hE.FE, Matrix.one_mul, Matrix.mul_one]

theorem frm_mul (Y Y' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :
    pairFrm h E (Y * Y') = pairFrm h E Y * pairFrm h E Y' := by
  calc pairFrm h E (Y * Y') = pairF h E * Y * (E * pairF h E) * Y' * E := by
        rw [hE.EF, Matrix.mul_one]; simp only [pairFrm, Matrix.mul_assoc]
    _ = pairFrm h E Y * pairFrm h E Y' := by simp only [pairFrm, Matrix.mul_assoc]

theorem conj_mul (M M' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (E * M * pairF h E) * (E * M' * pairF h E) = E * (M * M') * pairF h E := by
  calc (E * M * pairF h E) * (E * M' * pairF h E) = E * M * (pairF h E * E) * M' * pairF h E := by
        simp only [Matrix.mul_assoc]
    _ = E * (M * M') * pairF h E := by rw [hE.FE, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem frm_isometry {Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hY : (Y.map h.bar)ᵀ * hypGram 2 0 K * Y = hypGram 2 0 K) :
    ((pairFrm h E Y).map h.bar)ᵀ * pairGram K * pairFrm h E Y = pairGram K := by
  have hFGF : ((pairF h E).map h.bar)ᵀ * pairGram K * pairF h E = hypGram 2 0 K := by
    rw [barT_pairF]
    calc hypGram 2 0 K * E * pairGram K * pairGram K * pairF h E =
          hypGram 2 0 K * (E * pairF h E) := by
          rw [Matrix.mul_assoc (hypGram 2 0 K * E), pairGram_mul_self, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = hypGram 2 0 K := by rw [hE.EF, Matrix.mul_one]
  have key : (E.map h.bar)ᵀ *
      ((Y.map h.bar)ᵀ * (((pairF h E).map h.bar)ᵀ * pairGram K * pairF h E) * Y) * E =
      pairGram K := by rw [hFGF, hY, hE.gram]
  rw [pairFrm, barT_mul, barT_mul]
  refine Eq.trans ?_ key
  simp only [Matrix.mul_assoc]

theorem frm_mul_pairD {Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {c : K}
    (hY : Y * A = c • (A * Y)) : pairFrm h E Y * pairD l = c • (pairD l * pairFrm h E Y) := by
  calc pairFrm h E Y * pairD l = pairF h E * (Y * A) * E := by
        rw [pairFrm, Matrix.mul_assoc, ← hE.AE]; simp only [Matrix.mul_assoc]
    _ = c • (pairF h E * A * Y * E) := by
        rw [hY, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
    _ = c • (pairD l * pairFrm h E Y) := by rw [hE.FA]; simp only [pairFrm, Matrix.mul_assoc]

theorem exists_conj (hl : 2 * l ≠ 0) {Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hYi : (Y.map h.bar)ᵀ * hypGram 2 0 K * Y = hypGram 2 0 K) {c : K} (hc : c = 1 ∨ c = -1)
    (hY : Y * A = c • (A * Y)) {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det = 1) :
    ∃ B' : Matrix (Fin 2) (Fin 2) K, B'.det = 1 ∧
      Y * (E * pairLevi h B * pairF h E) = (E * pairLevi h B' * pairF h E) * Y := by
  have hD := hE.frm_mul_pairD hY
  have hI := hE.frm_isometry hYi
  have key : ∃ B' : Matrix (Fin 2) (Fin 2) K, B'.det = 1 ∧
      pairFrm h E Y * pairLevi h B = pairLevi h B' * pairFrm h E Y := by
    rcases hc with rfl | rfl
    · rw [one_smul] at hD
      obtain ⟨h12, h21⟩ := toBlocks₁₂_eq_zero_of_comm hl hD
      have hM : pairFrm h E Y =
          fromBlocks (pairFrm h E Y).toBlocks₁₁ 0 0 (pairFrm h E Y).toBlocks₂₂ := by
        conv_lhs => rw [← fromBlocks_toBlocks (pairFrm h E Y), h12, h21]
      rw [hM] at hI ⊢
      exact exists_levi_conj_diag h (star_mul_eq_one_of_diag h hI) hB
    · rw [neg_one_smul] at hD
      obtain ⟨h11, h22⟩ := toBlocks₁₁_eq_zero_of_anticomm hl hD
      have hM : pairFrm h E Y =
          fromBlocks 0 (pairFrm h E Y).toBlocks₁₂ (pairFrm h E Y).toBlocks₂₁ 0 := by
        conv_lhs => rw [← fromBlocks_toBlocks (pairFrm h E Y), h11, h22]
      rw [hM] at hI ⊢
      exact exists_levi_conj_anti h (star_mul_eq_one_of_anti h hI) hB
  obtain ⟨B', hB', hconj⟩ := key
  refine ⟨B', hB', ?_⟩
  conv_lhs => rw [hE.eq_frm Y]
  conv_rhs => rw [hE.eq_frm Y]
  rw [hE.conj_mul, hE.conj_mul, hconj]

theorem levi_comm (B : Matrix (Fin 2) (Fin 2) K) :
    (E * pairLevi h B * pairF h E) * A = A * (E * pairLevi h B * pairF h E) := by
  calc (E * pairLevi h B * pairF h E) * A = E * (pairLevi h B * pairD l) * pairF h E := by
        rw [Matrix.mul_assoc, hE.FA]; simp only [Matrix.mul_assoc]
    _ = A * (E * pairLevi h B * pairF h E) := by
        rw [pairLevi_mul_pairD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hE.AE]
        simp only [Matrix.mul_assoc]

theorem frm_mul_levi {Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {B : Matrix (Fin 2) (Fin 2) K}
    {c : K}
    (hY : Y * (E * pairLevi h B * pairF h E) = c • ((E * pairLevi h B * pairF h E) * Y)) :
    pairFrm h E Y * pairLevi h B = c • (pairLevi h B * pairFrm h E Y) := by
  have := congrArg (pairFrm h E) hY
  rwa [hE.frm_mul, hE.frm_conj, pairFrm_smul, hE.frm_mul, hE.frm_conj] at this

end PairFrame

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
