module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExt
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Incl

variable (K : Type*) [Field K] {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

@[expose] def inclMat (j : α → β) : Matrix β α K := Matrix.of fun b a => if b = j a then 1 else 0

variable {K}

theorem inclMat_transpose_mul {j : α → β} (hj : Function.Injective j) :
    (inclMat K j)ᵀ * inclMat K j = 1 := by
  ext a a'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, inclMat, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (j a)]
  · simp [hj.eq_iff]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem inclMat_transpose_mul_disjoint {j j' : α → β} (h : ∀ a a', j a ≠ j' a') :
    (inclMat K j)ᵀ * inclMat K j' = 0 := by
  ext a a'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, inclMat, Matrix.of_apply,
    Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : b = j a
  · subst hb
    have hne : j a ≠ j' a' := h a a'
    simp [hne]
  · simp [hb]

theorem inclMat_map {L : Type*} [Field L] (f : K → L) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (j : α → β) : (inclMat K j).map f = inclMat L j := by
  ext b a
  simp only [Matrix.map_apply, inclMat, Matrix.of_apply]
  split_ifs <;> simp [hf0, hf1]

end Incl

section Sp

variable {K : Type} [Field K] {e n : ℕ}

@[expose] def spIncl (K : Type) [Field K] (s : Fin e → Fin n) : Matrix (Fin n ⊕ Fin n) (Fin e ⊕ Fin e) K :=
  fromBlocks (inclMat K s) 0 0 (inclMat K s)

theorem spIncl_transpose_mul {s : Fin e → Fin n} (hs : Function.Injective s) :
    (spIncl K s)ᵀ * spIncl K s = 1 := by
  rw [spIncl, fromBlocks_transpose, fromBlocks_multiply]
  simp [inclMat_transpose_mul hs]

theorem spIncl_transpose_mul_disjoint {s s' : Fin e → Fin n} (h : ∀ i i', s i ≠ s' i') :
    (spIncl K s)ᵀ * spIncl K s' = 0 := by
  rw [spIncl, spIncl, fromBlocks_transpose, fromBlocks_multiply]
  simp [inclMat_transpose_mul_disjoint h]

theorem spIncl_map (σ : K ≃+* K) (s : Fin e → Fin n) : (spIncl K s).map σ = spIncl K s := by
  rw [spIncl, fromBlocks_map, inclMat_map σ (map_zero σ) (map_one σ)]
  simp [Matrix.map_zero _ (map_zero σ)]

theorem formJ_mul_spIncl (s : Fin e → Fin n) :
    formJ n K * spIncl K s = spIncl K s * formJ e K := by
  simp only [formJ, spIncl, Matrix.fromBlocks_multiply]
  simp

theorem formJ_transpose (r : ℕ) : (formJ r K)ᵀ = -formJ r K := by
  rw [formJ, fromBlocks_transpose, fromBlocks_neg]
  simp

theorem extMat_symplectic {E : Matrix (Fin n ⊕ Fin n) (Fin e ⊕ Fin e) K} (hE : Eᵀ * E = 1)
    (hJ : formJ n K * E = E * formJ e K) {G : Matrix (Fin e ⊕ Fin e) (Fin e ⊕ Fin e) K}
    (hG : Gᵀ * formJ e K * G = formJ e K) :
    (extMat E G)ᵀ * formJ n K * extMat E G = formJ n K := by
  have hEJ : Eᵀ * formJ n K = formJ e K * Eᵀ := by
    have h := congrArg Matrix.transpose hJ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, formJ_transpose, formJ_transpose,
      Matrix.mul_neg, Matrix.neg_mul] at h
    exact neg_inj.1 h
  have hEJE : formJ e K * Eᵀ * E = formJ e K := by
    rw [Matrix.mul_assoc, hE, Matrix.mul_one]
  have e1 : (extMat E G)ᵀ = 1 + E * (Gᵀ - 1) * Eᵀ := by
    simp [extMat, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.mul_assoc]
  have step : (1 + E * (Gᵀ - 1) * Eᵀ) * formJ n K * extMat E G =
      formJ n K + E * (Gᵀ - 1) * (Eᵀ * formJ n K) + formJ n K * E * (G - 1) * Eᵀ +
        E * (Gᵀ - 1) * (Eᵀ * formJ n K * E) * (G - 1) * Eᵀ := by
    unfold extMat
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have inner : (Gᵀ - 1) * formJ e K + formJ e K * (G - 1) + (Gᵀ - 1) * formJ e K * (G - 1) = 0 := by
    have : (Gᵀ - 1) * formJ e K + formJ e K * (G - 1) + (Gᵀ - 1) * formJ e K * (G - 1) =
        Gᵀ * formJ e K * G - formJ e K := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [this, hG, sub_self]
  rw [e1, step, hEJ, hJ, hEJE]
  have : E * (Gᵀ - 1) * (formJ e K * Eᵀ) + E * formJ e K * (G - 1) * Eᵀ +
      E * (Gᵀ - 1) * formJ e K * (G - 1) * Eᵀ =
      E * ((Gᵀ - 1) * formJ e K + formJ e K * (G - 1) + (Gᵀ - 1) * formJ e K * (G - 1)) * Eᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [add_assoc, add_assoc, ← add_assoc (E * (Gᵀ - 1) * (formJ e K * Eᵀ)), this, inner]
  simp

end Sp

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
