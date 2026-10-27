module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL fixed_transvection_false block_of_commute_single
  exists_diagGL_of_offdiag_zero coe_diagGL)
open scoped MatrixGroups

variable {n : ℕ} {k : Type} [Field k]

@[expose] noncomputable def invTransGL (g : GL (Fin n) k) : GL (Fin n) k where
  val := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose
  inv := (g : Matrix (Fin n) (Fin n) k).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem coe_invTransGL (g : GL (Fin n) k) :
    ((invTransGL g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose := rfl

theorem coe_invTransGL_inv (g : GL (Fin n) k) :
    (((invTransGL g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (g : Matrix (Fin n) (Fin n) k).transpose := rfl

@[expose] noncomputable def mapGL (φ : k ≃+* k) (g : GL (Fin n) k) : GL (Fin n) k :=
  Units.map φ.mapMatrix.toMonoidHom g

theorem coe_mapGL (φ : k ≃+* k) (g : GL (Fin n) k) :
    ((mapGL φ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      φ.mapMatrix (g : Matrix (Fin n) (Fin n) k) := rfl

theorem coe_mapGL_inv (φ : k ≃+* k) (g : GL (Fin n) k) :
    (((mapGL φ g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      φ.mapMatrix ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := rfl

theorem exists_sq_form (α : SL(n, k) →* SL(n, k)) (g : GL (Fin n) k) (φ : k ≃+* k) (ε : Bool)
    (hα : ∀ x, ((α x : SL(n, k)) : Matrix (Fin n) (Fin n) k) =
      (g : Matrix (Fin n) (Fin n) k) *
        φ.mapMatrix (if ε then (((x⁻¹ : SL(n, k)) : Matrix (Fin n) (Fin n) k)).transpose
          else (x : Matrix (Fin n) (Fin n) k)) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    ∃ g₂ : GL (Fin n) k, ∀ x : SL(n, k), ((α (α x) : SL(n, k)) : Matrix (Fin n) (Fin n) k) =
      (g₂ : Matrix (Fin n) (Fin n) k) * (φ.trans φ).mapMatrix (x : Matrix (Fin n) (Fin n) k) *
        ((g₂⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  have hmm : ∀ M : Matrix (Fin n) (Fin n) k,
      (φ.trans φ).mapMatrix M = φ.mapMatrix (φ.mapMatrix M) := fun M => by ext i j; rfl
  have hmt : ∀ M : Matrix (Fin n) (Fin n) k,
      φ.mapMatrix M.transpose = (φ.mapMatrix M).transpose := fun M => by ext i j; rfl
  cases ε
  · refine ⟨g * mapGL φ g, fun x => ?_⟩
    simp only [Bool.false_eq_true, ite_false] at hα
    rw [hα (α x), hα x, hmm]
    simp only [Units.val_mul, _root_.mul_inv_rev, map_mul, coe_mapGL, coe_mapGL_inv,
      Matrix.mul_assoc]
  · refine ⟨g * mapGL φ (invTransGL g), fun x => ?_⟩
    simp only [ite_true] at hα
    have h1 : (((α x)⁻¹ : SL(n, k)) : Matrix (Fin n) (Fin n) k) =
        (g : Matrix (Fin n) (Fin n) k) * φ.mapMatrix (x : Matrix (Fin n) (Fin n) k).transpose *
          ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      rw [← map_inv, hα (x⁻¹)]
      simp
    rw [hα (α x), h1, hmm]
    simp only [Units.val_mul, _root_.mul_inv_rev, map_mul, coe_mapGL, coe_mapGL_inv,
      coe_invTransGL, coe_invTransGL_inv, Matrix.transpose_mul, Matrix.transpose_transpose, hmt,
      Matrix.mul_assoc]

theorem exists_pair_same (hn : 3 ≤ n) (σ : Fin n → Bool) : ∃ i j : Fin n, i ≠ j ∧ σ i = σ j := by
  obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt σ (by simp; omega)
  exact ⟨i, j, hij, h⟩

theorem exists_third (hn : 3 ≤ n) (l m : Fin n) : ∃ t : Fin n, t ≠ l ∧ t ≠ m := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {l, m} := fun t _ => by
    by_cases htl : t = l
    · simp [htl]
    · simp [h t htl]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_two (a := l) (b := m)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem diag_of_fixes_blocks (hn : 3 ≤ n) (σ : Fin n → Bool) (α : SL(n, k) →* SL(n, k))
    (g : GL (Fin n) k) (φ : k ≃+* k)
    (hα : ∀ x, ((α x : SL(n, k)) : Matrix (Fin n) (Fin n) k) =
      (g : Matrix (Fin n) (Fin n) k) * φ.mapMatrix (x : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (hfix : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b), α s = s) :
    (∀ c, φ c = c) ∧ ∃ u : Fin n → kˣ, g = diagGL u ∧ ∀ i j, σ i = σ j → u i = u j := by
  have hpair : ∀ i j (hij : i ≠ j), σ i = σ j →
      (∀ c, φ c = c) ∧ (g : Matrix (Fin n) (Fin n) k) * Matrix.single i j (1 : k) =
        Matrix.single i j 1 * (g : Matrix (Fin n) (Fin n) k) := by
    intro i j hij hσ
    have hcard : 2 ≤ (coordSet σ (σ i)).card :=
      Finset.one_lt_card.mpr ⟨i, mem_coordSet.mpr rfl, j, mem_coordSet.mpr hσ.symm, hij⟩
    refine fixed_transvection_false α g φ hα hij fun c => hfix (σ i) hcard _ ?_
    exact transvection_mem_coordBlockSL (mem_coordSet.mpr rfl) (mem_coordSet.mpr hσ.symm) hij c
  obtain ⟨i₀, j₀, hij₀, hσ₀⟩ := exists_pair_same hn σ
  refine ⟨(hpair i₀ j₀ hij₀ hσ₀).1, ?_⟩
  have hblock : ∀ i j (hij : i ≠ j), σ i = σ j → _ := fun i j hij hσ =>
    block_of_commute_single (g : Matrix (Fin n) (Fin n) k) (hpair i j hij hσ).2
      (hpair j i hij.symm hσ.symm).2
  have hoff : ∀ l m : Fin n, l ≠ m → (g : Matrix (Fin n) (Fin n) k) l m = 0 := by
    intro l m hlm
    by_cases hl : ∃ j, j ≠ l ∧ σ j = σ l
    · obtain ⟨j, hjl, hσ⟩ := hl
      exact (hblock l j hjl.symm hσ.symm).2.2.2.1 m hlm.symm
    · by_cases hm : ∃ j, j ≠ m ∧ σ j = σ m
      · obtain ⟨j, hjm, hσ⟩ := hm
        exact (hblock m j hjm.symm hσ.symm).2.1 l hlm
      · exfalso
        obtain ⟨t, htl, htm⟩ := exists_third hn l m
        have hσlm : σ l ≠ σ m := fun h => hl ⟨m, hlm.symm, h.symm⟩
        by_cases h : σ t = σ l
        · exact hl ⟨t, htl, h⟩
        · refine hm ⟨t, htm, ?_⟩
          cases hsl : σ l <;> cases hsm : σ m <;> cases hst : σ t <;>
            simp_all
  obtain ⟨u, hu⟩ := exists_diagGL_of_offdiag_zero g hoff
  refine ⟨u, hu, fun i j hσ => ?_⟩
  by_cases hij : i = j
  · rw [hij]
  · have h1 := (hblock i j hij hσ).1
    rw [hu, coe_diagGL, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h1
    exact Units.ext h1

end CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
