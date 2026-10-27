module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersStage
public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersArith

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

theorem exists_of_sum_mul_self_eq_one {ι : Type*} (R : Finset ι) (f : ι → ℤ)
    (h : ∑ χ ∈ R, f χ * f χ = 1) :
    ∃ ω ∈ R, (f ω = 1 ∨ f ω = -1) ∧ ∀ χ ∈ R, χ ≠ ω → f χ = 0 := by
  have hex : ∃ ω ∈ R, f ω ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    have h0 : ∑ χ ∈ R, f χ * f χ = 0 :=
      Finset.sum_eq_zero fun χ hχ => by rw [hc χ hχ, mul_zero]
    omega
  obtain ⟨ω, hω, hne⟩ := hex
  have hsplit := Finset.add_sum_erase R (fun χ => f χ * f χ) hω
  have hpos := mul_self_pos.mpr hne
  have hnn : ∀ χ ∈ R.erase ω, 0 ≤ f χ * f χ := fun χ _ => mul_self_nonneg _
  have hnn' := Finset.sum_nonneg hnn
  have h1 : f ω * f ω = 1 := by omega
  have hrest : ∑ χ ∈ R.erase ω, f χ * f χ = 0 := by omega
  refine ⟨ω, hω, mul_self_eq_one_iff.mp h1, fun χ hχ hne' => ?_⟩
  exact mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hrest χ (Finset.mem_erase.mpr ⟨hne', hχ⟩))

theorem eq_zero_of_sum_mul_self_eq_zero {ι : Type*} (R : Finset ι) (f : ι → ℤ)
    (h : ∑ χ ∈ R, f χ * f χ = 0) : ∀ χ ∈ R, f χ = 0 := fun χ hχ =>
  mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun χ _ => mul_self_nonneg (f χ)).mp h χ hχ)

namespace ColumnData

variable {ι : Type*} {D : ColumnData ι} {κ lam γ : ι} {pβ pκ pl δ q₂ q₃ : ℤ}

theorem Stage1.c₁_pairs (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) :
    D.c₁ (D.cj D.χ₂) = D.c₁ D.χ₂ - 1 ∧ D.c₁ (D.cj D.χ₃) = D.c₁ D.χ₃ - 1 ∧
    D.c₃ D.χ₂ = D.c₁ D.χ₂ - 1 ∧ D.c₃ D.χ₃ = D.c₁ D.χ₃ - 1 ∧
    D.c₁ (D.cj D.η₁) = D.c₁ D.η₁ ∧ D.c₃ D.η₁ = D.c₁ D.η₁ ∧
    D.c₃ (D.cj D.η₁) = D.c₁ D.η₁ := by
  obtain ⟨v2, v3, -, -, v0⟩ := h.c₁₃_values
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have hηB := h.η_mem
  have hQ2 := hS.Q_J.1
  have hQ2' := hS.Q_J.2.1
  have hQ3 := hS.Q_J.2.2.1
  have hQ3' := hS.Q_J.2.2.2
  have hQη := hS.Q_H.1
  have hne : ∀ ξ, D.Q ξ ≠ 0 → D.η₁ ≠ ξ := fun ξ hξ e => hξ (by rw [← e, hQη])
  have hη := v0 D.η₁ hηB (hne _ hQ2) (hne _ hQ2') (hne _ hQ3) (hne _ hQ3')
  refine ⟨?_, ?_, by omega, by omega, ?_, hη.symm, ?_⟩
  · rw [h.c₁_cj _ h2B]
    omega
  · rw [h.c₁_cj _ h3B]
    omega
  · rw [h.c₁_cj _ hηB, hη]
  · rw [h.c₃_cj _ hηB]

theorem Stage1.c₁_values (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) :
    D.c₁ D.β₁ = -pβ ∧ D.c₁ D.η₁ = 0 ∧ (D.c₁ D.χ₂ = 0 ∨ D.c₁ D.χ₂ = 1) ∧
    (D.c₁ D.χ₃ = 0 ∨ D.c₁ D.χ₃ = 1) ∧
    ((D.c₁ γ = 2 * δ ∧ D.c₁ κ = 0 ∧ D.c₁ lam = 0 ∧
        ∀ χ ∈ rest11 D κ lam γ, D.c₁ χ = 0) ∨
      (D.c₁ γ = δ ∧ D.c₁ κ = pκ ∧ D.c₁ lam = -pl ∧ ∃ ω ∈ rest11 D κ lam γ,
        (D.c₁ ω = 1 ∨ D.c₁ ω = -1) ∧ ∀ χ ∈ rest11 D κ lam γ, χ ≠ ω → D.c₁ χ = 0)) := by
  obtain ⟨e2, e3, -, -, eη, -, -⟩ := hS.c₁_pairs h
  obtain ⟨rβ1, rβ2, -, -, rβ5⟩ := hS.row_β
  obtain ⟨rκ1, rκ2, -, -, rκ5⟩ := hS.row_κ
  obtain ⟨rl1, rl2, -, -, rl5⟩ := hS.row_lam
  obtain ⟨j1, j2, -, -, j5⟩ := hS.row_χ₂
  obtain ⟨k1, k2, -, -, k5⟩ := hS.row_χ₂'
  obtain ⟨l1, l2, -, -, l5⟩ := hS.row_χ₃
  obtain ⟨m1, m2, -, -, m5⟩ := hS.row_χ₃'
  obtain ⟨n1, n2, -, -, n5⟩ := hS.row_η
  obtain ⟨o1, o2, -, -, o5⟩ := hS.row_η'
  obtain ⟨g1, g2, -, -, g5⟩ := hS.row_γ
  have hR : ∀ (F : ι → ℤ), (∀ χ ∈ rest11 D κ lam γ, F χ = 0) →
      ∑ χ ∈ rest11 D κ lam γ, D.c₁ χ * F χ = 0 := fun F hF =>
    Finset.sum_eq_zero fun χ hχ => by rw [hF χ hχ, mul_zero]
  have hP := h.c₁P
  rw [hS.sum_eq h, hR D.P fun χ hχ => (hS.mem_rest hχ).2.1, h.P_p, rβ1, rκ1, rl1, j1, k1,
    l1, m1, n1, o1, g1, h.c₁_p] at hP
  have hL := h.c₁L₁
  rw [hS.sum_eq h, hR D.L₁ fun χ hχ => (hS.mem_rest hχ).2.2.2.1, h.L₁_p, rβ2, rκ2, rl2, j2,
    k2, l2, m2, n2, o2, g2, h.c₁_p] at hL
  have hC := h.c₁c₂
  rw [hS.sum_eq h, hR D.c₂ fun χ hχ => (hS.mem_rest hχ).2.2.2.2.2.2.1, h.c₂_p, rβ5, rκ5, rl5,
    j5, k5, l5, m5, n5, o5, g5, h.c₁_p] at hC
  have hN := h.c₁c₁
  rw [hS.sum_eq h, e2, e3, eη, h.c₁_p] at hN
  have hr : 0 ≤ ∑ χ ∈ rest11 D κ lam γ, D.c₁ χ * D.c₁ χ :=
    Finset.sum_nonneg fun χ _ => mul_self_nonneg _
  obtain ⟨hk, ha₂, ha₃, hvβ, halt⟩ := c1_solve (vβ := D.c₁ D.β₁) (vκ := D.c₁ κ) (vl := D.c₁ lam)
    (a₂ := D.c₁ D.χ₂) (a₃ := D.c₁ D.χ₃) (k := D.c₁ D.η₁) (g := D.c₁ γ)
    (r := ∑ χ ∈ rest11 D κ lam γ, D.c₁ χ * D.c₁ χ) hS.pβ_val hS.pκ_val hS.pl_val h.ε_val
    hS.δ_val (by linarith) (by linarith) (by linarith) (by linarith) hr
  refine ⟨hvβ, hk, ha₂, ha₃, ?_⟩
  rcases halt with ⟨hg, hvκ, hvl, hr0⟩ | ⟨hg, hvκ, hvl, hr1⟩
  · exact Or.inl ⟨hg, hvκ, hvl, eq_zero_of_sum_mul_self_eq_zero _ _ hr0⟩
  · exact Or.inr ⟨hg, hvκ, hvl, exists_of_sum_mul_self_eq_one _ _ hr1⟩

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
