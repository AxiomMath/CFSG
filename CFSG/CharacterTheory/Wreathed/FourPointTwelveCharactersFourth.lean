module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersThird

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

namespace ColumnData

variable {ι : Type*} {D : ColumnData ι} {κ lam γ : ι} {pβ pκ pl δ q₂ q₃ : ℤ}

theorem Stage1.cs_values (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) :
    D.cs D.β₁ = -pβ ∧ D.cs D.χ₂ = 0 ∧ D.cs D.χ₃ = 0 ∧ D.cs D.η₁ = 0 ∧
    ((D.cs κ = 0 ∧ D.cs lam = 0 ∧ D.cs γ = 2 * δ ∧
        ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.cs χ = 1) ∨
      (D.cs κ = pκ ∧ D.cs lam = -pl ∧ D.cs γ = δ ∧
        ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.cs χ = 2)) := by
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  obtain ⟨rβ1, rβ2, rβ3, -, rβ5⟩ := hS.row_β
  obtain ⟨rκ1, rκ2, rκ3, -, rκ5⟩ := hS.row_κ
  obtain ⟨rl1, rl2, rl3, -, rl5⟩ := hS.row_lam
  obtain ⟨j1, j2, j3, -, j5⟩ := hS.row_χ₂
  obtain ⟨k1, k2, k3, -, k5⟩ := hS.row_χ₂'
  obtain ⟨l1, l2, l3, -, l5⟩ := hS.row_χ₃
  obtain ⟨m1, m2, m3, -, m5⟩ := hS.row_χ₃'
  obtain ⟨n1, n2, n3, -, n5⟩ := hS.row_η
  obtain ⟨o1, o2, o3, -, o5⟩ := hS.row_η'
  obtain ⟨g1, g2, g3, -, g5⟩ := hS.row_γ
  have c2' : D.cs (D.cj D.χ₂) = D.cs D.χ₂ := h.cs_cj _ h2B
  have c3' : D.cs (D.cj D.χ₃) = D.cs D.χ₃ := h.cs_cj _ h3B
  have cη' : D.cs (D.cj D.η₁) = D.cs D.η₁ := h.cs_cj _ h.η_mem
  have hsub : ∀ F : ι → ℤ, ∑ χ ∈ D.B, (D.c₂ χ - D.cs χ) * F χ =
      ∑ χ ∈ D.B, D.c₂ χ * F χ - ∑ χ ∈ D.B, D.cs χ * F χ := fun F => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  have hR : ∀ (F : ι → ℤ), (∀ χ ∈ rest11 D κ lam γ, F χ = 0) →
      ∑ χ ∈ rest11 D κ lam γ, (D.c₂ χ - D.cs χ) * F χ = 0 := fun F hF =>
    Finset.sum_eq_zero fun χ hχ => by rw [hF χ hχ, mul_zero]
  have hZP := hsub D.P
  rw [h.c₂P, h.csP, hS.sum_eq h, hR D.P fun χ hχ => (hS.mem_rest hχ).2.1, h.P_p, rβ1, rκ1,
    rl1, j1, k1, l1, m1, n1, o1, g1, h.c₂_p, h.cs_p, rβ5, rκ5, rl5, j5, k5, l5, m5, n5, o5,
    g5] at hZP
  have hZL₁ := hsub D.L₁
  rw [h.c₂L₁, h.csL₁, hS.sum_eq h, hR D.L₁ fun χ hχ => (hS.mem_rest hχ).2.2.2.1, h.L₁_p, rβ2,
    rκ2, rl2, j2, k2, l2, m2, n2, o2, g2, h.c₂_p, h.cs_p, rβ5, rκ5, rl5, j5, k5, l5, m5, n5,
    o5, g5] at hZL₁
  have hZL₂ := hsub D.L₂
  rw [h.c₂L₂, h.csL₂, hS.sum_eq h, hR D.L₂ fun χ hχ => (hS.mem_rest hχ).2.2.2.2.1, h.L₂_p,
    rβ3, rκ3, rl3, j3, k3, l3, m3, n3, o3, g3, h.c₂_p, h.cs_p, rβ5, rκ5, rl5, j5, k5, l5, m5,
    n5, o5, g5] at hZL₂
  have hZc₂ := hsub D.c₂
  have hc₂cs : ∑ χ ∈ D.B, D.cs χ * D.c₂ χ = 6 := by
    rw [← h.c₂cs]
    exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  rw [h.c₂c₂, hc₂cs, hS.sum_eq h, hR D.c₂ fun χ hχ => (hS.mem_rest hχ).2.2.2.2.2.2.1, h.c₂_p,
    rβ5, rκ5, rl5, j5, k5, l5, m5, n5, o5, g5, h.cs_p] at hZc₂
  have hZZ : ∑ χ ∈ D.B, (D.c₂ χ - D.cs χ) * (D.c₂ χ - D.cs χ) = 3 := by
    have e : ∀ χ ∈ D.B, (D.c₂ χ - D.cs χ) * (D.c₂ χ - D.cs χ) =
        D.c₂ χ * D.c₂ χ - D.c₂ χ * D.cs χ - D.cs χ * D.c₂ χ + D.cs χ * D.cs χ :=
      fun χ _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, h.c₂c₂, h.c₂cs, hc₂cs, h.cscs]
    norm_num
  have hRZ : ∑ χ ∈ rest11 D κ lam γ, (D.c₂ χ - D.cs χ) * (D.c₂ χ - D.cs χ) =
      ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.cs χ :=
    Finset.sum_congr rfl fun χ hχ => by rw [(hS.mem_rest hχ).2.2.2.2.2.2.1]; ring
  rw [hS.sum_eq h, hRZ, h.c₂_p, h.cs_p, rβ5, rκ5, rl5, j5, k5, l5, m5, n5, o5, g5, c2', c3',
    cη'] at hZZ
  have hr : 0 ≤ ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.cs χ :=
    Finset.sum_nonneg fun χ _ => mul_self_nonneg _
  rw [c2', c3', cη'] at hZL₂ hZc₂ hZP hZL₁
  obtain ⟨hzβ, hw2, hw3, hhh, halt⟩ := Z_solve (zβ := -pβ - D.cs D.β₁)
    (zκ := pκ - D.cs κ) (zl := -pl - D.cs lam) (w₂ := 0 - D.cs D.χ₂) (w₃ := 0 - D.cs D.χ₃)
    (hh := 0 - D.cs D.η₁) (g := 2 * δ - D.cs γ) (r := ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.cs χ)
    hS.pβ_val hS.pκ_val hS.pl_val h.ε_val hS.δ_val hS.q₂_val hS.q₃_val (by linarith) hr
    (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
  rcases halt with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
  · exact Or.inl ⟨by linarith, by linarith, by linarith, e4⟩
  · exact Or.inr ⟨by linarith, by linarith, by linarith, e4⟩

theorem Stage1.T_ne_rest (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) {χ : ι}
    (hχ : χ ∈ rest11 D κ lam γ) (hc : D.cs χ = D.c₁ χ) : False := by
  obtain ⟨hχB, -, -, hL₁, hL₂, hL₃, hc₂, hc₁₃⟩ := hS.mem_rest hχ
  rcases h.T_ne χ hχB with e | e
  · apply e
    rw [hL₂, hc₂, hc, ← hc₁₃]
    ring
  · apply e
    rw [hL₁, hL₃, ← hc₁₃]
    ring

theorem Stage1.final (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) :
    D.c₁ γ = 2 * δ ∧ D.c₁ κ = 0 ∧ D.c₁ lam = 0 ∧ D.cs κ = 0 ∧ D.cs lam = 0 ∧
    D.cs γ = 2 * δ ∧ ∃ ψ, rest11 D κ lam γ = {ψ} ∧ (D.cs ψ = 1 ∨ D.cs ψ = -1) ∧
      D.c₁ ψ = 0 ∧ D.c₃ ψ = 0 ∧ D.cj ψ = ψ := by
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  obtain ⟨hc₁β, hc₁η, -, -, halt₁⟩ := hS.c₁_values h
  obtain ⟨-, -, -, -, eη, -, -⟩ := hS.c₁_pairs h
  obtain ⟨hcsβ, hcs2, hcs3, hcsη, halt₂⟩ := hS.cs_values h
  obtain ⟨-, -, -, -, rβ5⟩ := hS.row_β
  obtain ⟨-, -, -, -, rκ5⟩ := hS.row_κ
  obtain ⟨-, -, -, -, rl5⟩ := hS.row_lam
  obtain ⟨-, -, -, -, j5⟩ := hS.row_χ₂
  obtain ⟨-, -, -, -, k5⟩ := hS.row_χ₂'
  obtain ⟨-, -, -, -, l5⟩ := hS.row_χ₃
  obtain ⟨-, -, -, -, m5⟩ := hS.row_χ₃'
  obtain ⟨-, -, -, -, n5⟩ := hS.row_η
  obtain ⟨-, -, -, -, o5⟩ := hS.row_η'
  obtain ⟨-, -, -, -, g5⟩ := hS.row_γ
  have c2' : D.cs (D.cj D.χ₂) = 0 := by rw [h.cs_cj _ h2B, hcs2]
  have c3' : D.cs (D.cj D.χ₃) = 0 := by rw [h.cs_cj _ h3B, hcs3]
  have cη' : D.cs (D.cj D.η₁) = 0 := by rw [h.cs_cj _ h.η_mem, hcsη]
  have hZc₁ : ∑ χ ∈ D.B, (D.c₂ χ - D.cs χ) * D.c₁ χ = 0 := by
    have e : ∑ χ ∈ D.B, (D.c₂ χ - D.cs χ) * D.c₁ χ =
        ∑ χ ∈ D.B, D.c₁ χ * D.c₂ χ - ∑ χ ∈ D.B, D.c₁ χ * D.cs χ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [e, h.c₁c₂, h.c₁cs, sub_self]
  have hRc : ∑ χ ∈ rest11 D κ lam γ, (D.c₂ χ - D.cs χ) * D.c₁ χ =
      -∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.c₁ χ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun χ hχ => by rw [(hS.mem_rest hχ).2.2.2.2.2.2.1]; ring
  rw [hS.sum_eq h, hRc, h.c₂_p, h.cs_p, rβ5, hcsβ, rκ5, rl5, j5, hcs2, k5, c2', l5, hcs3, m5,
    c3', n5, hcsη, o5, cη', g5, eη, hc₁η] at hZc₁
  have hsq : ∀ χ ∈ rest11 D κ lam γ, D.cs χ * D.cs χ ≤
      ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.cs χ := fun χ hχ =>
    Finset.single_le_sum (f := fun χ => D.cs χ * D.cs χ) (fun χ _ => mul_self_nonneg _) hχ
  rcases halt₁ with ⟨hg, hvκ, hvl, hR0⟩ | ⟨hg, hvκ, hvl, ω, hω, hω1, hR1⟩
  · have hRs : ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.c₁ χ = 0 :=
      Finset.sum_eq_zero fun χ hχ => by rw [hR0 χ hχ, mul_zero]
    rw [hRs, hg, hvκ, hvl] at hZc₁
    rcases halt₂ with ⟨hsκ, hsl, hsγ, hr1⟩ | ⟨hsκ, hsl, hsγ, hr2⟩
    · obtain ⟨ψ, hψ, hψ1, hψ0⟩ := exists_of_sum_mul_self_eq_one _ _ hr1
      have hall : rest11 D κ lam γ = {ψ} := by
        ext χ
        rw [Finset.mem_singleton]
        constructor
        · intro hχ
          by_contra hne
          exact hS.T_ne_rest h hχ (by rw [hψ0 χ hχ hne, hR0 χ hχ])
        · rintro rfl
          exact hψ
      have hcjψ : D.cj ψ = ψ := by
        have e := hS.cj_mem_rest h hψ
        rw [hall, Finset.mem_singleton] at e
        exact e
      have hc₁ψ := hR0 ψ hψ
      refine ⟨hg, hvκ, hvl, hsκ, hsl, hsγ, ψ, hall, hψ1, hc₁ψ, ?_, hcjψ⟩
      rw [← (hS.mem_rest hψ).2.2.2.2.2.2.2, hc₁ψ]
    · rw [hsκ, hsl, hsγ] at hZc₁
      exfalso
      rcases hS.δ_val with e | e <;> rw [e] at hZc₁ <;> norm_num at hZc₁
  · have hRs : ∑ χ ∈ rest11 D κ lam γ, D.cs χ * D.c₁ χ = D.cs ω * D.c₁ ω := by
      refine Finset.sum_eq_single_of_mem ω hω fun χ hχ hne => ?_
      rw [hR1 χ hχ hne, mul_zero]
    rw [hRs, hg, hvκ, hvl] at hZc₁
    exfalso
    rcases halt₂ with ⟨hsκ, hsl, hsγ, hr1⟩ | ⟨hsκ, hsl, hsγ, hr2⟩
    · rw [hsκ, hsl, hsγ] at hZc₁
      have hb := hsq ω hω
      rw [hr1] at hb
      have hp1 := sign_mul_self hS.pκ_val
      have hp2 := sign_mul_self hS.pl_val
      rcases hω1 with e | e <;> rw [e] at hZc₁
      · have e2 : D.cs ω = 2 := by linarith
        rw [e2] at hb
        norm_num at hb
      · have e2 : D.cs ω = -2 := by linarith
        rw [e2] at hb
        norm_num at hb
    · rw [hsκ, hsl, hsγ] at hZc₁
      have hδ2 := sign_mul_self hS.δ_val
      have hcs : D.cs ω = D.c₁ ω := by
        rcases hω1 with e | e <;> rw [e] at hZc₁ ⊢ <;> linarith
      exact hS.T_ne_rest h hω hcs

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
