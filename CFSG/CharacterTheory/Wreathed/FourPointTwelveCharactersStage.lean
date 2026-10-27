module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersSecond

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

theorem nodup_append_of_sep {ι : Type*} {l₁ l₂ : List ι} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (f : ι → ℤ) (hf₁ : ∀ a ∈ l₁, f a ≠ 0) (hf₂ : ∀ b ∈ l₂, f b = 0) : (l₁ ++ l₂).Nodup := by
  rw [List.nodup_append]
  refine ⟨h₁, h₂, ?_⟩
  intro a ha b hb hab
  subst hab
  exact hf₁ a ha (hf₂ a hb)

theorem sq_add_sq_ne_zero {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) : a * a + b * b ≠ 0 := by
  rcases h with h | h
  · have := mul_self_pos.mpr h
    nlinarith [mul_self_nonneg b]
  · have := mul_self_pos.mpr h
    nlinarith [mul_self_nonneg a]

theorem sq_add_sq_add_sq_add_sq_ne_zero {a b c e : ℤ} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ e ≠ 0) :
    a * a + b * b + c * c + e * e ≠ 0 := by
  have ha := mul_self_nonneg a
  have hb := mul_self_nonneg b
  have hc := mul_self_nonneg c
  have he := mul_self_nonneg e
  rcases h with h | h | h | h
  · have := mul_self_pos.mpr h
    linarith
  · have := mul_self_pos.mpr h
    linarith
  · have := mul_self_pos.mpr h
    linarith
  · have := mul_self_pos.mpr h
    linarith

namespace ColumnData

variable {ι : Type*} {D : ColumnData ι} {x y γ : ι} {δ : ℤ}

theorem list11_nodup {κ lam : ι} (hEn : [D.p₀, D.β₁, κ, lam].Nodup)
    (hJn : [D.χ₂, D.cj D.χ₂, D.χ₃, D.cj D.χ₃].Nodup) (hηne : D.η₁ ≠ D.cj D.η₁)
    (hP0 : D.P D.p₀ ≠ 0) (hPβ : D.P D.β₁ ≠ 0) (hPκ : D.P κ ≠ 0) (hPl : D.P lam ≠ 0)
    (hQ2 : D.Q D.χ₂ ≠ 0) (hQ2' : D.Q (D.cj D.χ₂) ≠ 0) (hQ3 : D.Q D.χ₃ ≠ 0)
    (hQ3' : D.Q (D.cj D.χ₃) ≠ 0) (j1 : D.P D.χ₂ = 0) (k1 : D.P (D.cj D.χ₂) = 0)
    (l1 : D.P D.χ₃ = 0) (m1 : D.P (D.cj D.χ₃) = 0) (hPη : D.P D.η₁ = 0)
    (hPη' : D.P (D.cj D.η₁) = 0) (hQη : D.Q D.η₁ = 0) (hQη' : D.Q (D.cj D.η₁) = 0)
    (hLη : D.L₁ D.η₁ ≠ 0) (hLη' : D.L₃ (D.cj D.η₁) ≠ 0) (hPγ : D.P γ = 0) (hQγ : D.Q γ = 0)
    (hL₁γ : D.L₁ γ = 0) (hL₃γ : D.L₃ γ = 0) : (list11 D κ lam γ).Nodup := by
  have hEJ := nodup_append_of_sep hEn hJn D.P (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    exacts [hP0, hPβ, hPκ, hPl]) (by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    exacts [j1, k1, l1, m1])
  have hH : [D.η₁, D.cj D.η₁].Nodup := by
    simp [hηne]
  have hEJH := nodup_append_of_sep hEJ hH (fun χ => D.P χ * D.P χ + D.Q χ * D.Q χ) (by
    intro a ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sq_add_sq_ne_zero (Or.inl hP0)
    · exact sq_add_sq_ne_zero (Or.inl hPβ)
    · exact sq_add_sq_ne_zero (Or.inl hPκ)
    · exact sq_add_sq_ne_zero (Or.inl hPl)
    · exact sq_add_sq_ne_zero (Or.inr hQ2)
    · exact sq_add_sq_ne_zero (Or.inr hQ2')
    · exact sq_add_sq_ne_zero (Or.inr hQ3)
    · exact sq_add_sq_ne_zero (Or.inr hQ3')) (by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · simp only [hPη, hQη, mul_zero, add_zero]
    · simp only [hPη', hQη', mul_zero, add_zero])
  exact nodup_append_of_sep hEJH (List.nodup_singleton γ)
    (fun χ => D.P χ * D.P χ + D.Q χ * D.Q χ + D.L₁ χ * D.L₁ χ + D.L₃ χ * D.L₃ χ) (by
    intro a ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inl hP0)
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inl hPβ)
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inl hPκ)
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inl hPl)
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inr (Or.inl hQ2))
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inr (Or.inl hQ2'))
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inr (Or.inl hQ3))
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inr (Or.inl hQ3'))
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inr (Or.inr (Or.inl hLη)))
    · exact sq_add_sq_add_sq_add_sq_ne_zero (Or.inr (Or.inr (Or.inr hLη')))) (by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rw [hb, hPγ, hQγ, hL₁γ, hL₃γ]
    norm_num)

theorem ELabels.swap (hE : D.ELabels x y) : D.ELabels y x := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := nodup_four_iff.mp hE.nodup
  refine ⟨nodup_four_iff.mpr ⟨n1, n3, n2, n5, n4, n6.symm⟩, hE.y_mem, hE.x_mem, hE.Py, hE.Px,
    hE.Ly, hE.Lx, fun χ hχ hP => ?_⟩
  rcases hE.cover χ hχ hP with e | e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inr e))
  · exact Or.inr (Or.inr (Or.inl e))

theorem Valid.stage1_of (h : D.Valid) {κ lam : ι} (hE : D.ELabels κ lam)
    (hG : D.GammaData γ δ) (hcκ : D.c₂ κ = D.P κ) (hcl : D.c₂ lam = -D.P lam) :
    D.Stage1 κ lam γ (D.P D.β₁) (D.P κ) (D.P lam) δ (D.L₂ D.χ₂) (D.L₂ D.χ₃) := by
  obtain ⟨hγη, hγη'⟩ := hG.ne_η h hE
  obtain ⟨hcβ, -⟩ := h.c₂_pattern hE hG
  obtain ⟨hηne, hL₂β, hL₂κ, hL₂l, hL₃β, hL₃κ, hL₃l, hL₂J, hL₂0⟩ := h.L₂_structure hE hG
  obtain ⟨n12, n22, n33, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩ := h.six_ne
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := nodup_four_iff.mp hE.nodup
  have h2B' := h.cj_mem _ h2B
  have h3B' := h.cj_mem _ h3B
  have hηB' := h.cj_mem _ h.η_mem
  have hQη : D.Q D.η₁ = 0 := h.Q_η
  have hQη' : D.Q (D.cj D.η₁) = 0 := by rw [h.Q_cj _ h.η_mem, hQη, neg_zero]
  have hQγ : D.Q γ = 0 := by
    have e := h.Q_cj γ hG.mem
    rw [hG.cj_eq] at e
    omega
  have hQ2 : D.Q D.χ₂ ≠ 0 := (h.Q_ne_zero_iff h2B).mpr (Or.inl rfl)
  have hQ2' : D.Q (D.cj D.χ₂) ≠ 0 := (h.Q_ne_zero_iff h2B').mpr (Or.inr (Or.inl rfl))
  have hQ3 : D.Q D.χ₃ ≠ 0 := (h.Q_ne_zero_iff h3B).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hQ3' : D.Q (D.cj D.χ₃) ≠ 0 :=
    (h.Q_ne_zero_iff h3B').mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hPJ : ∀ χ ∈ D.B, D.Q χ ≠ 0 → D.P χ = 0 := fun χ hχ hQ => by
    by_contra hP
    exact hQ (h.Q_zero_of_P hE hG hχ hP)
  have hneQ : ∀ ξ ξ', D.Q ξ ≠ 0 → D.Q ξ' = 0 → ξ ≠ ξ' := fun ξ ξ' hξ hξ' e =>
    hξ (by rw [e, hξ'])
  have hJrow : ∀ χ ∈ D.B, D.Q χ ≠ 0 → D.P χ = 0 ∧ D.L₁ χ = 0 ∧ D.L₃ χ = 0 ∧ D.c₂ χ = 0 := by
    intro χ hχ hQ
    have hP := hPJ χ hχ hQ
    exact ⟨hP, h.L₁_off χ hχ hP (hneQ _ _ hQ hQη), h.L₃_off hχ hP (hneQ _ _ hQ hQη'),
      hG.c₂_off χ hχ hP (hneQ _ _ hQ hQγ)⟩
  obtain ⟨j1, j2, j3, j4⟩ := hJrow _ h2B hQ2
  obtain ⟨k1, k2, k3, k4⟩ := hJrow _ h2B' hQ2'
  obtain ⟨l1, l2, l3, l4⟩ := hJrow _ h3B hQ3
  obtain ⟨m1, m2, m3, m4⟩ := hJrow _ h3B' hQ3'
  have hPη' : D.P (D.cj D.η₁) = 0 := by rw [h.P_cj _ h.η_mem, h.η_P]
  have hPβ := h.β_P
  have hPκ := hE.Px
  have hPl := hE.Py
  have hcjβ : D.cj D.β₁ = D.β₁ := by
    have hB := h.cj_mem _ h.β_mem
    have hP : D.P (D.cj D.β₁) ≠ 0 := by rwa [h.P_cj _ h.β_mem]
    have hL : D.L₁ (D.cj D.β₁) = -D.P (D.cj D.β₁) := by
      rw [h.L₁_cj _ h.β_mem, hL₃β, h.P_cj _ h.β_mem]
    rcases h.Eminus _ hB hP hL with e | e
    · exact absurd (by rw [← h.cj_cj D.β₁, e, h.cj_p]) h.β_ne
    · exact e
  have hcjκ : D.cj κ = κ := by
    have hB := h.cj_mem _ hE.x_mem
    have hP : D.P (D.cj κ) ≠ 0 := by rwa [h.P_cj _ hE.x_mem]
    rcases hE.cover _ hB hP with e | e | e | e
    · exact absurd (by rw [← h.cj_cj κ, e, h.cj_p]) e2
    · exact absurd (by rw [← h.cj_cj κ, e, hcjβ]) e4
    · exact e
    · have hc := h.c₂_cj κ hE.x_mem
      have hPc := h.P_cj κ hE.x_mem
      rw [e] at hc hPc
      rw [hcl, hcκ, ← hPc] at hc
      exact absurd (by omega) hPl
  have hcjl : D.cj lam = lam := by
    have hB := h.cj_mem _ hE.y_mem
    have hP : D.P (D.cj lam) ≠ 0 := by rwa [h.P_cj _ hE.y_mem]
    rcases hE.cover _ hB hP with e | e | e | e
    · exact absurd (by rw [← h.cj_cj lam, e, h.cj_p]) e3
    · exact absurd (by rw [← h.cj_cj lam, e, hcjβ]) e5
    · exact absurd (by rw [← h.cj_cj lam, e, hcjκ]) e6.symm
    · exact e
  have rβ : D.P D.β₁ = D.P D.β₁ ∧ D.L₁ D.β₁ = -D.P D.β₁ ∧ D.L₂ D.β₁ = -D.P D.β₁ ∧
      D.L₃ D.β₁ = -D.P D.β₁ ∧ D.c₂ D.β₁ = -D.P D.β₁ := ⟨rfl, h.β_L, hL₂β, hL₃β, hcβ⟩
  have rκ : D.P κ = D.P κ ∧ D.L₁ κ = D.P κ ∧ D.L₂ κ = D.P κ ∧ D.L₃ κ = D.P κ ∧
      D.c₂ κ = D.P κ := ⟨rfl, hE.Lx, hL₂κ, hL₃κ, hcκ⟩
  have rl : D.P lam = D.P lam ∧ D.L₁ lam = D.P lam ∧ D.L₂ lam = D.P lam ∧
      D.L₃ lam = D.P lam ∧ D.c₂ lam = -D.P lam := ⟨rfl, hE.Ly, hL₂l, hL₃l, hcl⟩
  have rη : D.P D.η₁ = 0 ∧ D.L₁ D.η₁ = 2 * D.ε ∧ D.L₂ D.η₁ = 0 ∧ D.L₃ D.η₁ = 0 ∧
      D.c₂ D.η₁ = 0 :=
    ⟨h.η_P, h.L₁_η, hL₂0 _ h.η_mem h.η_P hQη, h.L₃_off h.η_mem h.η_P hηne,
      hG.c₂_off _ h.η_mem h.η_P (Ne.symm hγη)⟩
  have rη' : D.P (D.cj D.η₁) = 0 ∧ D.L₁ (D.cj D.η₁) = 0 ∧ D.L₂ (D.cj D.η₁) = 0 ∧
      D.L₃ (D.cj D.η₁) = 2 * D.ε ∧ D.c₂ (D.cj D.η₁) = 0 :=
    ⟨hPη', h.L₁_off _ hηB' hPη' (Ne.symm hηne), hL₂0 _ hηB' hPη' hQη', h.L₃_η,
      hG.c₂_off _ hηB' hPη' (Ne.symm hγη')⟩
  have rγ : D.P γ = 0 ∧ D.L₁ γ = 0 ∧ D.L₂ γ = 0 ∧ D.L₃ γ = 0 ∧ D.c₂ γ = 2 * δ :=
    ⟨hG.P0, h.L₁_off γ hG.mem hG.P0 hγη, hL₂0 γ hG.mem hG.P0 hQγ,
      h.L₃_off hG.mem hG.P0 hγη', hG.c₂γ⟩
  have hQβ := h.Q_zero_of_P hE hG h.β_mem hPβ
  have hQκ := h.Q_zero_of_P hE hG hE.x_mem hPκ
  have hQl := h.Q_zero_of_P hE hG hE.y_mem hPl
  have hnodup : (list11 D κ lam γ).Nodup := by
    refine list11_nodup hE.nodup (nodup_four_iff.mpr ⟨n22, c1, c2, c3, c4, n33⟩) hηne
      (by rw [h.P_p]; norm_num) hPβ hPκ hPl hQ2 hQ2' hQ3 hQ3' j1 k1 l1 m1 h.η_P hPη' hQη hQη'
      (by rw [h.L₁_η]; rcases h.ε_val with e | e <;> rw [e] <;> norm_num)
      (by rw [h.L₃_η]; rcases h.ε_val with e | e <;> rw [e] <;> norm_num) hG.P0 hQγ rγ.2.1
      rγ.2.2.2.1
  have hrest : ∀ χ ∈ D.B, χ ∉ list11 D κ lam γ → D.P χ = 0 ∧ D.Q χ = 0 ∧ D.L₁ χ = 0 ∧
      D.L₂ χ = 0 ∧ D.L₃ χ = 0 ∧ D.c₂ χ = 0 ∧ D.c₁ χ = D.c₃ χ := by
    intro χ hχ hn
    simp only [list11, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n0, nβ, nκ, nl, n2, n2', n3, n3', nη, nη', nγ⟩ := hn
    have hP : D.P χ = 0 := hE.P_zero hχ n0 nβ nκ nl
    have hQ : D.Q χ = 0 := by
      by_contra hQ
      rcases (h.Q_ne_zero_iff hχ).mp hQ with e | e | e | e <;> contradiction
    exact ⟨hP, hQ, h.L₁_off χ hχ hP nη, hL₂0 χ hχ hP hQ, h.L₃_off hχ hP nη',
      hG.c₂_off χ hχ hP nγ, h.c₁₃_values.2.2.2.2 χ hχ n2 n2' n3 n3'⟩
  exact { κ_mem := hE.x_mem
          lam_mem := hE.y_mem
          γ_mem := hG.mem
          pβ_val := h.P_unit h.β_mem hPβ
          pκ_val := h.P_unit hE.x_mem hPκ
          pl_val := h.P_unit hE.y_mem hPl
          δ_val := hG.δ_val
          q₂_val := hL₂J _ h2B hQ2
          q₃_val := hL₂J _ h3B hQ3
          η_ne := hηne
          large := (h.dich_ne hηne).1
          cj_β := hcjβ
          cj_κ := hcjκ
          cj_lam := hcjl
          cj_γ := hG.cj_eq
          row_β := rβ
          row_κ := rκ
          row_lam := rl
          row_χ₂ := ⟨j1, j2, rfl, j3, j4⟩
          row_χ₂' := ⟨k1, k2, h.L₂_cj _ h2B, k3, k4⟩
          row_χ₃ := ⟨l1, l2, rfl, l3, l4⟩
          row_χ₃' := ⟨m1, m2, h.L₂_cj _ h3B, m3, m4⟩
          row_η := rη
          row_η' := rη'
          row_γ := rγ
          Q_E := ⟨hQβ, hQκ, hQl⟩
          Q_H := ⟨hQη, hQη', hQγ⟩
          Q_J := ⟨hQ2, hQ2', hQ3, hQ3'⟩
          nodup := hnodup
          rest := hrest }

theorem Valid.exists_Stage1 (h : D.Valid) :
    ∃ κ lam γ : ι, ∃ pβ pκ pl δ q₂ q₃ : ℤ, D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃ := by
  obtain ⟨x, y, hE⟩ := h.exists_ELabels
  obtain ⟨γ, δ, hG⟩ := h.exists_GammaData
  obtain ⟨-, hcxy⟩ := h.c₂_pattern hE hG
  have hx := h.P_unit hE.x_mem hE.Px
  have hy := h.P_unit hE.y_mem hE.Py
  have sx := sign_mul (hG.c₂_E _ hE.x_mem hE.Px) hx
  rcases sx with e | e
  · have ey : D.c₂ y * D.P y = -1 := by linarith
    exact ⟨x, y, γ, _, _, _, _, _, _, h.stage1_of hE hG (eq_of_mul_eq_one hx e)
      (eq_neg_of_mul_eq_neg_one hy ey)⟩
  · have ey : D.c₂ y * D.P y = 1 := by linarith
    exact ⟨y, x, γ, _, _, _, _, _, _, h.stage1_of hE.swap hG (eq_of_mul_eq_one hy ey)
      (eq_neg_of_mul_eq_neg_one hx e)⟩

variable {κ lam : ι} {pβ pκ pl q₂ q₃ : ℤ}

theorem Stage1.list11_subset (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) :
    (list11 D κ lam γ).toFinset ⊆ D.B := by
  intro χ hχ
  simp only [list11, List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
    Finset.mem_singleton, insert_empty_eq] at hχ
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h.p_mem, h.β_mem, hS.κ_mem, hS.lam_mem, h2B, h.cj_mem _ h2B, h3B, h.cj_mem _ h3B,
    h.η_mem, h.cj_mem _ h.η_mem, hS.γ_mem]

@[expose] noncomputable def rest11 (D : ColumnData ι) (κ lam γ : ι) : Finset ι :=
  D.B \ (list11 D κ lam γ).toFinset

theorem Stage1.sum_eq (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) (f : ι → ℤ) :
    ∑ χ ∈ D.B, f χ = f D.p₀ + f D.β₁ + f κ + f lam + f D.χ₂ + f (D.cj D.χ₂) + f D.χ₃ +
      f (D.cj D.χ₃) + f D.η₁ + f (D.cj D.η₁) + f γ + ∑ χ ∈ rest11 D κ lam γ, f χ := by
  rw [rest11, ← Finset.sum_sdiff (hS.list11_subset h), sum_toFinset _ hS.nodup]
  simp only [list11, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem Stage1.mem_rest (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) {χ : ι}
    (hχ : χ ∈ rest11 D κ lam γ) :
    χ ∈ D.B ∧ D.P χ = 0 ∧ D.Q χ = 0 ∧ D.L₁ χ = 0 ∧ D.L₂ χ = 0 ∧ D.L₃ χ = 0 ∧
      D.c₂ χ = 0 ∧ D.c₁ χ = D.c₃ χ := by
  rw [rest11, Finset.mem_sdiff, List.mem_toFinset] at hχ
  exact ⟨hχ.1, hS.rest χ hχ.1 hχ.2⟩

theorem Stage1.cj_mem_rest (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) {χ : ι}
    (hχ : χ ∈ rest11 D κ lam γ) : D.cj χ ∈ rest11 D κ lam γ := by
  rw [rest11, Finset.mem_sdiff, List.mem_toFinset] at hχ ⊢
  refine ⟨h.cj_mem χ hχ.1, fun hc => hχ.2 ?_⟩
  simp only [list11, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
  rcases hc with e | e | e | e | e | e | e | e | e | e | e
  · left
    rw [← h.cj_cj χ, e, h.cj_p]
  · right; left
    rw [← h.cj_cj χ, e, hS.cj_β]
  · right; right; left
    rw [← h.cj_cj χ, e, hS.cj_κ]
  · right; right; right; left
    rw [← h.cj_cj χ, e, hS.cj_lam]
  · right; right; right; right; right; left
    rw [← h.cj_cj χ, e]
  · right; right; right; right; left
    rw [← h.cj_cj χ, e, h.cj_cj]
  · right; right; right; right; right; right; right; left
    rw [← h.cj_cj χ, e]
  · right; right; right; right; right; right; left
    rw [← h.cj_cj χ, e, h.cj_cj]
  · right; right; right; right; right; right; right; right; right; left
    rw [← h.cj_cj χ, e]
  · right; right; right; right; right; right; right; right; left
    rw [← h.cj_cj χ, e, h.cj_cj]
  · right; right; right; right; right; right; right; right; right; right
    rw [← h.cj_cj χ, e, hS.cj_γ]

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
