module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersFirst

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

theorem odd_column_norm {ι : Type*} (B S : Finset ι) (hSB : S ⊆ B) (L : ι → ℤ)
    (hL : ∑ χ ∈ B, L χ * L χ = S.card) (hodd : ∀ χ ∈ S, Odd (L χ)) :
    (∀ χ ∈ S, L χ = 1 ∨ L χ = -1) ∧ ∀ χ ∈ B, χ ∉ S → L χ = 0 := by
  have hsplit : ∑ χ ∈ B \ S, L χ * L χ + ∑ χ ∈ S, L χ * L χ = S.card := by
    rw [Finset.sum_sdiff hSB]
    exact hL
  have hS1 : ∀ χ ∈ S, 1 ≤ L χ * L χ := fun χ hχ => by
    obtain ⟨k, hk⟩ := hodd χ hχ
    rw [hk]
    rcases le_or_gt 0 k with h | h <;> nlinarith
  have hge : (S.card : ℤ) ≤ ∑ χ ∈ S, L χ * L χ := by
    have := Finset.card_nsmul_le_sum S (fun χ => L χ * L χ) 1 hS1
    simpa using this
  have hnn : ∀ χ ∈ B \ S, 0 ≤ L χ * L χ := fun χ _ => mul_self_nonneg _
  have hrest : ∑ χ ∈ B \ S, L χ * L χ = 0 := by
    have := Finset.sum_nonneg hnn
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hrest
  have heq : ∑ χ ∈ S, L χ * L χ = ∑ χ ∈ S, (1 : ℤ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have hone : ∀ χ ∈ S, L χ * L χ = 1 := by
    have h' := (Finset.sum_eq_sum_iff_of_le hS1).mp heq.symm
    intro χ hχ
    exact (h' χ hχ).symm
  refine ⟨fun χ hχ => ?_, fun χ hχ hχS => ?_⟩
  · have h1 := hone χ hχ
    have h2 : (L χ - 1) * (L χ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left
      linarith
    · right
      linarith
  · exact zero_eq_mul_self.mp (hzero χ (Finset.mem_sdiff.mpr ⟨hχ, hχS⟩)).symm

namespace ColumnData

variable {ι : Type*} {D : ColumnData ι} {x y γ : ι} {δ : ℤ}

theorem Valid.c₂_pattern (h : D.Valid) (hE : D.ELabels x y) (hG : D.GammaData γ δ) :
    D.c₂ D.β₁ = -D.P D.β₁ ∧ D.c₂ x * D.P x + D.c₂ y * D.P y = 0 := by
  have hγη := (hG.ne_η h hE).1
  have h1 := h.c₂P
  rw [h.sum_c₂ hE hG, h.P_p, hG.P0] at h1
  have h2 := h.c₂L₁
  rw [h.sum_c₂ hE hG, h.L₁_p, h.β_L, hE.Lx, hE.Ly, h.L₁_off γ hG.mem hG.P0 hγη] at h2
  have hβ : D.c₂ D.β₁ * D.P D.β₁ = -1 := by linarith
  refine ⟨eq_neg_of_mul_eq_neg_one (h.P_unit h.β_mem h.β_P) hβ, by linarith⟩

theorem Valid.Q_zero_of_P (h : D.Valid) (hE : D.ELabels x y) (hG : D.GammaData γ δ)
    {χ : ι} (hχ : χ ∈ D.B) (hP : D.P χ ≠ 0) : D.Q χ = 0 := by
  by_contra hQ
  obtain ⟨n12, n22, n33, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩ := h.six_ne
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have hξ := (h.Q_ne_zero_iff hχ).mp hQ
  have hcB := h.cj_mem χ hχ
  have hPc : D.P (D.cj χ) ≠ 0 := by rwa [h.P_cj χ hχ]
  have hQc : D.Q (D.cj χ) ≠ 0 := by
    rw [h.Q_cj χ hχ]
    exact neg_ne_zero.mpr hQ
  have hξc := (h.Q_ne_zero_iff hcB).mp hQc
  have hreal : χ ≠ D.cj χ := by
    rcases hξ with rfl | rfl | rfl | rfl
    · exact n22
    · rw [h.cj_cj]
      exact n22.symm
    · exact n33
    · rw [h.cj_cj]
      exact n33.symm
  have hp₀ : ∀ ξ, D.Q ξ ≠ 0 → ξ ≠ D.p₀ := fun ξ hξQ e => hξQ (by rw [e, h.Q_p])
  have hηne : D.η₁ ≠ D.cj D.η₁ := by
    intro hη
    obtain ⟨hP1, hP1'⟩ := h.dich_eq hη
    have hsmall : ∀ ξ, (ξ = D.χ₂ ∨ ξ = D.cj D.χ₂ ∨ ξ = D.χ₃ ∨ ξ = D.cj D.χ₃) →
        D.χ₁ ≠ ξ ∧ D.cj D.χ₁ ≠ ξ := by
      rintro ξ (rfl | rfl | rfl | rfl) <;> exact ⟨by assumption, by assumption⟩
    obtain ⟨e1, e2⟩ := hsmall χ hξ
    obtain ⟨e3, e4⟩ := hsmall _ hξc
    have hp1 : D.χ₁ ≠ D.p₀ := fun e => n12 (by rw [e, h.cj_p])
    have hp1' : D.cj D.χ₁ ≠ D.p₀ := fun e => n12 (by
      have e' := h.cj_cj D.χ₁
      rw [e, h.cj_p] at e'
      rw [e, ← e'])
    have hsub : ({D.p₀, D.χ₁, D.cj D.χ₁, χ, D.cj χ} : Finset ι) ⊆ {D.p₀, D.β₁, x, y} := by
      intro ξ hξ'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hξ' ⊢
      rcases hξ' with rfl | rfl | rfl | rfl | rfl
      · left
        rfl
      · exact hE.cover _ h1B hP1
      · exact hE.cover _ (h.cj_mem _ h1B) hP1'
      · exact hE.cover _ hχ hP
      · exact hE.cover _ hcB hPc
    have hnd : [D.p₀, D.χ₁, D.cj D.χ₁, χ, D.cj χ].Nodup :=
      nodup_five_iff.mpr ⟨hp1.symm, hp1'.symm, (hp₀ χ hQ).symm, (hp₀ _ hQc).symm, n12, e1,
        e3, e2, e4, hreal⟩
    have hc := Finset.card_le_card hsub
    have hc5 : ({D.p₀, D.χ₁, D.cj D.χ₁, χ, D.cj χ} : Finset ι).card = 5 := by
      have e : ({D.p₀, D.χ₁, D.cj D.χ₁, χ, D.cj χ} : Finset ι) =
          [D.p₀, D.χ₁, D.cj D.χ₁, χ, D.cj χ].toFinset := by
        ext ξ
        simp
      rw [e, List.toFinset_card_of_nodup hnd]
      rfl
    have hc4 := Finset.card_le_four (a := D.p₀) (b := D.β₁) (c := x) (d := y)
    omega
  have hL13 := (h.dich_ne hηne).2
  have hPe : D.P (D.cj χ) = D.P χ := h.P_cj χ hχ
  have hLe : D.L₁ (D.cj χ) = D.L₁ χ := by rw [h.L₁_cj χ hχ, hL13 χ hχ hP]
  have hce : D.c₂ (D.cj χ) = D.c₂ χ := h.c₂_cj χ hχ
  obtain ⟨hcβ, hcxy⟩ := h.c₂_pattern hE hG
  have cx := sign_mul (hG.c₂_E _ hE.x_mem hE.Px) (h.P_unit hE.x_mem hE.Px)
  have hval : ∀ a ∈ ({D.β₁, x, y} : Finset ι), ∀ b ∈ ({D.β₁, x, y} : Finset ι), a ≠ b →
      D.P a = D.P b → D.L₁ a = D.L₁ b → D.c₂ a = D.c₂ b → False := by
    have hLβ := h.β_L
    have hLx := hE.Lx
    have hLy := hE.Ly
    have hPβ := h.β_P
    have hPx := hE.Px
    have hPy := hE.Py
    intro a ha b hb hab hP' hL' hc'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact hab rfl
      | (rw [hLβ, hLx] at hL'; exact hPx (by linarith))
      | (rw [hLβ, hLy] at hL'; exact hPy (by linarith))
      | (rw [← hP', ← hc'] at hcxy; omega)
      | (rw [hP', hc'] at hcxy; omega)
  have hmem : ∀ ξ ∈ D.B, D.P ξ ≠ 0 → D.Q ξ ≠ 0 → ξ ∈ ({D.β₁, x, y} : Finset ι) := by
    intro ξ hξB hξP hξQ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hE.cover ξ hξB hξP with e | e | e | e
    · exact absurd e (hp₀ ξ hξQ)
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  exact hval χ (hmem χ hχ hP hQ) _ (hmem _ hcB hPc hQc) hreal hPe.symm hLe.symm hce.symm

theorem Valid.Q_η (h : D.Valid) : D.Q D.η₁ = 0 := by
  by_contra hQ
  obtain ⟨n12, n22, n33, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩ := h.six_ne
  have hmem := (h.Q_ne_zero_iff h.η_mem).mp hQ
  by_cases hη : D.η₁ = D.cj D.η₁
  · rcases hmem with e | e | e | e
    · exact n22 (by rw [← e, ← hη])
    · exact n22 (by rw [← h.cj_cj D.χ₂, ← e, ← hη, ← hη])
    · exact n33 (by rw [← e, ← hη])
    · exact n33 (by rw [← h.cj_cj D.χ₃, ← e, ← hη, ← hη])
  · rcases (h.dich_ne hη).1 with ⟨e1, e1'⟩ | ⟨e1, e1'⟩
    · rcases hmem with e | e | e | e
      · exact a1 (by rw [e1, e])
      · exact a2 (by rw [e1, e])
      · exact a3 (by rw [e1, e])
      · exact a4 (by rw [e1, e])
    · rcases hmem with e | e | e | e
      · exact b1 (by rw [e1', e])
      · exact b2 (by rw [e1', e])
      · exact b3 (by rw [e1', e])
      · exact b4 (by rw [e1', e])

theorem Valid.card_EJ (h : D.Valid) (hE : D.ELabels x y) (hG : D.GammaData γ δ) :
    (D.B.filter (fun χ => D.P χ ≠ 0 ∨ D.Q χ ≠ 0)).card = 8 := by
  obtain ⟨n12, n22, n33, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩ := h.six_ne
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have hJ : D.B.filter (fun χ => D.Q χ ≠ 0) = {D.χ₂, D.cj D.χ₂, D.χ₃, D.cj D.χ₃} := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hχ, hQ⟩
      exact (h.Q_ne_zero_iff hχ).mp hQ
    · intro hχ
      have hχB : χ ∈ D.B := by
        rcases hχ with rfl | rfl | rfl | rfl
        exacts [h2B, h.cj_mem _ h2B, h3B, h.cj_mem _ h3B]
      exact ⟨hχB, (h.Q_ne_zero_iff hχB).mpr hχ⟩
  have hJc : (D.B.filter (fun χ => D.Q χ ≠ 0)).card = 4 := by
    rw [hJ]
    have e : ({D.χ₂, D.cj D.χ₂, D.χ₃, D.cj D.χ₃} : Finset ι) =
        [D.χ₂, D.cj D.χ₂, D.χ₃, D.cj D.χ₃].toFinset := by
      ext ξ
      simp
    rw [e, List.toFinset_card_of_nodup (nodup_four_iff.mpr ⟨n22, c1, c2, c3, c4, n33⟩)]
    rfl
  rw [Finset.filter_or, Finset.card_union_of_disjoint, h.E_card, hJc]
  rw [Finset.disjoint_filter]
  intro χ hχ hP hQ
  exact hQ (h.Q_zero_of_P hE hG hχ hP)

theorem Valid.L₂_structure (h : D.Valid) (hE : D.ELabels x y) (hG : D.GammaData γ δ) :
    D.η₁ ≠ D.cj D.η₁ ∧
    D.L₂ D.β₁ = -D.P D.β₁ ∧ D.L₂ x = D.P x ∧ D.L₂ y = D.P y ∧
    D.L₃ D.β₁ = -D.P D.β₁ ∧ D.L₃ x = D.P x ∧ D.L₃ y = D.P y ∧
    (∀ χ ∈ D.B, D.Q χ ≠ 0 → D.L₂ χ = 1 ∨ D.L₂ χ = -1) ∧
    (∀ χ ∈ D.B, D.P χ = 0 → D.Q χ = 0 → D.L₂ χ = 0) := by
  set S := D.B.filter (fun χ => D.P χ ≠ 0 ∨ D.Q χ ≠ 0) with hS
  have hSB : S ⊆ D.B := Finset.filter_subset _ _
  have hodd : ∀ χ ∈ S, Odd (D.L₂ χ) := by
    intro χ hχ
    rw [hS, Finset.mem_filter] at hχ
    obtain ⟨hχB, hPQ⟩ := hχ
    obtain ⟨k, hk⟩ := h.L₂_par χ hχB
    by_cases hP : D.P χ = 0
    · have hQ : D.Q χ ≠ 0 := hPQ.resolve_left (not_not.mpr hP)
      rcases h.Q_val χ hχB with h0 | h1 | h1
      · exact absurd h0 hQ
      · exact ⟨k, by rw [hk, hP, h1]; ring⟩
      · exact ⟨k - 1, by rw [hk, hP, h1]; ring⟩
    · have hQ : D.Q χ = 0 := h.Q_zero_of_P hE hG hχB hP
      rcases h.P_unit hχB hP with h1 | h1
      · exact ⟨k, by rw [hk, hQ, h1]; ring⟩
      · exact ⟨k - 1, by rw [hk, hQ, h1]; ring⟩
  have hnorm : ∑ χ ∈ D.B, D.L₂ χ * D.L₂ χ = S.card := by
    rw [h.L₂L₂, hS, h.card_EJ hE hG]
    norm_num
  obtain ⟨hunit, hzero⟩ := odd_column_norm D.B S hSB D.L₂ hnorm hodd
  have hL₂E : ∀ χ ∈ D.B, D.P χ ≠ 0 → D.L₂ χ = 1 ∨ D.L₂ χ = -1 := fun χ hχ hP =>
    hunit χ (by rw [hS, Finset.mem_filter]; exact ⟨hχ, Or.inl hP⟩)
  have hL₂J : ∀ χ ∈ D.B, D.Q χ ≠ 0 → D.L₂ χ = 1 ∨ D.L₂ χ = -1 := fun χ hχ hQ =>
    hunit χ (by rw [hS, Finset.mem_filter]; exact ⟨hχ, Or.inr hQ⟩)
  have hL₂0 : ∀ χ ∈ D.B, D.P χ = 0 → D.Q χ = 0 → D.L₂ χ = 0 := by
    intro χ hχ hP hQ
    refine hzero χ hχ ?_
    rw [hS, Finset.mem_filter]
    rintro ⟨-, h' | h'⟩ <;> contradiction
  have hL₂η : D.L₂ D.η₁ = 0 := hL₂0 _ h.η_mem h.η_P h.Q_η
  have hL₂η' : D.L₂ (D.cj D.η₁) = 0 := by rw [h.L₂_cj _ h.η_mem, hL₂η]
  have e12 := h.L₁L₂
  rw [h.sum_L₁ hE, h.L₂_p, hL₂η] at e12
  have sβ := sign_mul (h.P_unit h.β_mem h.β_P) (hL₂E _ h.β_mem h.β_P)
  have sx := sign_mul (h.P_unit hE.x_mem hE.Px) (hL₂E _ hE.x_mem hE.Px)
  have sy := sign_mul (h.P_unit hE.y_mem hE.Py) (hL₂E _ hE.y_mem hE.Py)
  have hk : D.P D.β₁ * D.L₂ D.β₁ = -1 ∧ D.P x * D.L₂ x = 1 ∧ D.P y * D.L₂ y = 1 := by
    rcases sβ with e | e <;> rcases sx with e' | e' <;> rcases sy with e'' | e'' <;> omega
  have hL₂β : D.L₂ D.β₁ = -D.P D.β₁ := by
    rw [mul_comm] at hk
    exact eq_neg_of_mul_eq_neg_one (h.P_unit h.β_mem h.β_P) hk.1
  have hL₂x : D.L₂ x = D.P x := by
    have e := hk.2.1
    rw [mul_comm] at e
    exact eq_of_mul_eq_one (h.P_unit hE.x_mem hE.Px) e
  have hL₂y : D.L₂ y = D.P y := by
    have e := hk.2.2
    rw [mul_comm] at e
    exact eq_of_mul_eq_one (h.P_unit hE.y_mem hE.Py) e
  have e23 : ∑ χ ∈ D.B, D.L₃ χ * D.L₂ χ = 4 := by
    rw [← h.L₂L₃]
    exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  rw [h.sum_L₃ hE, h.L₂_p, hL₂η'] at e23
  have tβ := sign_mul (h.L₃_E h.β_mem h.β_P) (hL₂E _ h.β_mem h.β_P)
  have tx := sign_mul (h.L₃_E hE.x_mem hE.Px) (hL₂E _ hE.x_mem hE.Px)
  have ty := sign_mul (h.L₃_E hE.y_mem hE.Py) (hL₂E _ hE.y_mem hE.Py)
  have ht : D.L₃ D.β₁ * D.L₂ D.β₁ = 1 ∧ D.L₃ x * D.L₂ x = 1 ∧ D.L₃ y * D.L₂ y = 1 := by
    rcases tβ with e | e <;> rcases tx with e' | e' <;> rcases ty with e'' | e'' <;> omega
  have hL₃β : D.L₃ D.β₁ = -D.P D.β₁ := by
    rw [← hL₂β]
    exact eq_of_mul_eq_one (hL₂E _ h.β_mem h.β_P) ht.1
  have hL₃x : D.L₃ x = D.P x := by
    rw [← hL₂x]
    exact eq_of_mul_eq_one (hL₂E _ hE.x_mem hE.Px) ht.2.1
  have hL₃y : D.L₃ y = D.P y := by
    rw [← hL₂y]
    exact eq_of_mul_eq_one (hL₂E _ hE.y_mem hE.Py) ht.2.2
  have e13 := h.L₁L₃
  rw [h.sum_L₁ hE, h.L₃_p, hL₃β, hL₃x, hL₃y] at e13
  have hP2 : ∀ χ ∈ D.B, D.P χ ≠ 0 → D.P χ * D.P χ = 1 := fun χ hχ hP =>
    sign_mul_self (h.P_unit hχ hP)
  have hβ2 := hP2 _ h.β_mem h.β_P
  have hx2 := hP2 _ hE.x_mem hE.Px
  have hy2 := hP2 _ hE.y_mem hE.Py
  have hη3 : D.ε * D.L₃ D.η₁ = 0 := by linarith
  have hηne : D.η₁ ≠ D.cj D.η₁ := by
    intro e
    rw [e, h.L₃_η] at hη3
    rcases h.ε_val with h' | h' <;> rw [h'] at hη3 <;> norm_num at hη3
  exact ⟨hηne, hL₂β, hL₂x, hL₂y, hL₃β, hL₃x, hL₃y, hL₂J, hL₂0⟩

@[expose] def list11 (D : ColumnData ι) (κ lam γ : ι) : List ι :=
  [D.p₀, D.β₁, κ, lam, D.χ₂, D.cj D.χ₂, D.χ₃, D.cj D.χ₃, D.η₁, D.cj D.η₁, γ]

structure Stage1 (D : ColumnData ι) (κ lam γ : ι) (pβ pκ pl δ q₂ q₃ : ℤ) : Prop where
  κ_mem : κ ∈ D.B
  lam_mem : lam ∈ D.B
  γ_mem : γ ∈ D.B
  pβ_val : pβ = 1 ∨ pβ = -1
  pκ_val : pκ = 1 ∨ pκ = -1
  pl_val : pl = 1 ∨ pl = -1
  δ_val : δ = 1 ∨ δ = -1
  q₂_val : q₂ = 1 ∨ q₂ = -1
  q₃_val : q₃ = 1 ∨ q₃ = -1
  η_ne : D.η₁ ≠ D.cj D.η₁
  large : (D.χ₁ = D.η₁ ∧ D.cj D.χ₁ = D.cj D.η₁) ∨ (D.χ₁ = D.cj D.η₁ ∧ D.cj D.χ₁ = D.η₁)
  cj_β : D.cj D.β₁ = D.β₁
  cj_κ : D.cj κ = κ
  cj_lam : D.cj lam = lam
  cj_γ : D.cj γ = γ
  row_β : D.P D.β₁ = pβ ∧ D.L₁ D.β₁ = -pβ ∧ D.L₂ D.β₁ = -pβ ∧ D.L₃ D.β₁ = -pβ ∧
    D.c₂ D.β₁ = -pβ
  row_κ : D.P κ = pκ ∧ D.L₁ κ = pκ ∧ D.L₂ κ = pκ ∧ D.L₃ κ = pκ ∧ D.c₂ κ = pκ
  row_lam : D.P lam = pl ∧ D.L₁ lam = pl ∧ D.L₂ lam = pl ∧ D.L₃ lam = pl ∧ D.c₂ lam = -pl
  row_χ₂ : D.P D.χ₂ = 0 ∧ D.L₁ D.χ₂ = 0 ∧ D.L₂ D.χ₂ = q₂ ∧ D.L₃ D.χ₂ = 0 ∧ D.c₂ D.χ₂ = 0
  row_χ₂' : D.P (D.cj D.χ₂) = 0 ∧ D.L₁ (D.cj D.χ₂) = 0 ∧ D.L₂ (D.cj D.χ₂) = q₂ ∧
    D.L₃ (D.cj D.χ₂) = 0 ∧ D.c₂ (D.cj D.χ₂) = 0
  row_χ₃ : D.P D.χ₃ = 0 ∧ D.L₁ D.χ₃ = 0 ∧ D.L₂ D.χ₃ = q₃ ∧ D.L₃ D.χ₃ = 0 ∧ D.c₂ D.χ₃ = 0
  row_χ₃' : D.P (D.cj D.χ₃) = 0 ∧ D.L₁ (D.cj D.χ₃) = 0 ∧ D.L₂ (D.cj D.χ₃) = q₃ ∧
    D.L₃ (D.cj D.χ₃) = 0 ∧ D.c₂ (D.cj D.χ₃) = 0
  row_η : D.P D.η₁ = 0 ∧ D.L₁ D.η₁ = 2 * D.ε ∧ D.L₂ D.η₁ = 0 ∧ D.L₃ D.η₁ = 0 ∧
    D.c₂ D.η₁ = 0
  row_η' : D.P (D.cj D.η₁) = 0 ∧ D.L₁ (D.cj D.η₁) = 0 ∧ D.L₂ (D.cj D.η₁) = 0 ∧
    D.L₃ (D.cj D.η₁) = 2 * D.ε ∧ D.c₂ (D.cj D.η₁) = 0
  row_γ : D.P γ = 0 ∧ D.L₁ γ = 0 ∧ D.L₂ γ = 0 ∧ D.L₃ γ = 0 ∧ D.c₂ γ = 2 * δ
  Q_E : D.Q D.β₁ = 0 ∧ D.Q κ = 0 ∧ D.Q lam = 0
  Q_H : D.Q D.η₁ = 0 ∧ D.Q (D.cj D.η₁) = 0 ∧ D.Q γ = 0
  Q_J : D.Q D.χ₂ ≠ 0 ∧ D.Q (D.cj D.χ₂) ≠ 0 ∧ D.Q D.χ₃ ≠ 0 ∧ D.Q (D.cj D.χ₃) ≠ 0
  nodup : (list11 D κ lam γ).Nodup
  rest : ∀ χ ∈ D.B, χ ∉ list11 D κ lam γ → D.P χ = 0 ∧ D.Q χ = 0 ∧ D.L₁ χ = 0 ∧
    D.L₂ χ = 0 ∧ D.L₃ χ = 0 ∧ D.c₂ χ = 0 ∧ D.c₁ χ = D.c₃ χ

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
