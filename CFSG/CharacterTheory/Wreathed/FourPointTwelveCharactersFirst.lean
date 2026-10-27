module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersData
public import CFSG.CharacterTheory.Wreathed.FourPointThreePairsSupport

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

theorem sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem sign_mul_self {a : ℤ} (ha : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases ha with rfl | rfl <;> norm_num

theorem eq_of_mul_eq_one {a b : ℤ} (hb : b = 1 ∨ b = -1) (h : a * b = 1) : a = b := by
  rcases hb with rfl | rfl <;> linarith

theorem eq_neg_of_mul_eq_neg_one {a b : ℤ} (hb : b = 1 ∨ b = -1) (h : a * b = -1) : a = -b := by
  rcases hb with rfl | rfl <;> linarith

theorem gamma_aux {cβ cx cy lβ lx ly δ ε d₀ dβ dx dy dγ : ℤ}
    (hcβ : cβ = 1 ∨ cβ = -1) (hcx : cx = 1 ∨ cx = -1) (hcy : cy = 1 ∨ cy = -1)
    (hlβ : lβ = 1 ∨ lβ = -1) (hlx : lx = 1 ∨ lx = -1) (hly : ly = 1 ∨ ly = -1)
    (hδ : δ = 1 ∨ δ = -1) (hε : ε = 1 ∨ ε = -1)
    (h1 : 1 * -1 + cβ * lβ + cx * lx + cy * ly + 2 * δ * (2 * ε) = 0)
    (h2 : 1 * d₀ + cβ * dβ + cx * dx + cy * dy + 2 * δ * dγ = 0)
    (h3 : -1 * d₀ + lβ * dβ + lx * dx + ly * dy + 2 * ε * dγ = 0) (hdγ : 1 ≤ dγ) : False := by
  have pβ := sign_mul hcβ hlβ
  have px := sign_mul hcx hlx
  have py := sign_mul hcy hly
  have pw := sign_mul hδ hε
  have h1' : -1 + cβ * lβ + cx * lx + cy * ly + 4 * (δ * ε) = 0 := by linarith
  have key : cβ * lβ = -1 ∧ cx * lx = -1 ∧ cy * ly = -1 ∧ δ * ε = 1 := by
    rcases pβ with e | e <;> rcases px with e' | e' <;> rcases py with e'' | e'' <;>
      rcases pw with ew | ew <;> omega
  obtain ⟨kβ, kx, ky, kw⟩ := key
  have eβ := eq_neg_of_mul_eq_neg_one hlβ kβ
  have ex := eq_neg_of_mul_eq_neg_one hlx kx
  have ey := eq_neg_of_mul_eq_neg_one hly ky
  have eδ := eq_of_mul_eq_one hε kw
  subst eβ ex ey
  rw [eδ] at h2
  have h4 : 4 * ε * dγ = 0 := by linarith
  rcases hε with rfl | rfl <;> linarith

namespace ColumnData

variable {ι : Type*} {D : ColumnData ι}

structure ELabels (D : ColumnData ι) (x y : ι) : Prop where
  nodup : [D.p₀, D.β₁, x, y].Nodup
  x_mem : x ∈ D.B
  y_mem : y ∈ D.B
  Px : D.P x ≠ 0
  Py : D.P y ≠ 0
  Lx : D.L₁ x = D.P x
  Ly : D.L₁ y = D.P y
  cover : ∀ χ ∈ D.B, D.P χ ≠ 0 → χ = D.p₀ ∨ χ = D.β₁ ∨ χ = x ∨ χ = y

theorem Valid.P_unit (h : D.Valid) {χ : ι} (hχ : χ ∈ D.B) (hP : D.P χ ≠ 0) :
    D.P χ = 1 ∨ D.P χ = -1 :=
  (h.P_val χ hχ).resolve_left hP

theorem Valid.exists_ELabels (h : D.Valid) : ∃ x y : ι, D.ELabels x y := by
  set E := D.B.filter (fun χ => D.P χ ≠ 0) with hE
  have hm : E.filter (fun χ => ¬ D.L₁ χ = D.P χ) = {D.p₀, D.β₁} := by
    ext χ
    simp only [hE, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hχB, hPχ⟩, hL⟩
      refine h.Eminus χ hχB hPχ ?_
      rcases h.L₁_E χ hχB hPχ with h1 | h1 <;>
        rcases h.P_val χ hχB with h2 | h2 | h2 <;> omega
    · rintro (rfl | rfl)
      · refine ⟨⟨h.p_mem, by rw [h.P_p]; norm_num⟩, by rw [h.L₁_p, h.P_p]; norm_num⟩
      · refine ⟨⟨h.β_mem, h.β_P⟩, fun hL => h.β_P ?_⟩
        rw [h.β_L] at hL
        linarith
  have hcard : (E.filter (fun χ => D.L₁ χ = D.P χ)).card = 2 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := E) (fun χ => D.L₁ χ = D.P χ)
    rw [hm, Finset.card_pair h.β_ne.symm, h.E_card] at h1
    omega
  obtain ⟨x, y, hxy, hxyE⟩ := Finset.card_eq_two.mp hcard
  have hx : x ∈ E.filter (fun χ => D.L₁ χ = D.P χ) := by
    rw [hxyE]
    simp
  have hy : y ∈ E.filter (fun χ => D.L₁ χ = D.P χ) := by
    rw [hxyE]
    simp
  simp only [hE, Finset.mem_filter] at hx hy
  obtain ⟨⟨hxB, hPx⟩, hLx⟩ := hx
  obtain ⟨⟨hyB, hPy⟩, hLy⟩ := hy
  have hne : ∀ χ, D.L₁ χ = D.P χ → D.P χ ≠ 0 → χ ≠ D.p₀ ∧ χ ≠ D.β₁ := by
    intro χ hL hP
    constructor
    · rintro rfl
      rw [h.L₁_p, h.P_p] at hL
      norm_num at hL
    · rintro rfl
      rw [h.β_L] at hL
      exact hP (by linarith)
  obtain ⟨hx0, hxβ⟩ := hne x hLx hPx
  obtain ⟨hy0, hyβ⟩ := hne y hLy hPy
  refine ⟨x, y, ⟨?_, hxB, hyB, hPx, hPy, hLx, hLy, ?_⟩⟩
  · simp [h.β_ne.symm, hx0.symm, hy0.symm, hxβ.symm, hyβ.symm, hxy]
  · intro χ hχB hPχ
    by_cases hL : D.L₁ χ = D.P χ
    · have hmem : χ ∈ E.filter (fun χ => D.L₁ χ = D.P χ) := by
        simp only [hE, Finset.mem_filter]
        exact ⟨⟨hχB, hPχ⟩, hL⟩
      rw [hxyE] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl <;> simp
    · have hmem : χ ∈ E.filter (fun χ => ¬ D.L₁ χ = D.P χ) := by
        simp only [hE, Finset.mem_filter]
        exact ⟨⟨hχB, hPχ⟩, hL⟩
      rw [hm] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl <;> simp

theorem Valid.c₁₃_values (h : D.Valid) : D.c₁ D.χ₂ - D.c₃ D.χ₂ = 1 ∧
    D.c₁ D.χ₃ - D.c₃ D.χ₃ = 1 ∧ D.c₁ (D.cj D.χ₂) - D.c₃ (D.cj D.χ₂) = -1 ∧
    D.c₁ (D.cj D.χ₃) - D.c₃ (D.cj D.χ₃) = -1 ∧
    ∀ χ ∈ D.B, χ ≠ D.χ₂ → χ ≠ D.cj D.χ₂ → χ ≠ D.χ₃ → χ ≠ D.cj D.χ₃ → D.c₁ χ = D.c₃ χ := by
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have e2 := h.c₁₃ _ h2B
  have e3 := h.c₁₃ _ h3B
  have e2' := h.c₁₃ _ (h.cj_mem _ h2B)
  have e3' := h.c₁₃ _ (h.cj_mem _ h3B)
  rw [h.Uim₂, h.Tim₂] at e2
  rw [h.Uim₃, h.Tim₃] at e3
  rw [h.Uim_cj _ h2B, h.Tim_cj _ h2B, h.Uim₂, h.Tim₂] at e2'
  rw [h.Uim_cj _ h3B, h.Tim_cj _ h3B, h.Uim₃, h.Tim₃] at e3'
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro χ hχ h2 h2' h3 h3'
  have e := h.c₁₃ χ hχ
  by_cases h1 : χ = D.χ₁
  · subst h1
    rw [h.Uim₁, h.Tim₁] at e
    omega
  by_cases h1' : χ = D.cj D.χ₁
  · subst h1'
    rw [h.Uim_cj _ h1B, h.Tim_cj _ h1B, h.Uim₁, h.Tim₁] at e
    omega
  obtain ⟨hT, hU⟩ := h.off_six χ hχ h1 h1' h2 h2' h3 h3'
  rw [hT, hU] at e
  omega

theorem Valid.Q_ne_zero_iff (h : D.Valid) {χ : ι} (hχ : χ ∈ D.B) :
    D.Q χ ≠ 0 ↔ χ = D.χ₂ ∨ χ = D.cj D.χ₂ ∨ χ = D.χ₃ ∨ χ = D.cj D.χ₃ := by
  obtain ⟨v2, v3, v2', v3', v0⟩ := h.c₁₃_values
  obtain ⟨k, hk⟩ := h.c₁₃_par χ hχ
  have hQ := h.Q_val χ hχ
  constructor
  · intro hQ0
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨n2, n2', n3, n3'⟩ := hn
    have := v0 χ hχ n2 n2' n3 n3'
    omega
  · rintro (rfl | rfl | rfl | rfl) <;> omega

theorem Valid.six_ne (h : D.Valid) : D.χ₁ ≠ D.cj D.χ₁ ∧ D.χ₂ ≠ D.cj D.χ₂ ∧ D.χ₃ ≠ D.cj D.χ₃ ∧
    D.χ₁ ≠ D.χ₂ ∧ D.χ₁ ≠ D.cj D.χ₂ ∧ D.χ₁ ≠ D.χ₃ ∧ D.χ₁ ≠ D.cj D.χ₃ ∧
    D.cj D.χ₁ ≠ D.χ₂ ∧ D.cj D.χ₁ ≠ D.cj D.χ₂ ∧ D.cj D.χ₁ ≠ D.χ₃ ∧ D.cj D.χ₁ ≠ D.cj D.χ₃ ∧
    D.χ₂ ≠ D.χ₃ ∧ D.χ₂ ≠ D.cj D.χ₃ ∧ D.cj D.χ₂ ≠ D.χ₃ ∧ D.cj D.χ₂ ≠ D.cj D.χ₃ := by
  have hn := h.six_nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hn
  tauto

theorem Valid.L₃_eq (h : D.Valid) {χ : ι} (hχ : χ ∈ D.B) : D.L₃ χ = D.L₁ (D.cj χ) := by
  have e := h.L₃_cj (D.cj χ) (h.cj_mem χ hχ)
  rwa [h.cj_cj] at e

theorem Valid.L₃_E (h : D.Valid) {χ : ι} (hχ : χ ∈ D.B) (hP : D.P χ ≠ 0) :
    D.L₃ χ = 1 ∨ D.L₃ χ = -1 := by
  rw [h.L₃_eq hχ]
  exact h.L₁_E _ (h.cj_mem χ hχ) (by rwa [h.P_cj χ hχ])

theorem Valid.L₃_off (h : D.Valid) {χ : ι} (hχ : χ ∈ D.B) (hP : D.P χ = 0)
    (hne : χ ≠ D.cj D.η₁) : D.L₃ χ = 0 := by
  rw [h.L₃_eq hχ]
  refine h.L₁_off _ (h.cj_mem χ hχ) (by rwa [h.P_cj χ hχ]) fun he => hne ?_
  rw [← he, h.cj_cj]

theorem Valid.L₃_η (h : D.Valid) : D.L₃ (D.cj D.η₁) = 2 * D.ε := by
  rw [h.L₃_cj _ h.η_mem, h.L₁_η]

structure GammaData (D : ColumnData ι) (γ : ι) (δ : ℤ) : Prop where
  mem : γ ∈ D.B
  P0 : D.P γ = 0
  cj_eq : D.cj γ = γ
  δ_val : δ = 1 ∨ δ = -1
  c₂γ : D.c₂ γ = 2 * δ
  c₂_off : ∀ χ ∈ D.B, D.P χ = 0 → χ ≠ γ → D.c₂ χ = 0
  c₂_E : ∀ χ ∈ D.B, D.P χ ≠ 0 → D.c₂ χ = 1 ∨ D.c₂ χ = -1

theorem Valid.exists_GammaData (h : D.Valid) : ∃ γ δ, D.GammaData γ δ := by
  set E := D.B.filter (fun χ => D.P χ ≠ 0) with hE
  have hEB : E ⊆ D.B := Finset.filter_subset _ _
  have hsq : ∑ χ ∈ D.B, D.c₂ χ ^ 2 = 8 := by
    rw [← h.c₂c₂]
    exact Finset.sum_congr rfl fun χ _ => sq _
  have hodd : ∀ χ ∈ E, Odd (D.c₂ χ) := by
    intro χ hχ
    rw [hE, Finset.mem_filter] at hχ
    obtain ⟨k, hk⟩ := h.c₂_par χ hχ.1
    rcases h.P_unit hχ.1 hχ.2 with h1 | h1 <;> rw [h1] at hk
    · exact ⟨k, by rw [hk]; ring⟩
    · exact ⟨k - 1, by rw [hk]; ring⟩
  have hP0 : ∀ χ ∈ D.B, χ ∉ E → D.P χ = 0 := by
    intro χ hχ hχE
    by_contra hP
    exact hχE (by rw [hE, Finset.mem_filter]; exact ⟨hχ, hP⟩)
  have heven : ∀ χ ∈ D.B, χ ∉ E → Even (D.c₂ χ) := by
    intro χ hχ hχE
    obtain ⟨k, hk⟩ := h.c₂_par χ hχ
    exact ⟨k, by rw [hk, hP0 χ hχ hχE]; ring⟩
  obtain ⟨hunit, γ, hγB, hγE, hγ2, hzero⟩ :=
    FourPointThreePairs.norm_eight_odd_column D.B E hEB h.E_card D.c₂ hsq hodd heven
  have hPγ : D.P γ = 0 := hP0 γ hγB hγE
  have hzero' : ∀ χ ∈ D.B, D.P χ = 0 → χ ≠ γ → D.c₂ χ = 0 := by
    intro χ hχ hP hne
    refine hzero χ hχ ?_ hne
    rw [hE, Finset.mem_filter]
    exact fun h' => h'.2 hP
  have hE' : ∀ χ ∈ D.B, D.P χ ≠ 0 → D.c₂ χ = 1 ∨ D.c₂ χ = -1 := fun χ hχ hP =>
    hunit χ (by rw [hE, Finset.mem_filter]; exact ⟨hχ, hP⟩)
  have hcjγ : D.cj γ = γ := by
    by_contra hne
    have h0 := hzero' (D.cj γ) (h.cj_mem γ hγB) (by rw [h.P_cj γ hγB, hPγ]) hne
    rw [h.c₂_cj γ hγB] at h0
    rcases hγ2 with h2 | h2 <;> omega
  rcases hγ2 with h2 | h2
  · exact ⟨γ, 1, hγB, hPγ, hcjγ, Or.inl rfl, by rw [h2]; norm_num, hzero', hE'⟩
  · exact ⟨γ, -1, hγB, hPγ, hcjγ, Or.inr rfl, by rw [h2]; norm_num, hzero', hE'⟩

variable {x y : ι}

theorem ELabels.nodup_η (h : D.Valid) (hE : D.ELabels x y) :
    [D.p₀, D.β₁, x, y, D.η₁].Nodup ∧ [D.p₀, D.β₁, x, y, D.cj D.η₁].Nodup := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := nodup_four_iff.mp hE.nodup
  have hPη' : D.P (D.cj D.η₁) = 0 := by rw [h.P_cj _ h.η_mem, h.η_P]
  have hne : ∀ χ, D.P χ = 0 → χ ≠ D.p₀ ∧ χ ≠ D.β₁ ∧ χ ≠ x ∧ χ ≠ y := by
    intro χ hP
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · rw [h.P_p] at hP
      norm_num at hP
    · exact h.β_P hP
    · exact hE.Px hP
    · exact hE.Py hP
  obtain ⟨a1, a2, a3, a4⟩ := hne _ h.η_P
  obtain ⟨b1, b2, b3, b4⟩ := hne _ hPη'
  exact ⟨nodup_five_iff.mpr ⟨n1, n2, n3, a1.symm, n4, n5, a2.symm, n6, a3.symm, a4.symm⟩,
    nodup_five_iff.mpr ⟨n1, n2, n3, b1.symm, n4, n5, b2.symm, n6, b3.symm, b4.symm⟩⟩

theorem ELabels.P_zero (hE : D.ELabels x y) {χ : ι} (hχ : χ ∈ D.B) (h0 : χ ≠ D.p₀)
    (hβ : χ ≠ D.β₁) (hx : χ ≠ x) (hy : χ ≠ y) : D.P χ = 0 := by
  by_contra hP
  rcases hE.cover χ hχ hP with h' | h' | h' | h' <;> contradiction

theorem Valid.sum_P (h : D.Valid) (hE : D.ELabels x y) (f : ι → ℤ) :
    ∑ χ ∈ D.B, D.P χ * f χ = f D.p₀ + D.P D.β₁ * f D.β₁ + D.P x * f x + D.P y * f y := by
  rw [sum_eq_sum_of_vanish D.B {D.p₀, D.β₁, x, y} _ ?_ ?_, sum_four hE.nodup, h.P_p, one_mul]
  · intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl | rfl
    exacts [h.p_mem, h.β_mem, hE.x_mem, hE.y_mem]
  · intro χ hχ hS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hS
    rw [hE.P_zero hχ hS.1 hS.2.1 hS.2.2.1 hS.2.2.2, zero_mul]

theorem Valid.sum_L₁ (h : D.Valid) (hE : D.ELabels x y) (f : ι → ℤ) :
    ∑ χ ∈ D.B, D.L₁ χ * f χ = -f D.p₀ - D.P D.β₁ * f D.β₁ + D.P x * f x + D.P y * f y +
      2 * D.ε * f D.η₁ := by
  rw [sum_eq_sum_of_vanish D.B {D.p₀, D.β₁, x, y, D.η₁} _ ?_ ?_,
    sum_five (hE.nodup_η h).1, h.L₁_p, h.β_L, hE.Lx, hE.Ly, h.L₁_η]
  · ring
  · intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl | rfl | rfl
    exacts [h.p_mem, h.β_mem, hE.x_mem, hE.y_mem, h.η_mem]
  · intro χ hχ hS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hS
    rw [h.L₁_off χ hχ (hE.P_zero hχ hS.1 hS.2.1 hS.2.2.1 hS.2.2.2.1) hS.2.2.2.2, zero_mul]

theorem Valid.sum_L₃ (h : D.Valid) (hE : D.ELabels x y) (f : ι → ℤ) :
    ∑ χ ∈ D.B, D.L₃ χ * f χ = -f D.p₀ + D.L₃ D.β₁ * f D.β₁ + D.L₃ x * f x + D.L₃ y * f y +
      2 * D.ε * f (D.cj D.η₁) := by
  rw [sum_eq_sum_of_vanish D.B {D.p₀, D.β₁, x, y, D.cj D.η₁} _ ?_ ?_,
    sum_five (hE.nodup_η h).2, h.L₃_p, h.L₃_η]
  · ring
  · intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl | rfl | rfl
    exacts [h.p_mem, h.β_mem, hE.x_mem, hE.y_mem, h.cj_mem _ h.η_mem]
  · intro χ hχ hS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hS
    rw [h.L₃_off hχ (hE.P_zero hχ hS.1 hS.2.1 hS.2.2.1 hS.2.2.2.1) hS.2.2.2.2, zero_mul]

variable {γ : ι} {δ : ℤ}

theorem GammaData.nodup (h : D.Valid) (hE : D.ELabels x y) (hG : D.GammaData γ δ) :
    [D.p₀, D.β₁, x, y, γ].Nodup := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := nodup_four_iff.mp hE.nodup
  have a1 : γ ≠ D.p₀ := by
    rintro rfl
    have := hG.P0
    rw [h.P_p] at this
    norm_num at this
  have a2 : γ ≠ D.β₁ := fun e => h.β_P (e ▸ hG.P0)
  have a3 : γ ≠ x := fun e => hE.Px (e ▸ hG.P0)
  have a4 : γ ≠ y := fun e => hE.Py (e ▸ hG.P0)
  exact nodup_five_iff.mpr ⟨n1, n2, n3, a1.symm, n4, n5, a2.symm, n6, a3.symm, a4.symm⟩

theorem Valid.sum_c₂ (h : D.Valid) (hE : D.ELabels x y) (hG : D.GammaData γ δ) (f : ι → ℤ) :
    ∑ χ ∈ D.B, D.c₂ χ * f χ = f D.p₀ + D.c₂ D.β₁ * f D.β₁ + D.c₂ x * f x + D.c₂ y * f y +
      2 * δ * f γ := by
  rw [sum_eq_sum_of_vanish D.B {D.p₀, D.β₁, x, y, γ} _ ?_ ?_, sum_five (hG.nodup h hE),
    h.c₂_p, hG.c₂γ, one_mul]
  · intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl | rfl | rfl
    exacts [h.p_mem, h.β_mem, hE.x_mem, hE.y_mem, hG.mem]
  · intro χ hχ hS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hS
    rw [hG.c₂_off χ hχ (hE.P_zero hχ hS.1 hS.2.1 hS.2.2.1 hS.2.2.2.1) hS.2.2.2.2, zero_mul]

theorem GammaData.ne_η (h : D.Valid) (hE : D.ELabels x y) (hG : D.GammaData γ δ) :
    γ ≠ D.η₁ ∧ γ ≠ D.cj D.η₁ := by
  have hβ := h.P_unit h.β_mem h.β_P
  have hx := h.P_unit hE.x_mem hE.Px
  have hy := h.P_unit hE.y_mem hE.Py
  have cβ := hG.c₂_E _ h.β_mem h.β_P
  have cx := hG.c₂_E _ hE.x_mem hE.Px
  have cy := hG.c₂_E _ hE.y_mem hE.Py
  have h2 := h.c₂d
  rw [h.sum_c₂ hE hG] at h2
  have hdγ := h.d_pos γ hG.mem
  constructor
  · rintro rfl
    have h1 := h.c₂L₁
    rw [h.sum_c₂ hE hG, h.L₁_p, h.β_L, hE.Lx, hE.Ly, h.L₁_η] at h1
    have h3 := h.L₁d
    rw [h.sum_L₁ hE] at h3
    exact gamma_aux cβ cx cy (lβ := -D.P D.β₁) (lx := D.P x) (ly := D.P y)
      (d₀ := D.d D.p₀) (dβ := D.d D.β₁) (dx := D.d x) (dy := D.d y)
      (by rcases hβ with e | e <;> rw [e] <;> norm_num) hx hy hG.δ_val h.ε_val
      (by linarith) (by linarith) (by linarith) hdγ
  · intro e
    have h1 := h.c₂L₃
    rw [h.sum_c₂ hE hG, h.L₃_p, e, h.L₃_η] at h1
    have h3 := h.L₃d
    rw [h.sum_L₃ hE, ← e] at h3
    exact gamma_aux cβ cx cy (h.L₃_E h.β_mem h.β_P) (h.L₃_E hE.x_mem hE.Px)
      (h.L₃_E hE.y_mem hE.Py) hG.δ_val h.ε_val (d₀ := D.d D.p₀) (dβ := D.d D.β₁)
      (dx := D.d x) (dy := D.d y) (by linarith) (by linarith) (by linarith) hdγ

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
