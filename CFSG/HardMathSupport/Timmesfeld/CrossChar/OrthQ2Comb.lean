module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Iso

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Classical

@[expose] noncomputable def lineSum (r₀ : ℕ) (r : Z3 → ℕ) (x : Z3) : ℕ :=
  r₀ + ∑ φ ∈ Rset.filter (fun φ => dot φ x = 0), r φ

theorem sum_lineSum_inner (L : Finset Z3) (r : Z3 → ℕ) :
    ∑ x ∈ L, ∑ φ ∈ Rset.filter (fun φ => dot φ x = 0), r φ =
      ∑ φ ∈ Rset, (L.filter (fun x => dot φ x = 0)).card * r φ := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

theorem card_lines_through_pair (ψ φ : Z3) (hψ : ψ ∈ Rset) (hφ : φ ∈ Rset) :
    ((Rset.filter (fun x => dot ψ x = 0)).filter (fun x => dot φ x = 0)).card =
      if φ = ψ then 4 else 1 := by
  rw [Finset.filter_filter]
  split_ifs with h
  · subst h
    simp only [and_self]
    exact card_lines_through φ hφ
  · exact card_lines_through_two ψ hψ φ hφ (Ne.symm h)

theorem sum_lineSum_through (r₀ : ℕ) (r : Z3 → ℕ) {ψ : Z3} (hψ : ψ ∈ Rset) :
    ∑ x ∈ Rset.filter (fun x => dot ψ x = 0), lineSum r₀ r x =
      (r₀ + ∑ φ ∈ Rset, r φ) + 3 * r₀ + 3 * r ψ := by
  simp only [lineSum]
  rw [Finset.sum_add_distrib, Finset.sum_const, card_lines_through ψ hψ, smul_eq_mul,
    sum_lineSum_inner]
  have h : ∀ φ ∈ Rset, ((Rset.filter (fun x => dot ψ x = 0)).filter
      (fun x => dot φ x = 0)).card * r φ = r φ + if φ = ψ then 3 * r φ else 0 := by
    intro φ hφ
    rw [card_lines_through_pair ψ φ hψ hφ]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq' Rset ψ]
  simp only [hψ, ↓reduceIte]
  ring

theorem even_lineSum {r₀ : ℕ} {r : Z3 → ℕ} (hr₀ : Even r₀) (hr : ∀ φ ∈ Rset, Even (r φ))
    (x : Z3) : Even (lineSum r₀ r x) := by
  unfold lineSum
  refine hr₀.add (Finset.even_sum _ fun φ hφ => hr φ (Finset.mem_filter.1 hφ).1)

theorem exists_line_of_ne_zero {r₀ : ℕ} {r : Z3 → ℕ} (hr₀ : Even r₀)
    (hr : ∀ φ ∈ Rset, Even (r φ)) (hN : 8 ≤ r₀ + ∑ φ ∈ Rset, r φ) {ψ : Z3} (hψ : ψ ∈ Rset)
    (hrψ : r ψ ≠ 0) :
    (∃ x ∈ Rset, dot ψ x = 0 ∧ 6 ≤ lineSum r₀ r x) ∨
      (r₀ = 0 ∧ ∃ x ∈ Rset, dot ψ x ≠ 0 ∧ lineSum r₀ r x + 8 ≤ r₀ + ∑ φ ∈ Rset, r φ) := by
  set N := r₀ + ∑ φ ∈ Rset, r φ with hNdef
  by_cases hgood : ∃ x ∈ Rset, dot ψ x = 0 ∧ 6 ≤ lineSum r₀ r x
  · exact Or.inl hgood
  right
  push Not at hgood
  have h4 : ∀ x ∈ Rset.filter (fun x => dot ψ x = 0), lineSum r₀ r x ≤ 4 := by
    intro x hx
    obtain ⟨hxR, hxψ⟩ := Finset.mem_filter.1 hx
    have h6 := hgood x hxR hxψ
    obtain ⟨k, hk⟩ := even_lineSum hr₀ hr x
    omega
  have hsum := sum_lineSum_through r₀ r hψ
  have hle : ∑ x ∈ Rset.filter (fun x => dot ψ x = 0), lineSum r₀ r x ≤ 16 := by
    calc ∑ x ∈ Rset.filter (fun x => dot ψ x = 0), lineSum r₀ r x
        ≤ ∑ _x ∈ Rset.filter (fun x => dot ψ x = 0), 4 := Finset.sum_le_sum h4
      _ = 16 := by rw [Finset.sum_const, card_lines_through ψ hψ, smul_eq_mul]
  obtain ⟨a, ha⟩ := hr₀
  obtain ⟨b, hb⟩ := hr ψ hψ
  have hr₀0 : r₀ = 0 := by omega
  have hrψ2 : r ψ = 2 := by omega
  have hN10 : N ≤ 10 := by omega
  refine ⟨hr₀0, ?_⟩
  have hline : ∀ φ ∈ Rset, φ ≠ ψ → ∃ x ∈ Rset, dot ψ x = 0 ∧ dot φ x = 0 := by
    intro φ hφ hne
    have h1 := card_lines_through_two ψ hψ φ hφ (Ne.symm hne)
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega :
      0 < (Rset.filter (fun x => dot ψ x = 0 ∧ dot φ x = 0)).card)
    obtain ⟨hxR, hxψ, hxφ⟩ := Finset.mem_filter.1 hx
    exact ⟨x, hxR, hxψ, hxφ⟩
  have hlineSum : ∀ x ∈ Rset, dot ψ x = 0 → ∀ s : Finset Z3, s ⊆ Rset → ψ ∉ s →
      (∀ φ ∈ s, dot φ x = 0) → 2 + ∑ φ ∈ s, r φ ≤ 4 := by
    intro x hxR hxψ s hs hψs hsx
    have h1 := h4 x (Finset.mem_filter.2 ⟨hxR, hxψ⟩)
    have hsub : insert ψ s ⊆ Rset.filter (fun φ => dot φ x = 0) := by
      intro φ hφ
      rcases Finset.mem_insert.1 hφ with rfl | hφ
      · exact Finset.mem_filter.2 ⟨hψ, by rw [dot_comm] at hxψ ⊢; exact hxψ⟩
      · exact Finset.mem_filter.2 ⟨hs hφ, hsx φ hφ⟩
    have h2 := Finset.sum_le_sum_of_subset (f := r) hsub
    rw [Finset.sum_insert hψs, hrψ2] at h2
    unfold lineSum at h1
    omega
  set S := Rset.filter (fun φ => φ ≠ ψ ∧ r φ ≠ 0) with hS
  have hSR : S ⊆ Rset := Finset.filter_subset _ _
  have hψS : ψ ∉ S := fun h => (Finset.mem_filter.1 h).2.1 rfl
  have hS2 : ∀ φ ∈ S, r φ = 2 := by
    intro φ hφ
    obtain ⟨hφR, hne, hφ0⟩ := Finset.mem_filter.1 hφ
    obtain ⟨x, hxR, hxψ, hxφ⟩ := hline φ hφR hne
    have h1 := hlineSum x hxR hxψ {φ} (Finset.singleton_subset_iff.2 hφR)
      (by simpa using Ne.symm hne) (by simpa using hxφ)
    rw [Finset.sum_singleton] at h1
    obtain ⟨c, hc⟩ := hr φ hφR
    omega
  have hcol : ∀ φ ∈ S, ∀ φ' ∈ S, φ ≠ φ' → ∀ x ∈ Rset, dot φ x = 0 → dot φ' x = 0 →
      dot ψ x ≠ 0 := by
    intro φ hφ φ' hφ' hne x hxR hxφ hxφ' hxψ
    have h1 := hlineSum x hxR hxψ {φ, φ'} (by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hSR hφ
      · rw [Finset.mem_singleton.1 ht]; exact hSR hφ')
      (by
        intro h
        rcases Finset.mem_insert.1 h with h | h
        · exact hψS (h ▸ hφ)
        · exact hψS (Finset.mem_singleton.1 h ▸ hφ'))
      (by
        intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact hxφ
        · rw [Finset.mem_singleton.1 ht]; exact hxφ')
    rw [Finset.sum_pair hne, hS2 φ hφ, hS2 φ' hφ'] at h1
    omega
  have hNS : N = 2 + 2 * S.card := by
    have h1 : ∑ φ ∈ Rset, r φ = r ψ + ∑ φ ∈ Rset.erase ψ, r φ :=
      (Finset.add_sum_erase _ _ hψ).symm
    have h2 : ∑ φ ∈ Rset.erase ψ, r φ = ∑ φ ∈ S, r φ := by
      rw [hS, Finset.sum_filter]
      rw [← Finset.add_sum_erase _ _ hψ]
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun φ hφ => ?_
      have hne : φ ≠ ψ := Finset.ne_of_mem_erase hφ
      by_cases h0 : r φ = 0 <;> simp [hne, h0]
    have h3 : ∑ φ ∈ S, r φ = 2 * S.card := by
      rw [Finset.sum_congr rfl hS2, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hNdef, hr₀0, zero_add, h1, h2, h3, hrψ2]
  set k : Z3 → ℕ := fun x => (S.filter (fun φ => dot φ x = 0)).card with hk
  have hFk : ∀ x ∈ Rset, dot ψ x ≠ 0 → lineSum r₀ r x = 2 * k x := by
    intro x hxR hxψ
    unfold lineSum
    rw [hr₀0, zero_add]
    have h1 : ∑ φ ∈ Rset.filter (fun φ => dot φ x = 0), r φ =
        ∑ φ ∈ S.filter (fun φ => dot φ x = 0), r φ := by
      rw [hS, Finset.filter_filter]
      refine (Finset.sum_subset (fun φ hφ => ?_) fun φ hφ hφ' => ?_).symm
      · obtain ⟨hφR, -, hx⟩ := Finset.mem_filter.1 hφ
        exact Finset.mem_filter.2 ⟨hφR, hx⟩
      · obtain ⟨hφR, hx⟩ := Finset.mem_filter.1 hφ
        by_contra h0
        apply hφ'
        refine Finset.mem_filter.2 ⟨hφR, ⟨fun h => ?_, h0⟩, hx⟩
        subst h
        exact hxψ hx
    rw [h1, Finset.sum_congr rfl fun φ hφ => hS2 φ (Finset.mem_filter.1 hφ).1,
      Finset.sum_const, smul_eq_mul, mul_comm]
  set L' := Rset.filter (fun x => dot ψ x ≠ 0) with hL'
  have hsumk : ∑ x ∈ L', k x = 3 * S.card := by
    simp only [hk, Finset.card_filter]
    rw [Finset.sum_comm]
    have h1 : ∀ φ ∈ S, ∑ x ∈ L', (if dot φ x = 0 then 1 else 0) = 3 := by
      intro φ hφ
      rw [← Finset.card_filter, hL', Finset.filter_filter]
      exact card_lines_avoid ψ hψ φ (hSR hφ) (fun h => hψS (h ▸ hφ))
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcardL' : L'.card = 9 := card_lines_not_through ψ hψ
  by_contra hno
  push Not at hno
  have hS34 : S.card = 3 ∨ S.card = 4 := by omega
  rcases hS34 with h3 | h4'
  ·
    have hk1 : ∀ x ∈ L', 1 ≤ k x := by
      intro x hx
      obtain ⟨hxR, hxψ⟩ := Finset.mem_filter.1 hx
      have h1 := hno x hxR hxψ
      rw [hFk x hxR hxψ] at h1
      omega
    have hkeq : ∀ x ∈ L', k x = 1 := by
      intro x hx
      by_contra hne
      have h2 : 2 ≤ k x := by have := hk1 x hx; omega
      have hlow : ∑ y ∈ L', 1 + 1 ≤ ∑ y ∈ L', k y := by
        rw [← Finset.add_sum_erase _ _ hx, ← Finset.add_sum_erase _ _ hx]
        have h5 : ∑ y ∈ L'.erase x, 1 ≤ ∑ y ∈ L'.erase x, k y :=
          Finset.sum_le_sum fun y hy => hk1 y (Finset.mem_of_mem_erase hy)
        omega
      rw [Finset.sum_const, smul_eq_mul, hcardL', hsumk, h3] at hlow
      omega
    obtain ⟨φ, hφ, φ', hφ', hne⟩ : ∃ φ ∈ S, ∃ φ' ∈ S, φ ≠ φ' := by
      have : 1 < S.card := by omega
      obtain ⟨φ, hφ, φ', hφ', hne⟩ := Finset.one_lt_card.1 this
      exact ⟨φ, hφ, φ', hφ', hne⟩
    have h1 := card_lines_through_two φ (hSR hφ) φ' (hSR hφ') hne
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega :
      0 < (Rset.filter (fun x => dot φ x = 0 ∧ dot φ' x = 0)).card)
    obtain ⟨hxR, hxφ, hxφ'⟩ := Finset.mem_filter.1 hx
    have hxψ := hcol φ hφ φ' hφ' hne x hxR hxφ hxφ'
    have hxL : x ∈ L' := Finset.mem_filter.2 ⟨hxR, hxψ⟩
    have h2 : 2 ≤ k x := by
      simp only [hk]
      have hsub : ({φ, φ'} : Finset Z3) ⊆ S.filter (fun t => dot t x = 0) := by
        intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact Finset.mem_filter.2 ⟨hφ, hxφ⟩
        · rw [Finset.mem_singleton.1 ht]; exact Finset.mem_filter.2 ⟨hφ', hxφ'⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hne] at this
    have := hkeq x hxL
    omega
  ·
    have hk2 : ∀ x ∈ L', 2 ≤ k x := by
      intro x hx
      obtain ⟨hxR, hxψ⟩ := Finset.mem_filter.1 hx
      have h1 := hno x hxR hxψ
      rw [hFk x hxR hxψ] at h1
      omega
    have hlow : ∑ _y ∈ L', 2 ≤ ∑ y ∈ L', k y := Finset.sum_le_sum hk2
    rw [Finset.sum_const, smul_eq_mul, hcardL', hsumk, h4'] at hlow
    omega

end CFSG.HardMathSupport.Timmesfeld.CrossChar
