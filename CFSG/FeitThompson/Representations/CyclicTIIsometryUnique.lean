module

public import CFSG.FeitThompson.Representations.InducedRectangleDifferencesNormThree
public import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange
public import CFSG.FeitThompson.Representations.NormOneVirtualCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Lattice

variable {G : Type*} [Group G] [Fintype G]

theorem eq_of_cfInner_ne_zero_of_orthogonal {P : Type*} {η : P → G → ℂ} {t : G → ℂ}
    (hη : ∀ p, η p ∈ signedIrr G) (hηorth : ∀ p q, p ≠ q → cfInner (η p) (η q) = 0)
    (ht : t ∈ signedIrr G) (p q : P) (hp : cfInner (η p) t ≠ 0) (hq : cfInner (η q) t ≠ 0) :
    p = q := by
  by_contra hpq
  have h1 := eq_or_eq_neg_of_cfInner_ne_zero (hη p) ht hp
  have h2 := eq_or_eq_neg_of_cfInner_ne_zero (hη q) ht hq
  have h0 := hηorth p q hpq
  have htt : cfInner t t = 1 := cfInner_self_of_mem_signedIrr ht
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at h0 <;>
    simp [cfInner_neg_left, cfInner_neg_right, htt] at h0

theorem eq_of_cfInner_triple_eq_neg_one {P : Type*} {η : P → G → ℂ} {t : G → ℂ}
    (hη : ∀ p, η p ∈ signedIrr G) (hηorth : ∀ p q, p ≠ q → cfInner (η p) (η q) = 0)
    (ht : t ∈ signedIrr G) {p₀ q₁ r₁ q₂ r₂ : P}
    (h1 : cfInner (-η p₀ - η q₁ + η r₁) t = -1)
    (h2 : cfInner (-η p₀ - η q₂ + η r₂) t = -1)
    (hq₁ : q₁ ≠ p₀) (hr₁ : r₁ ≠ p₀)
    (h11 : q₁ ≠ q₂) (h12 : q₁ ≠ r₂) (h21 : r₁ ≠ q₂) (h22 : r₁ ≠ r₂) :
    η p₀ = t := by
  have hexp : ∀ q r : P, cfInner (-η p₀ - η q + η r) t
      = -cfInner (η p₀) t - cfInner (η q) t + cfInner (η r) t := fun q r => by
    rw [cfInner_add_left, cfInner_sub_left, cfInner_neg_left]
  rw [hexp] at h1 h2
  have huniq := eq_of_cfInner_ne_zero_of_orthogonal hη hηorth ht
  have hp₀ : cfInner (η p₀) t ≠ 0 := by
    intro ha
    rw [ha] at h1 h2
    have hne1 : cfInner (η q₁) t ≠ 0 ∨ cfInner (η r₁) t ≠ 0 := by
      by_contra hc
      rw [not_or, not_ne_iff, not_ne_iff] at hc
      rw [hc.1, hc.2] at h1
      norm_num at h1
    have hne2 : cfInner (η q₂) t ≠ 0 ∨ cfInner (η r₂) t ≠ 0 := by
      by_contra hc
      rw [not_or, not_ne_iff, not_ne_iff] at hc
      rw [hc.1, hc.2] at h2
      norm_num at h2
    rcases hne1 with hx | hx <;> rcases hne2 with hy | hy
    · exact h11 (huniq _ _ hx hy)
    · exact h12 (huniq _ _ hx hy)
    · exact h21 (huniq _ _ hx hy)
    · exact h22 (huniq _ _ hx hy)
  have hb : cfInner (η q₁) t = 0 := by by_contra hc; exact hq₁ (huniq _ _ hc hp₀)
  have hc : cfInner (η r₁) t = 0 := by by_contra hc; exact hr₁ (huniq _ _ hc hp₀)
  rw [hb, hc] at h1
  refine eq_of_cfInner_eq_one (hη p₀) ht ?_
  linear_combination -h1

end Lattice

theorem exists_pair_ne_ne_of_three_le_natCard {α : Type*} (x₀ : α) (h : 3 ≤ Nat.card α) :
    ∃ a b : α, a ≠ b ∧ a ≠ x₀ ∧ b ≠ x₀ := by
  classical
  have hfin : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype α := Fintype.ofFinite α
  have hcard : 3 ≤ Fintype.card α := by rwa [Nat.card_eq_fintype_card] at h
  have h1 : 1 < (Finset.univ.erase x₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
  exact ⟨a, b, hab, (Finset.mem_erase.mp ha).1, (Finset.mem_erase.mp hb).1⟩

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]

namespace IsCyclicTIPair

noncomputable def prodCharAlphaCF (h : IsCyclicTIPair W W1 W2) (i : Irr ↥W1) (j : Irr ↥W2) :
    classFun ↥W :=
  h.basisProdIrr (principalIrr ↥W1, principalIrr ↥W2) - h.basisProdIrr (i, principalIrr ↥W2)
    - h.basisProdIrr (principalIrr ↥W1, j) + h.basisProdIrr (i, j)

omit [Fintype G] [Fintype ↥W] in
theorem prodCharAlphaCF_eq (h : IsCyclicTIPair W W1 W2) (i : Irr ↥W1) (j : Irr ↥W2) :
    h.prodCharAlphaCF i j =
      h.basisProdIrr (principalIrr ↥W1, principalIrr ↥W2) - h.basisProdIrr (i, principalIrr ↥W2)
        - h.basisProdIrr (principalIrr ↥W1, j) + h.basisProdIrr (i, j) := (rfl)

omit [Fintype G] [Fintype ↥W] in
theorem coe_prodCharAlphaCF (h : IsCyclicTIPair W W1 W2) (i : Irr ↥W1) (j : Irr ↥W2) :
    ((h.prodCharAlphaCF i j : classFun ↥W) : ↥W → ℂ) =
      h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) := by
  simp [prodCharAlphaCF_eq, prodCharAlpha_eq, coe_basisProdIrr_apply]

omit [Fintype G] [Fintype ↥W] in
theorem three_le_natCard_Irr_left (h : IsCyclicTIPair W W1 W2) : 3 ≤ Nat.card (Irr ↥W1) := by
  rw [h.card_Irr_left]; exact h.three_le_natCard_left

omit [Fintype G] [Fintype ↥W] in
theorem three_le_natCard_Irr_right (h : IsCyclicTIPair W W1 W2) : 3 ≤ Nat.card (Irr ↥W2) := by
  rw [h.card_Irr_right]; exact h.three_le_natCard_right

variable {σ τ : classFun ↥W →ₗ[ℂ] classFun G}

theorem cfInner_prodCharEta_of_ne (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {p q : Irr ↥W1 × Irr ↥W2} (hpq : p ≠ q) :
    cfInner (h.prodCharEta σ p.1 p.2) (h.prodCharEta σ q.1 q.2) = 0 := by
  rw [h.cfInner_prodCharEta hσ, if_neg]
  rintro ⟨h1, h2⟩
  exact hpq (Prod.ext h1 h2)

theorem cfInner_prodCharEta_self (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) :
    cfInner (h.prodCharEta σ i j) (h.prodCharEta σ i j) = 1 := by
  rw [h.cfInner_prodCharEta hσ, if_pos ⟨rfl, rfl⟩]

theorem prodCharEta_mem_signedIrr (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) :
    h.prodCharEta σ i j ∈ signedIrr G :=
  mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
    (mem_span_Irr_of_mem_virtualChars (h.prodCharEta_mem_virtualChars hσ i j))
    (h.cfInner_prodCharEta_self hσ i j)

theorem prodCharBeta_eq_prodCharEta (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) :
    h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) =
      -h.prodCharEta σ i (principalIrr ↥W2) - h.prodCharEta σ (principalIrr ↥W1) j
        + h.prodCharEta σ i j := by
  have hind : ((σ (h.prodCharAlphaCF i j) : classFun G) : G → ℂ)
      = indClassFun W (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) := by
    rw [← h.coe_prodCharAlphaCF i j]
    refine hσ.eq_indClassFun _ fun x hx => ?_
    rw [h.coe_prodCharAlphaCF]
    exact dadeDomain.apply_eq_zero (h.prodCharAlpha_mem_dadeDomain i.2 j.2) hx
  have hlin : ((σ (h.prodCharAlphaCF i j) : classFun G) : G → ℂ)
      = h.prodCharEta σ (principalIrr ↥W1) (principalIrr ↥W2)
        - h.prodCharEta σ i (principalIrr ↥W2)
        - h.prodCharEta σ (principalIrr ↥W1) j + h.prodCharEta σ i j := by
    rw [h.prodCharAlphaCF_eq, map_add, map_sub, map_sub]
    simp only [prodCharEta_eq_coe_apply, Submodule.coe_add, Submodule.coe_sub]
  rw [h.prodCharBeta_eq, ← hind, hlin, h.prodCharEta_principal hσ]
  abel

theorem prodCharBeta_eq_prodCharEta' (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) :
    h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) =
      -h.prodCharEta σ (principalIrr ↥W1) j - h.prodCharEta σ i (principalIrr ↥W2)
        + h.prodCharEta σ i j := by
  rw [h.prodCharBeta_eq_prodCharEta hσ]; abel

theorem cfInner_prodCharBeta_prodCharEta_row (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {i : Irr ↥W1} {j : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hj : j ≠ principalIrr ↥W2) :
    cfInner (h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodCharEta σ i (principalIrr ↥W2)) = -1 := by
  rw [h.prodCharBeta_eq_prodCharEta hσ, cfInner_add_left, cfInner_sub_left, cfInner_neg_left,
    h.cfInner_prodCharEta_self hσ,
    h.cfInner_prodCharEta_of_ne hσ (p := (principalIrr ↥W1, j)) (q := (i, principalIrr ↥W2))
      (by simp [Prod.ext_iff, Ne.symm hi]),
    h.cfInner_prodCharEta_of_ne hσ (p := (i, j)) (q := (i, principalIrr ↥W2))
      (by simp [Prod.ext_iff, hj])]
  ring

theorem cfInner_prodCharBeta_prodCharEta_col (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {i : Irr ↥W1} {j : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) :
    cfInner (h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodCharEta σ (principalIrr ↥W1) j) = -1 := by
  rw [h.prodCharBeta_eq_prodCharEta' hσ, cfInner_add_left, cfInner_sub_left, cfInner_neg_left,
    h.cfInner_prodCharEta_self hσ,
    h.cfInner_prodCharEta_of_ne hσ (p := (i, principalIrr ↥W2)) (q := (principalIrr ↥W1, j))
      (by simp [Prod.ext_iff, hi]),
    h.cfInner_prodCharEta_of_ne hσ (p := (i, j)) (q := (principalIrr ↥W1, j))
      (by simp [Prod.ext_iff, hi])]
  ring

theorem prodCharEta_row_eq (h : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (hτ : IsCyclicTIIsometry W W1 W2 τ) {i : Irr ↥W1} (hi : i ≠ principalIrr ↥W1) :
    h.prodCharEta σ i (principalIrr ↥W2) = h.prodCharEta τ i (principalIrr ↥W2) := by
  obtain ⟨j, k, hjk, hj, hk⟩ :=
    exists_pair_ne_ne_of_three_le_natCard (principalIrr ↥W2) h.three_le_natCard_Irr_right
  refine eq_of_cfInner_triple_eq_neg_one
    (η := fun p : Irr ↥W1 × Irr ↥W2 => h.prodCharEta σ p.1 p.2)
    (fun p => h.prodCharEta_mem_signedIrr hσ p.1 p.2)
    (fun p q hpq => h.cfInner_prodCharEta_of_ne hσ hpq)
    (h.prodCharEta_mem_signedIrr hτ i (principalIrr ↥W2))
    (p₀ := (i, principalIrr ↥W2))
    (q₁ := (principalIrr ↥W1, j)) (r₁ := (i, j))
    (q₂ := (principalIrr ↥W1, k)) (r₂ := (i, k)) ?_ ?_
    (by simp [Prod.ext_iff, Ne.symm hi]) (by simp [Prod.ext_iff, hj])
    (by simp [Prod.ext_iff, hjk]) (by simp [Prod.ext_iff, Ne.symm hi])
    (by simp [Prod.ext_iff, hi]) (by simp [Prod.ext_iff, hjk])
  · rw [← h.prodCharBeta_eq_prodCharEta hσ i j]
    exact h.cfInner_prodCharBeta_prodCharEta_row hτ hi hj
  · rw [← h.prodCharBeta_eq_prodCharEta hσ i k]
    exact h.cfInner_prodCharBeta_prodCharEta_row hτ hi hk

theorem prodCharEta_col_eq (h : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (hτ : IsCyclicTIIsometry W W1 W2 τ) {j : Irr ↥W2} (hj : j ≠ principalIrr ↥W2) :
    h.prodCharEta σ (principalIrr ↥W1) j = h.prodCharEta τ (principalIrr ↥W1) j := by
  obtain ⟨i, k, hik, hi, hk⟩ :=
    exists_pair_ne_ne_of_three_le_natCard (principalIrr ↥W1) h.three_le_natCard_Irr_left
  refine eq_of_cfInner_triple_eq_neg_one
    (η := fun p : Irr ↥W1 × Irr ↥W2 => h.prodCharEta σ p.1 p.2)
    (fun p => h.prodCharEta_mem_signedIrr hσ p.1 p.2)
    (fun p q hpq => h.cfInner_prodCharEta_of_ne hσ hpq)
    (h.prodCharEta_mem_signedIrr hτ (principalIrr ↥W1) j)
    (p₀ := (principalIrr ↥W1, j))
    (q₁ := (i, principalIrr ↥W2)) (r₁ := (i, j))
    (q₂ := (k, principalIrr ↥W2)) (r₂ := (k, j)) ?_ ?_
    (by simp [Prod.ext_iff, hi]) (by simp [Prod.ext_iff, hi])
    (by simp [Prod.ext_iff, hik]) (by simp [Prod.ext_iff, Ne.symm hj])
    (by simp [Prod.ext_iff, hj]) (by simp [Prod.ext_iff, hik])
  · rw [← h.prodCharBeta_eq_prodCharEta' hσ i j]
    exact h.cfInner_prodCharBeta_prodCharEta_col hτ hi
  · rw [← h.prodCharBeta_eq_prodCharEta' hσ k j]
    exact h.cfInner_prodCharBeta_prodCharEta_col hτ hk

theorem prodCharEta_eq_prodCharEta (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hτ : IsCyclicTIIsometry W W1 W2 τ)
    (i : Irr ↥W1) (j : Irr ↥W2) : h.prodCharEta σ i j = h.prodCharEta τ i j := by
  by_cases hi : i = principalIrr ↥W1
  · subst hi
    by_cases hj : j = principalIrr ↥W2
    · subst hj
      rw [h.prodCharEta_principal hσ, h.prodCharEta_principal hτ]
    · exact h.prodCharEta_col_eq hσ hτ hj
  · by_cases hj : j = principalIrr ↥W2
    · subst hj
      exact h.prodCharEta_row_eq hσ hτ hi
    ·
      have hrect := (h.prodCharBeta_eq_prodCharEta hσ i j).symm.trans
        (h.prodCharBeta_eq_prodCharEta hτ i j)
      rw [h.prodCharEta_row_eq hσ hτ hi, h.prodCharEta_col_eq hσ hτ hj] at hrect
      exact add_left_cancel hrect

end IsCyclicTIPair

namespace IsCyclicTIIsometry

variable {σ τ : classFun ↥W →ₗ[ℂ] classFun G}

theorem eq_of_isCyclicTIIsometry (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hτ : IsCyclicTIIsometry W W1 W2 τ) : σ = τ :=
  h.basisProdIrr.ext fun p => by
    obtain ⟨i, j⟩ := p
    refine Subtype.ext ?_
    rw [← h.prodCharEta_eq_coe_apply (σ := σ) i j, ← h.prodCharEta_eq_coe_apply (σ := τ) i j]
    exact h.prodCharEta_eq_prodCharEta hσ hτ i j

theorem apply_eq_of_isCyclicTIIsometry (h : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (hτ : IsCyclicTIIsometry W W1 W2 τ)
    (f : classFun ↥W) : σ f = τ f := by
  rw [eq_of_isCyclicTIIsometry h hσ hτ]

end IsCyclicTIIsometry

end CFSG.FeitThompson

end
