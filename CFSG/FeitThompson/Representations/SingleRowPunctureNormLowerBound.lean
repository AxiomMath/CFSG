module

import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
public import CFSG.FeitThompson.Representations.OneBlockRestrictionPuncturedNorm
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open OneBlockRestriction

theorem mem_irrTrivialOn_of_subset {K : Type*} [Group K] {Q : Subgroup K} {χ : K → ℂ}
    (hχ : χ ∈ Irr K) (h : (Q : Set K) ⊆ charValueKernel χ) : χ ∈ irrTrivialOn Q :=
  mem_irrTrivialOn.2 ⟨hχ, fun _ hx => mem_charValueKernel.1 (h hx)⟩

private theorem erase_eq_erase {A : Type*} (d₁ d₂ : DecidableEq A) (s : Finset A) (a : A) :
    @Finset.erase A d₁ s a = @Finset.erase A d₂ s a := by
  ext x
  rw [@Finset.mem_erase A d₁, @Finset.mem_erase A d₂]

variable {G : Type*} [Group G] [Fintype G] {S : Subgroup G} [Fintype ↥S] {H P : Subgroup ↥S}

theorem card_div_sub_sq_le_sum_erase_norm_sq [DecidableEq ↥H] [Fintype ↥H] [H.Normal] [P.Normal]
    [IsMulCommutative ↥H] (hPH : P ≤ H)
    (ν : Submodule.span ℤ (indFamDetect H (P.subgroupOf H)) →+ Submodule.span ℤ (Irr G))
    (hν : ∀ f : charSpanZero (indFamDetect H (P.subgroupOf H)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun S (f : ↥S → ℂ))
    (hcard : 2 ≤ (indFamDetect H (P.subgroupOf H)).ncard)
    {q u : ℕ} (hd : H.index = u * q) (hPu : 2 * u + 1 ≤ Nat.card ↥P)
    {ζ : ↥S → ℂ} (hζ : ζ ∈ indFamDetect H (P.subgroupOf H)) (hζq : cfInner ζ ζ = (q : ℂ))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {χ : G → ℂ} (hχ : χ ∈ Submodule.span ℤ (Irr G))
    (hζχ : cfInner (ν ⟨ζ, Submodule.subset_span hζ⟩ : G → ℂ) χ = (ε : ℂ))
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect H (P.subgroupOf H), ξ ≠ ζ →
      cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) χ = 0) :
    (Nat.card ↥S : ℝ) / q - (u : ℝ) ^ 2
      ≤ ∑ x ∈ Finset.univ.erase (1 : ↥H), ‖χ ((x : ↥S) : G)‖ ^ 2 := by
  have dH : DecidableEq ↥H := Classical.decEq ↥H
  rw [erase_eq_erase _ dH]
  obtain ⟨a, n, b, hnpos, ha, hn, hζ1, hbsupp, hsplit⟩ :=
    exists_intCast_eq_on_sdiff_one_of_cfInner_eq_zero hPH ν hν hcard hζ hχ horth
  have haε : a = ε := by
    have : (a : ℂ) = (ε : ℂ) := by rw [← ha, hζχ]
    exact_mod_cast this
  have hnq : n = q := by
    have : (n : ℂ) = (q : ℂ) := by rw [← hn, hζq]
    exact_mod_cast this
  subst haε hnq
  obtain ⟨θ, hθIrr, hθdet, hθind⟩ := exists_mem_Irr_of_mem_indFamDetect hζ
  set α : ↥H → ℂ := ∑ θ' ∈ irrFinset ↥H, (b θ' : ℂ) • θ' with hαdef
  have hα : α ∈ Submodule.span ℤ (irrTrivialOn (P.subgroupOf H)) := by
    rw [hαdef]
    refine Submodule.sum_mem _ fun θ' hθ' => ?_
    by_cases hz : (P.subgroupOf H : Set ↥H) ⊆ charValueKernel θ'
    · rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (mem_irrTrivialOn_of_subset (mem_irrFinset.1 hθ') hz))
    · rw [hbsupp θ' hz]
      simp
  obtain ⟨m, hm⟩ := exists_int_apply_one_of_mem_span_irrTrivialOn hα
  have hkey := sum_erase_norm_sq_eq (P := P) hθIrr hθdet (n := n) (by rw [hθind, hn]) a hα
    (f := fun x : ↥H => χ ((x : ↥S) : G)) (fun x hx => by
      rw [hsplit x hx, hθind, hαdef]
      simp [Finset.sum_apply])
  rw [hm, erase_eq_erase _ dH] at hkey
  have hreal : (∑ x ∈ Finset.univ.erase (1 : ↥H), ‖χ ((x : ↥S) : G)‖ ^ 2 : ℝ)
      = (a : ℝ) ^ 2 / (n : ℝ) * ((Nat.card ↥S : ℝ) - (H.index : ℝ) ^ 2 / (n : ℝ))
        - 2 * (a : ℝ) * (H.index : ℝ) * (m : ℝ) / (n : ℝ)
        + ∑ x ∈ Finset.univ.erase (1 : ↥H), ‖α x‖ ^ 2 := by
    apply Complex.ofReal_inj.1
    push_cast
    linear_combination hkey
  have hlow : ((Nat.card ↥P : ℝ) - 1) * (m : ℝ) ^ 2
      ≤ ∑ x ∈ Finset.univ.erase (1 : ↥H), ‖α x‖ ^ 2 := by
    have h := card_sub_one_mul_norm_sq_le_sum_erase_norm_sq (P := P) hPH hα
    rw [hm, Complex.norm_intCast, sq_abs, erase_eq_erase _ dH] at h
    exact h
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have ha2 : (a : ℝ) ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hdR : (H.index : ℝ) = (u : ℝ) * (n : ℝ) := by rw [hd]; push_cast; ring
  have hbsq : (a : ℝ) * (m : ℝ) ≤ ((a : ℝ) * (m : ℝ)) ^ 2 := by
    have h1 := Int.le_self_sq (a * m)
    have h2 : ((a * m : ℤ) : ℝ) ≤ (((a * m) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hPuR : 2 * (u : ℝ) ≤ (Nat.card ↥P : ℝ) - 1 := by
    have h3 : ((2 * u + 1 : ℕ) : ℝ) ≤ (Nat.card ↥P : ℝ) := by exact_mod_cast hPu
    push_cast at h3
    linarith
  have huR : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
  rw [hreal, hdR, ha2]
  have hrem : 2 * (a : ℝ) * ((u : ℝ) * (n : ℝ)) * (m : ℝ) / (n : ℝ)
      ≤ ((Nat.card ↥P : ℝ) - 1) * (m : ℝ) ^ 2 := by
    have hmul : 2 * (a : ℝ) * ((u : ℝ) * (n : ℝ)) * (m : ℝ) / (n : ℝ)
        = 2 * (u : ℝ) * ((a : ℝ) * (m : ℝ)) := by field_simp
    have hsq : ((a : ℝ) * (m : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by rw [mul_pow, ha2, one_mul]
    rw [hmul, ← hsq]
    nlinarith [mul_nonneg (sub_nonneg.2 hPuR) (sq_nonneg ((a : ℝ) * (m : ℝ))),
      mul_nonneg huR (sub_nonneg.2 hbsq)]
  have hmain : (Nat.card ↥S : ℝ) / (n : ℝ) - (u : ℝ) ^ 2
      = 1 / (n : ℝ) * ((Nat.card ↥S : ℝ) - ((u : ℝ) * (n : ℝ)) ^ 2 / (n : ℝ)) := by
    field_simp
  rw [hmain]
  linarith

end CFSG.FeitThompson
