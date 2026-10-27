module

public import CFSG.CGT.T75E.RootLin

public section

namespace CFSG.CGT.T75E

open Matrix CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Vectors

variable {F : Type} [Field F] {n : ℕ}

theorem tvSL_mulVec {v φ : Fin n → F} (h : φ ⬝ᵥ v = 0) (x : Fin n → F) :
    ((tvSL v φ h : SL(n, F)) : Matrix (Fin n) (Fin n) F) *ᵥ x = x + (φ ⬝ᵥ x) • v := by
  rw [coe_tvSL, one_add_vecMulVec_mulVec]

theorem exists_sl_mulVec_eq {p q : Fin n → F} (hpq : ∀ μ : F, q ≠ μ • p)
    (hqp : ∀ μ : F, p ≠ μ • q) :
    ∃ g : SL(n, F), (g : Matrix (Fin n) (Fin n) F) *ᵥ p = q := by
  obtain ⟨χ₁, h1p, h1q⟩ := exists_dot_of_not_smul (c := p) (d := q) hpq
  obtain ⟨χ₂, h2q, h2p⟩ := exists_dot_of_not_smul (c := q) (d := p) hqp
  have hφ : (χ₁ + χ₂) ⬝ᵥ (q - p) = 0 := by
    rw [dotProduct_sub, add_dotProduct, add_dotProduct, h1p, h1q, h2q, h2p]
    ring
  refine ⟨tvSL (q - p) (χ₁ + χ₂) hφ, ?_⟩
  rw [tvSL_mulVec, add_dotProduct, h1p, h2p, zero_add, one_smul]
  abel

theorem exists_sl_fix_move {a w r : Fin n → F} (hw : ∀ μ : F, w ≠ μ • a)
    (hr : ∀ α β : F, r ≠ α • a + β • w) :
    ∃ g : SL(n, F), (g : Matrix (Fin n) (Fin n) F) *ᵥ a = a ∧
      (g : Matrix (Fin n) (Fin n) F) *ᵥ w = r := by
  have hwr : ∀ α β : F, w ≠ α • a + β • r := by
    intro α β h
    by_cases hβ : β = 0
    · subst hβ
      exact hw α (by rw [h, zero_smul, add_zero])
    · apply hr (-(β⁻¹ * α)) β⁻¹
      rw [h, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hβ, one_smul, ← add_assoc,
        ← add_smul, neg_add_cancel, zero_smul, zero_add]
  obtain ⟨θ₁, h1a, h1w, h1r⟩ := exists_dot_of_not_mem_pair (c := a) (e := w) (d := r) hr
  obtain ⟨θ₂, h2a, h2r, h2w⟩ := exists_dot_of_not_mem_pair (c := a) (e := r) (d := w) hwr
  have hφ : (θ₁ + θ₂) ⬝ᵥ (r - w) = 0 := by
    rw [dotProduct_sub, add_dotProduct, add_dotProduct, h1r, h1w, h2r, h2w]
    ring
  refine ⟨tvSL (r - w) (θ₁ + θ₂) hφ, ?_, ?_⟩
  · rw [tvSL_mulVec, add_dotProduct, h1a, h2a, add_zero, zero_smul, add_zero]
  · rw [tvSL_mulVec, add_dotProduct, h1w, h2w, zero_add, one_smul]
    abel

theorem exists_not_mem_span_pair (hn : 3 ≤ n) (a w : Fin n → F) :
    ∃ r : Fin n → F, ∀ α β : F, r ≠ α • a + β • w := by
  by_contra h
  push Not at h
  have hspan : Submodule.span F {a, w} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨α, β, hx⟩ := h x
    rw [Submodule.mem_span_pair]
    exact ⟨α, β, hx.symm⟩
  classical
  have h1 : Module.finrank F (Submodule.span F {a, w}) ≤ 2 := by
    have := finrank_span_finset_le_card (R := F) ({a, w} : Finset (Fin n → F))
    rw [Finset.coe_pair] at this
    exact this.trans Finset.card_le_two
  rw [hspan, finrank_top, Module.finrank_fin_fun] at h1
  omega

theorem exists_sl_fix_move_pt (hn : 3 ≤ n) {a w b : Fin n → F} (hw : ∀ μ : F, w ≠ μ • a)
    (hb : ∀ μ : F, b ≠ μ • a) :
    ∃ g : SL(n, F), (g : Matrix (Fin n) (Fin n) F) *ᵥ a = a ∧
      (g : Matrix (Fin n) (Fin n) F) *ᵥ w = b := by
  by_cases hout : ∀ α β : F, b ≠ α • a + β • w
  · exact exists_sl_fix_move hw hout
  push Not at hout
  obtain ⟨α, β, hαβ⟩ := hout
  obtain ⟨r, hr⟩ := exists_not_mem_span_pair hn a w
  obtain ⟨g₁, hg₁a, hg₁w⟩ := exists_sl_fix_move hw hr
  have hra : ∀ μ : F, r ≠ μ • a := fun μ h => hr μ 0 (by rw [h, zero_smul, add_zero])
  have hbr : ∀ α' β' : F, b ≠ α' • a + β' • r := by
    intro α' β' h
    by_cases hβ' : β' = 0
    · subst hβ'
      exact hb α' (by rw [h, zero_smul, add_zero])
    · have h1 : α' • a + β' • r = α • a + β • w := h.symm.trans hαβ
      have h2 : β' • r = (α - α') • a + β • w :=
        calc β' • r = (α' • a + β' • r) - α' • a := by abel
          _ = (α • a + β • w) - α' • a := by rw [h1]
          _ = (α - α') • a + β • w := by rw [sub_smul]; abel
      apply hr (β'⁻¹ * (α - α')) (β'⁻¹ * β)
      calc r = β'⁻¹ • (β' • r) := by rw [smul_smul, inv_mul_cancel₀ hβ', one_smul]
        _ = β'⁻¹ • ((α - α') • a + β • w) := by rw [h2]
        _ = (β'⁻¹ * (α - α')) • a + (β'⁻¹ * β) • w := by rw [smul_add, smul_smul, smul_smul]
  obtain ⟨g₂, hg₂a, hg₂r⟩ := exists_sl_fix_move hra hbr
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁a, hg₂a]
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁w, hg₂r]

theorem exists_sl_pair (hn : 3 ≤ n) {p₁ p₂ q₁ q₂ : Fin n → F} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hp : ∀ μ : F, p₂ ≠ μ • p₁) (hq : ∀ μ : F, q₂ ≠ μ • q₁) :
    ∃ h : SL(n, F), ∃ μ : F, μ ≠ 0 ∧ (h : Matrix (Fin n) (Fin n) F) *ᵥ p₁ = μ • q₁ ∧
      (h : Matrix (Fin n) (Fin n) F) *ᵥ p₂ = q₂ := by
  obtain ⟨g₁, μ₁, hμ₁, hg₁⟩ : ∃ g₁ : SL(n, F), ∃ μ₁ : F, μ₁ ≠ 0 ∧
      (g₁ : Matrix (Fin n) (Fin n) F) *ᵥ p₁ = μ₁ • q₁ := by
    by_cases hc : ∃ μ : F, q₁ = μ • p₁
    · obtain ⟨μ, hμ⟩ := hc
      have hμ0 : μ ≠ 0 := fun h => hq₁ (by rw [hμ, h, zero_smul])
      refine ⟨1, μ⁻¹, inv_ne_zero hμ0, ?_⟩
      rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul, Matrix.SpecialLinearGroup.coe_one,
        one_mulVec]
    · push Not at hc
      have hqp : ∀ μ : F, p₁ ≠ μ • q₁ := by
        intro μ h
        have hμ0 : μ ≠ 0 := fun h0 => hp₁ (by rw [h, h0, zero_smul])
        exact hc μ⁻¹ (by rw [h, smul_smul, inv_mul_cancel₀ hμ0, one_smul])
      obtain ⟨g, hg⟩ := exists_sl_mulVec_eq hc hqp
      exact ⟨g, 1, one_ne_zero, by rw [hg, one_smul]⟩
  have hw : ∀ μ : F, (g₁ : Matrix (Fin n) (Fin n) F) *ᵥ p₂ ≠ μ • q₁ := by
    intro μ h
    have h0 : (g₁ : Matrix (Fin n) (Fin n) F) *ᵥ (p₂ - (μ * μ₁⁻¹) • p₁) = 0 := by
      rw [mulVec_sub, mulVec_smul, hg₁, h, smul_smul, mul_assoc, inv_mul_cancel₀ hμ₁, mul_one,
        sub_self]
    have h1 : p₂ - (μ * μ₁⁻¹) • p₁ = 0 := by
      have := inv_mulVec_mulVec' g₁ (p₂ - (μ * μ₁⁻¹) • p₁)
      rw [h0, mulVec_zero] at this
      exact this.symm
    exact hp (μ * μ₁⁻¹) (sub_eq_zero.1 h1)
  obtain ⟨g₂, hg₂a, hg₂w⟩ := exists_sl_fix_move_pt hn hw hq
  refine ⟨g₂ * g₁, μ₁, hμ₁, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁, mulVec_smul, hg₂a]
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₂w]

end Vectors

section Group

variable {K : Type} [Group K] {n : ℕ} {F : Type} [Field F]

theorem two_trans_lin (hn : 3 ≤ n) (π : SL(n, F) →* K) (hπ : Function.Surjective π)
    {c : Fin n → F} (hc : c ≠ 0) :
    ∀ U₁ U₂ V₁ V₂ : Subgroup K, (∃ x : K, U₁ = conjSubgroup x ((tvCenterSL c).map π)) →
      (∃ x : K, U₂ = conjSubgroup x ((tvCenterSL c).map π)) →
      (∃ x : K, V₁ = conjSubgroup x ((tvCenterSL c).map π)) →
      (∃ x : K, V₂ = conjSubgroup x ((tvCenterSL c).map π)) → U₁ ≠ U₂ → V₁ ≠ V₂ →
        ∃ g : K, conjSubgroup g U₁ = V₁ ∧ conjSubgroup g U₂ = V₂ := by
  have hconj : ∀ g : SL(n, F), conjSubgroup (π g) ((tvCenterSL c).map π) =
      (tvCenterSL ((g : Matrix (Fin n) (Fin n) F) *ᵥ c)).map π := fun g => by
    rw [← map_conjSubgroup, conjSubgroup_tvCenterSL]
  have hsm : ∀ {p : Fin n → F} {μ : F}, μ ≠ 0 → (tvCenterSL (μ • p)).map π =
      (tvCenterSL p).map π := fun {p μ} hμ => by rw [tvCenterSL_smul hμ]
  rintro U₁ U₂ V₁ V₂ ⟨x₁, rfl⟩ ⟨x₂, rfl⟩ ⟨y₁, rfl⟩ ⟨y₂, rfl⟩ hU hV
  obtain ⟨g₁, rfl⟩ := hπ x₁
  obtain ⟨g₂, rfl⟩ := hπ x₂
  obtain ⟨h₁, rfl⟩ := hπ y₁
  obtain ⟨h₂, rfl⟩ := hπ y₂
  rw [hconj, hconj] at hU hV
  have hp₁ : (g₁ : Matrix (Fin n) (Fin n) F) *ᵥ c ≠ 0 := mulVec_ne_zero' g₁ hc
  have hp₂ : (g₂ : Matrix (Fin n) (Fin n) F) *ᵥ c ≠ 0 := mulVec_ne_zero' g₂ hc
  have hq₁ : (h₁ : Matrix (Fin n) (Fin n) F) *ᵥ c ≠ 0 := mulVec_ne_zero' h₁ hc
  have hq₂ : (h₂ : Matrix (Fin n) (Fin n) F) *ᵥ c ≠ 0 := mulVec_ne_zero' h₂ hc
  have hp : ∀ μ : F, (g₂ : Matrix (Fin n) (Fin n) F) *ᵥ c ≠
      μ • ((g₁ : Matrix (Fin n) (Fin n) F) *ᵥ c) := by
    intro μ h
    have hμ : μ ≠ 0 := fun h0 => hp₂ (by rw [h, h0, zero_smul])
    exact hU (by rw [h, hsm hμ])
  have hq : ∀ μ : F, (h₂ : Matrix (Fin n) (Fin n) F) *ᵥ c ≠
      μ • ((h₁ : Matrix (Fin n) (Fin n) F) *ᵥ c) := by
    intro μ h
    have hμ : μ ≠ 0 := fun h0 => hq₂ (by rw [h, h0, zero_smul])
    exact hV (by rw [h, hsm hμ])
  obtain ⟨h, μ, hμ, hh₁, hh₂⟩ := exists_sl_pair hn hp₁ hq₁ hp hq
  refine ⟨π h, ?_, ?_⟩
  · rw [hconj, ← map_conjSubgroup, conjSubgroup_tvCenterSL, hh₁, hsm hμ, hconj]
  · rw [hconj, ← map_conjSubgroup, conjSubgroup_tvCenterSL, hh₂, hconj]

end Group

section Psl

variable {K : Type} [Group K] {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem two_trans_psl (hn : 3 ≤ n) (e : K ≃* StatedProj (StatedSL n F)) {T : Subgroup K}
    (hT : IsWC T) (hT1 : T ≠ ⊥) :
    ∀ U₁ U₂ V₁ V₂ : Subgroup K, (∃ x : K, U₁ = conjSubgroup x T) →
      (∃ x : K, U₂ = conjSubgroup x T) → (∃ x : K, V₁ = conjSubgroup x T) →
      (∃ x : K, V₂ = conjSubgroup x T) → U₁ ≠ U₂ → V₁ ≠ V₂ →
        ∃ g : K, conjSubgroup g U₁ = V₁ ∧ conjSubgroup g U₂ = V₂ := by
  obtain ⟨π, hπ, c, hc, rfl⟩ := exists_centre_data hn e hT hT1
  exact two_trans_lin hn π hπ hc

end Psl

end CFSG.CGT.T75E
