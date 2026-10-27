module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4P

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup BS4 BL4
open scoped commutatorElement

variable {K : Type} [Field K] {φ : K →+* K}

@[expose] def fixE0G : Subgroup (GL (Fin 2 ⊕ Fin 2) K) where
  carrier := {x | (x : MB K) *ᵥ e0 = e0}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, one_mulVec]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, Units.val_mul] at hx hy ⊢
    rw [← mulVec_mulVec, hy, hx]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    conv_lhs => rw [← hx, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec]

theorem inv_mulVec_e0G {x : GL (Fin 2 ⊕ Fin 2) K} {c : K} (hx : (x : MB K) *ᵥ e0 = c • e0) :
    c ≠ 0 ∧ ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : MB K) *ᵥ e0 = c⁻¹ • e0 := by
  have h1 : ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : MB K) * (x : MB K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have he : (e0 : Fin 2 ⊕ Fin 2 → K) = c • (((x⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : MB K) *ᵥ e0) := by
    conv_lhs => rw [← one_mulVec e0, ← h1, ← mulVec_mulVec, hx]
    rw [mulVec_smul]
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at he
    simpa using congrFun he (Sum.inl 0)
  refine ⟨hc, ?_⟩
  conv_rhs => rw [he, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem commutator_le_fixE0G {G : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}
    (hG : ∀ x ∈ G, ∃ c : K, (x : MB K) *ᵥ e0 = c • e0) : ⁅G, G⁆ ≤ fixE0G := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨c, hc⟩ := hG a ha
  obtain ⟨d, hd⟩ := hG b hb
  obtain ⟨hc0, hci⟩ := inv_mulVec_e0G hc
  obtain ⟨hd0, hdi⟩ := inv_mulVec_e0G hd
  show _ *ᵥ e0 = e0
  rw [commutatorElement_def]
  simp only [Units.val_mul, ← mulVec_mulVec, hdi, mulVec_smul, hci, hd, hc, smul_smul]
  rw [show d⁻¹ * (c⁻¹ * (d * c)) = 1 by field_simp, one_smul]

theorem midB_mul_of_mem {G : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}
    (hG : ∀ x ∈ G, ∃ c : K, (x : MB K) *ᵥ e0 = c • e0)
    (hGu : ∀ x ∈ G, ((x : MB K).map φ)ᵀ * jU * (x : MB K) = jU) {x y : GL (Fin 2 ⊕ Fin 2) K}
    (hx : x ∈ G) (hy : y ∈ G) :
    midB ((x * y : GL (Fin 2 ⊕ Fin 2) K) : MB K) = midB (x : MB K) * midB (y : MB K) := by
  obtain ⟨c, hc⟩ := hG x hx
  obtain ⟨d, hd⟩ := hG y hy
  obtain ⟨-, c1, -, c3⟩ := col_e0c hc
  obtain ⟨r1, r2, -⟩ := row_e0U hd (hGu y hy)
  rw [Units.val_mul]
  exact midB_mul ⟨c1, c3⟩ ⟨r1, r2⟩

@[expose] def detMid (G : Subgroup (GL (Fin 2 ⊕ Fin 2) K))
    (hmul : ∀ x ∈ G, ∀ y ∈ G, midB ((x * y : GL (Fin 2 ⊕ Fin 2) K) : MB K) =
      midB (x : MB K) * midB (y : MB K)) : Subgroup (GL (Fin 2 ⊕ Fin 2) K) where
  carrier := {x | x ∈ G ∧ (midB (x : MB K)).det = 1}
  one_mem' := ⟨G.one_mem, by rw [Units.val_one, midB_one, det_one]⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨G.mul_mem hx.1 hy.1, by rw [hmul x hx.1 y hy.1, det_mul, hx.2, hy.2, one_mul]⟩
  inv_mem' := fun {x} hx => ⟨G.inv_mem hx.1, by
    have e := congrArg Matrix.det (hmul x hx.1 x⁻¹ (G.inv_mem hx.1))
    rw [mul_inv_cancel, Units.val_one, midB_one, det_one, det_mul, hx.2, one_mul] at e
    exact e.symm⟩

theorem det_midB_of_mem {G : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}
    (hmul : ∀ x ∈ G, ∀ y ∈ G, midB ((x * y : GL (Fin 2 ⊕ Fin 2) K) : MB K) =
      midB (x : MB K) * midB (y : MB K)) :
    ∀ x ∈ ⁅G, G⁆, (midB (x : MB K)).det = 1 := by
  have hinv : ∀ x ∈ G, (midB (x : MB K)).det *
      (midB ((x⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : MB K)).det = 1 := by
    intro x hx
    rw [← det_mul, ← hmul x hx _ (G.inv_mem hx), mul_inv_cancel, Units.val_one, midB_one,
      det_one]
  have hle : ⁅G, G⁆ ≤ detMid G hmul := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab := G.mul_mem ha hb
    have haba := G.mul_mem hab (G.inv_mem ha)
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact G.mul_mem haba (G.inv_mem hb)
    · rw [commutatorElement_def, hmul _ haba _ (G.inv_mem hb), hmul _ hab _ (G.inv_mem ha),
        hmul _ ha _ hb, det_mul, det_mul, det_mul]
      linear_combination (midB (b : MB K)).det *
        (midB ((b⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : MB K)).det * hinv a ha + hinv b hb
  exact fun x hx => (hle hx).2

theorem false_of_pointU (h2 : (2 : K) ≠ 0) {G : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}
    (hG : ∀ x ∈ G, ∃ c : K, (x : MB K) *ᵥ e0 = c • e0)
    (hGu : ∀ x ∈ G, ((x : MB K).map φ)ᵀ * jU * (x : MB K) = jU)
    {x₁ x₂ : GL (Fin 2 ⊕ Fin 2) K} (hx₁ : x₁ ∈ ⁅G, G⁆) (hx₂ : x₂ ∈ ⁅G, G⁆)
    (hsq₁ : ∃ c : K, ((x₁ * x₁ : GL (Fin 2 ⊕ Fin 2) K) : MB K) = c • 1)
    (hsq₂ : ∃ c : K, ((x₂ * x₂ : GL (Fin 2 ⊕ Fin 2) K) : MB K) = c • 1)
    (hsq₁₂ : ∃ c : K, ((x₁ * x₂ * (x₁ * x₂) : GL (Fin 2 ⊕ Fin 2) K) : MB K) = c • 1)
    (hne₁ : x₁ ≠ 1) (hne₂ : x₂ ≠ 1) (hne₁₂ : x₁ * x₂ ≠ 1) : False := by
  have hD := commutator_le_fixE0G hG
  have hmul : ∀ x ∈ G, ∀ y ∈ G, midB ((x * y : GL (Fin 2 ⊕ Fin 2) K) : MB K) =
      midB (x : MB K) * midB (y : MB K) := fun x hx y hy => midB_mul_of_mem hG hGu hx hy
  have hdet := det_midB_of_mem hmul
  have hGG : ⁅G, G⁆ ≤ G := Subgroup.commutator_le_self G
  have key : ∀ x ∈ ⁅G, G⁆, (∃ c : K, ((x * x : GL (Fin 2 ⊕ Fin 2) K) : MB K) = c • 1) →
      x ≠ 1 → midB (x : MB K) = -1 := by
    rintro x hx ⟨c, hc⟩ hne
    have hfix : (x : MB K) *ᵥ e0 = e0 := hD hx
    have hfix2 : ((x * x : GL (Fin 2 ⊕ Fin 2) K) : MB K) *ᵥ e0 = e0 := hD (mul_mem hx hx)
    rw [hc] at hfix2
    have hc1 : c = 1 := by simpa using congrFun hfix2 (Sum.inl 0)
    rw [hc1, one_smul] at hc
    have hM : (x : MB K) * (x : MB K) = 1 := by rw [← Units.val_mul]; exact hc
    have hmid2 := hmul x (hGG hx) x (hGG hx)
    rw [hc, midB_one] at hmid2
    rcases eq_one_or_neg_one_of_sq h2 hmid2.symm (hdet x hx) with h | h
    · exfalso
      apply hne
      obtain ⟨r1, r2, r3⟩ := row_e0U (c := 1) (by rw [one_smul]; exact hfix) (hGu x (hGG hx))
      rw [map_one, one_mul] at r3
      exact Units.ext (by
        rw [Units.val_one]
        exact eq_one_of_midB_eq_one' h2 hfix ⟨r1, r2, r3⟩ hM h)
    · exact h
  have e12 := key (x₁ * x₂) (mul_mem hx₁ hx₂) hsq₁₂ hne₁₂
  rw [hmul x₁ (hGG hx₁) x₂ (hGG hx₂), key x₁ hx₁ hsq₁ hne₁, key x₂ hx₂ hsq₂ hne₂, neg_one_mul,
    neg_neg] at e12
  have h00 := congrFun (congrFun e12 0) 0
  rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h00
  exact h2 (by linear_combination h00)

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
