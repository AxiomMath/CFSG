
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowOffenderBase

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowP

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ eq_xorBits xorBits_two_pow_of_lt)

section Bound

theorem offender_bound {u : Bool} {A : Subgroup (Equiv.Perm (Fin 64))} (hA : A ≤ Gq u)
    (hcomm : ∀ σ ∈ A, ∀ τ ∈ A, σ * τ = τ * σ) (hsq : ∀ σ ∈ A, σ * σ = 1) (hne : A ≠ ⊥) :
    Nat.card A * Nat.card {e : Fin 512 // ∀ σ ∈ A, eAct u σ e = e} *
      Nat.card {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ A, σ v = v} < 2 ^ (if u then 9 else 12) := by
  have hAp : IsPGroup 2 A := fun σ => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two, hsq σ σ.2]; rfl)⟩
  obtain ⟨g, hg, hgA⟩ := exists_conj_le_Psub hA hAp
  let A' := A.map (MulAut.conj g).toMonoidHom
  have hmem' : ∀ {σ'}, σ' ∈ A' ↔ ∃ σ ∈ A, g * σ * g⁻¹ = σ' := by
    intro σ'
    simp [A']
  have hA' : A' ≤ Psub u := by
    intro σ' h
    obtain ⟨σ, hσ, rfl⟩ := hmem'.1 h
    exact hgA σ hσ
  have hcomm' : ∀ σ ∈ A', ∀ τ ∈ A', σ * τ = τ * σ := by
    intro σ' h τ' h'
    obtain ⟨σ, hσ, rfl⟩ := hmem'.1 h
    obtain ⟨τ, hτ, rfl⟩ := hmem'.1 h'
    calc g * σ * g⁻¹ * (g * τ * g⁻¹) = g * (σ * τ) * g⁻¹ := by group
      _ = g * (τ * σ) * g⁻¹ := by rw [hcomm σ hσ τ hτ]
      _ = g * τ * g⁻¹ * (g * σ * g⁻¹) := by group
  have hsq' : ∀ σ ∈ A', σ * σ = 1 := by
    intro σ' h
    obtain ⟨σ, hσ, rfl⟩ := hmem'.1 h
    calc g * σ * g⁻¹ * (g * σ * g⁻¹) = g * (σ * σ) * g⁻¹ := by group
      _ = 1 := by rw [hsq σ hσ]; group
  have hne' : A' ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.eq_bot_iff_forall] at h ⊢
    intro σ hσ
    have := h _ (hmem'.2 ⟨σ, hσ, rfl⟩)
    calc σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  have h := offender_bound_P hA' hcomm' hsq' hne'
  have hc1 : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc2 : Nat.card {e : Fin 512 // ∀ σ ∈ A', eAct u σ e = e} =
      Nat.card {e : Fin 512 // ∀ σ ∈ A, eAct u σ e = e} := by
    refine Nat.card_congr
      { toFun := fun e => ⟨⟨eAct u g⁻¹ e.1, eAct_lt _ _ _⟩, fun σ hσ => ?_⟩
        invFun := fun e => ⟨⟨eAct u g e.1, eAct_lt _ _ _⟩, fun σ' hσ' => ?_⟩
        left_inv := fun e => Subtype.ext (Fin.ext (eAct_mul_inv hg e.1.2))
        right_inv := fun e => Subtype.ext (Fin.ext (eAct_inv_mul hg e.1.2)) }
    · have h1 := e.2 _ (hmem'.2 ⟨σ, hσ, rfl⟩)
      have h2 := eAct_conj hg (hA hσ) (eAct_lt u g⁻¹ e.1)
      rw [eAct_mul_inv hg e.1.2, h1] at h2
      have h3 := congrArg (eAct u g⁻¹) h2
      rw [eAct_inv_mul hg (eAct_lt _ _ _)] at h3
      exact h3.symm
    · obtain ⟨σ, hσ, rfl⟩ := hmem'.1 hσ'
      simp only
      rw [eAct_conj hg (hA hσ) e.1.2, e.2 σ hσ]
  have hc3 : Nat.card {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ A', σ v = v} =
      Nat.card {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ A, σ v = v} := by
    refine Nat.card_congr
      { toFun := fun v => ⟨g⁻¹ v.1, ?_, fun σ hσ => ?_⟩
        invFun := fun v => ⟨g v.1, ?_, fun σ' hσ' => ?_⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
    · rw [q_eAct (inv_mem hg), v.2.1, eAct_zero]
    · have := v.2.2 _ (hmem'.2 ⟨σ, hσ, rfl⟩)
      apply g.injective
      simp only [Equiv.Perm.coe_mul, Function.comp_apply] at this
      calc g (σ (g⁻¹ v.1)) = v.1 := this
        _ = g (g⁻¹ v.1) := by simp
    · rw [q_eAct hg, v.2.1, eAct_zero]
    · obtain ⟨σ, hσ, rfl⟩ := hmem'.1 hσ'
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [show g⁻¹ (g v.1) = v.1 by simp, v.2.2 σ hσ]
  rwa [hc1, hc2, hc3] at h

end Bound

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
