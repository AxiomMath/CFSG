module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {n : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

theorem exists_four_of_layer [Finite X] (hρ : IsPermAction θ ρ) (hn : 4 ≤ n) {Ms C : Subgroup X}
    (hMsle : Ms ≤ M ⊓ C) {τ : Perm (Fin n)}
    {χs : ↥Ms ⧸ pPrimeCore 2 ↥Ms ≃* alternatingGroup ↥(τ.supportᶜ : Finset (Fin n))}
    (hχs : ∀ (z : ↥Ms) (hz : (z : X) ∈ M),
      Perm.ofSubtype ((χs (z : ↥Ms ⧸ pPrimeCore 2 ↥Ms) : alternatingGroup _) :
        Perm ↥(τ.supportᶜ : Finset (Fin n))) = coreImage θ hz)
    {k : ℕ} (hk : Fintype.card ↥(τ.supportᶜ : Finset (Fin n)) = k) {R₀ D : Subgroup X}
    (hR₀ : R₀ ≤ Ms ⊓ D) {u : Perm (Fin k)}
    {χ₀ : ↥R₀ ⧸ pPrimeCore 2 ↥R₀ ≃* alternatingGroup ↥(u.supportᶜ : Finset (Fin k))}
    (hχ₀ : ∀ (z : ↥R₀) (hz : (z : X) ∈ Ms),
      Perm.ofSubtype ((χ₀ (z : ↥R₀ ⧸ pPrimeCore 2 ↥R₀) : alternatingGroup _) :
        Perm ↥(u.supportᶜ : Finset (Fin k))) =
          coreImage (χs.trans (Fintype.equivFinOfCardEq hk).altCongrHom) hz)
    {r : ℕ} (hcard : Fintype.card ↥(u.supportᶜ : Finset (Fin k)) = r) (hr5 : 5 ≤ r)
    (hr6 : r ≠ 6) :
    ∃ f ∈ R₀, ∃ hfMs : f ∈ Ms, f * f = 1 ∧
      (ρ ⟨f, le_normalizer (mem_inf.mp (hMsle hfMs)).1⟩).support.card = 4 := by
  classical
  set θs := χs.trans (Fintype.equivFinOfCardEq hk).altCongrHom with hθsdef
  set χ₀' := χ₀.trans (Fintype.equivFinOfCardEq hcard).altCongrHom with hχ₀'def
  obtain ⟨ρa, hρa⟩ := exists_isPermAction (M := R₀) hr5 hr6 χ₀'
  obtain ⟨δ, hδA, hδ2, hδ4, -, -⟩ := exists_four_of_fix (1 : Perm (Fin r))
    (by rw [Perm.support_one, Finset.card_empty]; omega)
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hδ4
    omega
  obtain ⟨f, hfR₀, -, hf2, hρaf⟩ := hρa.exists_involution_lift (by omega) (one_mem _)
    (one_mul 1) hδA hδ2 hδ1 (by rw [show (⟨1, one_mem _⟩ : ↥(normalizer (R₀ : Set X))) = 1 from
      rfl, map_one, mul_one, one_mul])
  have hfMs : f ∈ Ms := (mem_inf.mp (hR₀ hfR₀)).1
  have hfM : f ∈ M := (mem_inf.mp (hMsle hfMs)).1
  refine ⟨f, hfR₀, hfMs, hf2, ?_⟩
  have h1 : (coreImage θs hfMs).support.card = δ.support.card := by
    have h3 := hρa.apply_of_mem (by omega) ⟨f, hfR₀⟩
    rw [hρaf] at h3
    rw [h3, hχ₀'def, MulEquiv.trans_apply, Equiv.altCongrHom_apply_coe, card_support_permCongr,
      ← card_support_ofSubtype, hχ₀ ⟨f, hfR₀⟩ hfMs]
  have h2 : (coreImage θs hfMs).support.card = (ρ ⟨f, le_normalizer hfM⟩).support.card := by
    unfold coreImage
    rw [hθsdef, MulEquiv.trans_apply, Equiv.altCongrHom_apply_coe, card_support_permCongr,
      ← card_support_ofSubtype, hχs ⟨f, hfMs⟩ hfM]
    unfold coreImage
    rw [← hρ.apply_of_mem hn ⟨f, hfM⟩]
  rw [← h2, h1, hδ4]

end CFSG.ComponentClassification.SolMax
