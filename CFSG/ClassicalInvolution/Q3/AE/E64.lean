module

public import CFSG.ClassicalInvolution.Q3.AE.PermElt
public import CFSG.ClassicalInvolution.Q3.AE.Models

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

@[expose] def e64Sigma0 : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 3 * (Equiv.swap 4 5 * Equiv.swap 5 6)

theorem e64Sigma0_spec : (∀ s ∈ fanoLines, s.map e64Sigma0.toEmbedding ∈ fanoLines ∧
      s.map e64Sigma0⁻¹.toEmbedding ∈ fanoLines) ∧
    (∀ x ∈ ({0, 1, 3} : Finset (Fin 7))ᶜ, e64Sigma0 x ∈ ({0, 1, 3} : Finset (Fin 7))ᶜ) ∧
    e64Sigma0 ^ 3 = 1 ∧ (∃ x ∈ ({0, 1, 3} : Finset (Fin 7))ᶜ, e64Sigma0 x ≠ x) ∧
    Equiv.Perm.sign e64Sigma0 = 1 := by
  decide +kernel

@[expose] def e64Sigma1 : Equiv.Perm (Fin 7) := Equiv.swap 1 2 * Equiv.swap 2 4 * (Equiv.swap 3 6 * Equiv.swap 6 5)

theorem e64Sigma1_spec : (∀ s ∈ fanoLines, s.map e64Sigma1.toEmbedding ∈ fanoLines ∧
      s.map e64Sigma1⁻¹.toEmbedding ∈ fanoLines) ∧
    (∀ x ∈ ({1, 2, 4} : Finset (Fin 7))ᶜ, e64Sigma1 x ∈ ({1, 2, 4} : Finset (Fin 7))ᶜ) ∧
    e64Sigma1 ^ 3 = 1 ∧ (∃ x ∈ ({1, 2, 4} : Finset (Fin 7))ᶜ, e64Sigma1 x ≠ x) ∧
    Equiv.Perm.sign e64Sigma1 = 1 := by
  decide +kernel

@[expose] def e64Sigma2 : Equiv.Perm (Fin 7) := Equiv.swap 1 4 * Equiv.swap 4 6 * (Equiv.swap 2 3 * Equiv.swap 3 5)

theorem e64Sigma2_spec : (∀ s ∈ fanoLines, s.map e64Sigma2.toEmbedding ∈ fanoLines ∧
      s.map e64Sigma2⁻¹.toEmbedding ∈ fanoLines) ∧
    (∀ x ∈ ({2, 3, 5} : Finset (Fin 7))ᶜ, e64Sigma2 x ∈ ({2, 3, 5} : Finset (Fin 7))ᶜ) ∧
    e64Sigma2 ^ 3 = 1 ∧ (∃ x ∈ ({2, 3, 5} : Finset (Fin 7))ᶜ, e64Sigma2 x ≠ x) ∧
    Equiv.Perm.sign e64Sigma2 = 1 := by
  decide +kernel

@[expose] def e64Sigma3 : Equiv.Perm (Fin 7) := Equiv.swap 1 2 * Equiv.swap 2 5 * (Equiv.swap 3 6 * Equiv.swap 6 4)

theorem e64Sigma3_spec : (∀ s ∈ fanoLines, s.map e64Sigma3.toEmbedding ∈ fanoLines ∧
      s.map e64Sigma3⁻¹.toEmbedding ∈ fanoLines) ∧
    (∀ x ∈ ({3, 4, 6} : Finset (Fin 7))ᶜ, e64Sigma3 x ∈ ({3, 4, 6} : Finset (Fin 7))ᶜ) ∧
    e64Sigma3 ^ 3 = 1 ∧ (∃ x ∈ ({3, 4, 6} : Finset (Fin 7))ᶜ, e64Sigma3 x ≠ x) ∧
    Equiv.Perm.sign e64Sigma3 = 1 := by
  decide +kernel

@[expose] def e64Sigma4 : Equiv.Perm (Fin 7) := Equiv.swap 0 4 * Equiv.swap 4 5 * (Equiv.swap 2 6 * Equiv.swap 6 3)

theorem e64Sigma4_spec : (∀ s ∈ fanoLines, s.map e64Sigma4.toEmbedding ∈ fanoLines ∧
      s.map e64Sigma4⁻¹.toEmbedding ∈ fanoLines) ∧
    (∀ x ∈ ({4, 5, 0} : Finset (Fin 7))ᶜ, e64Sigma4 x ∈ ({4, 5, 0} : Finset (Fin 7))ᶜ) ∧
    e64Sigma4 ^ 3 = 1 ∧ (∃ x ∈ ({4, 5, 0} : Finset (Fin 7))ᶜ, e64Sigma4 x ≠ x) ∧
    Equiv.Perm.sign e64Sigma4 = 1 := by
  decide +kernel

@[expose] def e64Sigma5 : Equiv.Perm (Fin 7) := Equiv.swap 1 5 * Equiv.swap 5 6 * (Equiv.swap 2 3 * Equiv.swap 3 4)

theorem e64Sigma5_spec : (∀ s ∈ fanoLines, s.map e64Sigma5.toEmbedding ∈ fanoLines ∧
      s.map e64Sigma5⁻¹.toEmbedding ∈ fanoLines) ∧
    (∀ x ∈ ({5, 6, 1} : Finset (Fin 7))ᶜ, e64Sigma5 x ∈ ({5, 6, 1} : Finset (Fin 7))ᶜ) ∧
    e64Sigma5 ^ 3 = 1 ∧ (∃ x ∈ ({5, 6, 1} : Finset (Fin 7))ᶜ, e64Sigma5 x ≠ x) ∧
    Equiv.Perm.sign e64Sigma5 = 1 := by
  decide +kernel

@[expose] def e64Sigma6 : Equiv.Perm (Fin 7) := Equiv.swap 0 2 * Equiv.swap 2 6 * (Equiv.swap 3 4 * Equiv.swap 4 5)

theorem e64Sigma6_spec : (∀ s ∈ fanoLines, s.map e64Sigma6.toEmbedding ∈ fanoLines ∧
      s.map e64Sigma6⁻¹.toEmbedding ∈ fanoLines) ∧
    (∀ x ∈ ({6, 0, 2} : Finset (Fin 7))ᶜ, e64Sigma6 x ∈ ({6, 0, 2} : Finset (Fin 7))ᶜ) ∧
    e64Sigma6 ^ 3 = 1 ∧ (∃ x ∈ ({6, 0, 2} : Finset (Fin 7))ᶜ, e64Sigma6 x ≠ x) ∧
    Equiv.Perm.sign e64Sigma6 = 1 := by
  decide +kernel

theorem fanoLines_compl_card : ∀ ℓ ∈ fanoLines, ℓᶜ.card = 4 := by decide +kernel

theorem fanoLines_compl_not_disjoint : ∀ ℓ ∈ fanoLines, ∀ m ∈ fanoLines, ℓ ≠ m →
    ¬ Disjoint ℓᶜ mᶜ := by
  decide +kernel

theorem e64Sets_not_disjoint {α β : Finset (Fin 7)} (hα : α ∈ e64Sets) (hβ : β ∈ e64Sets)
    (hne : α ≠ β) : ¬ Disjoint α β := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  obtain ⟨m, hm, rfl⟩ := hβ
  exact fanoLines_compl_not_disjoint ℓ hℓ m hm fun h => hne (by rw [h])

theorem ofPerm_mem_aeSubOver {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ A) (hs : Equiv.Perm.sign σ = 1) : ofPerm σ ∈ aeSubOver A := by
  refine ⟨⟨?_, hs⟩, hσ⟩
  unfold wsum
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem e64_yElt {α : Finset (Fin 7)} (hα : α ∈ e64Sets) (h : α.card = 4) :
    ∃ y ∈ e64Sub, y ^ 3 = 1 ∧ y * zBar α h = zBar α h * y ∧
      (∀ b, ∀ x ∈ memBar α h b, y * x * y⁻¹ ∈ memBar α h b) ∧
      (∀ b, ∃ x ∈ memBar α h b, y * x ≠ x * y) := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  have key : ∀ σ : Equiv.Perm (Fin 7), (∀ s ∈ fanoLines, s.map σ.toEmbedding ∈ fanoLines ∧
      s.map σ⁻¹.toEmbedding ∈ fanoLines) → Equiv.Perm.sign σ = 1 →
      (∀ x ∈ ℓᶜ, σ x ∈ ℓᶜ) → σ ^ 3 = 1 → (∃ x ∈ ℓᶜ, σ x ≠ x) →
      ∃ y ∈ e64Sub, y ^ 3 = 1 ∧ y * zBar ℓᶜ h = zBar ℓᶜ h * y ∧
        (∀ b, ∀ x ∈ memBar ℓᶜ h b, y * x * y⁻¹ ∈ memBar ℓᶜ h b) ∧
        (∀ b, ∃ x ∈ memBar ℓᶜ h b, y * x ≠ x * y) := by
    intro σ hm hsg hs h3 hmv
    obtain ⟨h1, h2, h3', h4⟩ := yElt_of_perm (by norm_num) h hs h3 hmv
    exact ⟨mkQ 7 (ofPerm σ), ⟨_, ofPerm_mem_aeSubOver hm hsg, rfl⟩, h1, h2, h3', h4⟩
  simp only [fanoLines, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma0_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma1_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma2_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma3_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma4_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma5_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma6_spec
    exact key _ hm hsg hs h3 hmv

end CFSG.ClassicalInvolution.Q3.AE
