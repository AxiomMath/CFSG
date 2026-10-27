module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Suz
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.HeldB

@[expose] def InvolutionTwoClasses {Ω : Type*} [Group Ω] (M : Subgroup Ω) : Prop :=
  ∀ σ₁ ∈ M, ∀ σ₂ ∈ M, ∀ τ ∈ M, orderOf σ₁ = 2 → orderOf σ₂ = 2 → orderOf τ = 2 →
    (∃ m ∈ M, τ = m * σ₁ * m⁻¹) ∨ (∃ m ∈ M, τ = m * σ₂ * m⁻¹) ∨ ∃ m ∈ M, σ₂ = m * σ₁ * m⁻¹

theorem exists_conj_conj {Ω : Type*} [Group Ω] {M : Subgroup Ω} {m₁ m₂ : Ω} (h₁ : m₁ ∈ M)
    (h₂ : m₂ ∈ M) (x : Ω) : ∃ m ∈ M, m₂ * x * m₂⁻¹ = m * (m₁ * x * m₁⁻¹) * m⁻¹ :=
  ⟨m₂ * m₁⁻¹, M.mul_mem h₂ (M.inv_mem h₁), by group⟩

theorem involutionTwoClasses_of_reps {Ω : Type*} [Group Ω] {M : Subgroup Ω} {a b : Ω}
    (h : ∀ τ ∈ M, orderOf τ = 2 → (∃ m ∈ M, τ = m * a * m⁻¹) ∨ ∃ m ∈ M, τ = m * b * m⁻¹) :
    InvolutionTwoClasses M := by
  intro σ₁ hσ₁ σ₂ hσ₂ τ hτ h1 h2 h3
  rcases h σ₁ hσ₁ h1 with ⟨m₁, hm₁, rfl⟩ | ⟨m₁, hm₁, rfl⟩ <;>
    rcases h σ₂ hσ₂ h2 with ⟨m₂, hm₂, rfl⟩ | ⟨m₂, hm₂, rfl⟩ <;>
    rcases h τ hτ h3 with ⟨m₃, hm₃, rfl⟩ | ⟨m₃, hm₃, rfl⟩
  all_goals first
    | exact Or.inl (exists_conj_conj hm₁ hm₃ _)
    | exact Or.inr (Or.inl (exists_conj_conj hm₂ hm₃ _))
    | exact Or.inr (Or.inr (exists_conj_conj hm₁ hm₂ _))

section Suz


theorem exists_centralizer_not_mem_suzM {k : ℕ} (hk : k < 2) :
    ∃ s ∈ suzT, s * suzInv k = suzInv k * s ∧ s ∉ suzM := by
  by_contra hcon
  push Not at hcon
  have hle : suzT ⊓ centralizer ({suzInv k} : Set (Equiv.Perm (Fin 1782))) ≤
      suzM ⊓ centralizer ({suzInv k} : Set (Equiv.Perm (Fin 1782))) := fun s hs =>
    ⟨hcon s hs.1 (mem_centralizer_singleton_iff.mp hs.2), hs.2⟩
  have h := Subgroup.card_le_of_le hle
  rw [card_suzT_inf_centralizer (by omega), card_suzM_inf_centralizer (by omega)] at h
  interval_cases k <;> simp [invFullOrders, invInnerOrders] at h

theorem exists_suzM_conj {k : ℕ} (hk : k < 2) {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) :
    ∃ m ∈ suzM, c * suzInv k * c⁻¹ = m * suzInv k * m⁻¹ := by
  by_cases hcM : c ∈ suzM
  · exact ⟨c, hcM, rfl⟩
  obtain ⟨s, hsT, hs, hsM⟩ := exists_centralizer_not_mem_suzM hk
  have hmem : (⟨c, hc⟩ : suzT) * ⟨s, hsT⟩ ∈ suzM.subgroupOf suzT := by
    rw [mul_mem_iff_of_index_two suzM_index_T, mem_subgroupOf, mem_subgroupOf]
    exact iff_of_false hcM hsM
  refine ⟨c * s, hmem, ?_⟩
  calc c * suzInv k * c⁻¹ = c * (suzInv k * s) * s⁻¹ * c⁻¹ := by group
    _ = c * (s * suzInv k) * s⁻¹ * c⁻¹ := by rw [hs]
    _ = c * s * suzInv k * (c * s)⁻¹ := by group

theorem suzM_conj_cases {g : Equiv.Perm (Fin 1782)}
    (hg : g ∈ suzM) (h2 : orderOf g = 2) :
    (∃ m ∈ suzM, g = m * suzInv 0 * m⁻¹) ∨ ∃ m ∈ suzM, g = m * suzInv 1 * m⁻¹ := by
  obtain ⟨c, hc, h | h⟩ := suzM_involution_class hg h2
  · obtain ⟨m, hm, hcm⟩ := exists_suzM_conj (k := 0) (by norm_num) hc
    exact Or.inl ⟨m, hm, h ▸ hcm⟩
  · obtain ⟨m, hm, hcm⟩ := exists_suzM_conj (k := 1) (by norm_num) hc
    exact Or.inr ⟨m, hm, h ▸ hcm⟩

theorem suz_involutionTwoClasses : InvolutionTwoClasses suzM :=
  involutionTwoClasses_of_reps fun _ hτ h2 => suzM_conj_cases hτ h2

end Suz

theorem he_involutionTwoClasses :
    InvolutionTwoClasses heP :=
  involutionTwoClasses_of_reps fun _ hτ h2 => involution_conj_cases hτ h2

end CFSG.ComponentClassification.AS81
