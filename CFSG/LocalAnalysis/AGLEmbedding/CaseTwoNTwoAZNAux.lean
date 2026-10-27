module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClassAux
import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedB

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.normal_of_two_components (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤)
    (hL₁ : ¬ L₁ ≤ Y₀) (hL₂ : L₂ ≤ Y₀) : L₁.Normal ∧ L₂.Normal := by
  have hne : L₁ ≠ L₂ := fun heq => hL₁ (heq ▸ hL₂)
  have htop := h.top_le_sup_layer hcyc h₁ h₂ hne
  have key : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      (∀ x ∈ Y₀, L.map (MulAut.conj x).toMonoidHom ≤ L) → L.Normal := fun L hL hY₀ =>
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop.trans (sup_le
      (fun x hx => mem_normalizer_of_conj_map_le (hY₀ x hx))
      (CFSG.LocalCores.layer_le_normalizer ((CFSG.isComponent_iff_open L).mpr hL)))))
  have hconj : ∀ {L : Subgroup Y}, IsComponentOf L ⊤ → ∀ x : Y,
      L.map (MulAut.conj x).toMonoidHom = L₁ ∨ L.map (MulAut.conj x).toMonoidHom = L₂ :=
    fun hL x => h.eq_or_eq_of_isComponentOf h₁ h₂ hne
      ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj x) _).mpr hL)
  refine ⟨key L₁ h₁ fun x hx => ?_, key L₂ h₂ fun x hx => ?_⟩
  · rcases hconj h₁ x with heq | heq
    · exact heq.le
    · refine absurd (fun l hl => ?_) hL₁
      have hxl : x * l * x⁻¹ ∈ Y₀ := hL₂ (heq ▸ ⟨l, hl, rfl⟩)
      have e : l = x⁻¹ * (x * l * x⁻¹) * x := by group
      rw [e]
      exact Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem hx) hxl) hx
  · rcases hconj h₂ x with heq | heq
    · refine absurd (heq ▸ ?_) hL₁
      rintro _ ⟨l, hl, rfl⟩
      exact Y₀.mul_mem (Y₀.mul_mem hx (hL₂ hl)) (Y₀.inv_mem hx)
    · exact heq.le

theorem ReducedNongeneration.centralizer_le_of_not_le (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤)
    (hL₁ : ¬ L₁ ≤ Y₀) (hL₂ : L₂ ≤ Y₀) : Subgroup.centralizer (L₁ : Set Y) ≤ Y₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hne : L₁ ≠ L₂ := fun heq => hL₁ (heq ▸ hL₂)
  have : L₂.Normal := (h.normal_of_two_components hcyc h₁ h₂ hL₁ hL₂).2
  obtain ⟨t₁, ht₁, ht₁p, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb h₁
  obtain ⟨t₂, ht₂, ht₂p, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb h₂
  have hNQ := h.normalizer_sup_zpowers_le_of_ne hcyc h₁ h₂ hne ht₁ ht₁p ht₂ ht₂p
  have h₂₁ := le_centralizer_of_component_ne h₂ h₁ hne.symm
  obtain ⟨S, hS⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (Subgroup.Normal.isSubnormal ‹L₂.Normal›)
  have htop := Sylow.normalizer_sup_eq_top S
  rw [hS] at htop
  intro c hc
  have hc' : c ∈ ((Subgroup.normalizer (((Rb : Subgroup Y) ⊓ L₂ : Subgroup Y) : Set Y) ⊔ L₂ :
      Subgroup Y) : Set Y) := by
    rw [htop]
    trivial
  rw [Subgroup.mul_normal] at hc'
  obtain ⟨n, hn, l, hl, rfl⟩ := hc'
  have hnC : n ∈ Subgroup.centralizer (L₁ : Set Y) := by
    have h1 := (Subgroup.centralizer (L₁ : Set Y)).mul_mem hc
      ((Subgroup.centralizer (L₁ : Set Y)).inv_mem (h₂₁ hl))
    rwa [mul_inv_cancel_right] at h1
  have hn₁ : n * t₁ * n⁻¹ = t₁ := by
    rw [← Subgroup.mem_centralizer_iff.mp hnC t₁ ht₁.2, mul_inv_cancel_right]
  have := hcyc L₂ h₂
  have hn₂ : n * t₂ * n⁻¹ ∈ Subgroup.zpowers t₂ :=
    conj_mem_zpowers_of_isCyclic (T := (Rb : Subgroup Y) ⊓ L₂) rfl ht₂
      ((Subgroup.mem_normalizer_iff.mp hn t₂).mp ht₂)
  have hnY₀ : n ∈ Y₀ := hNQ (mem_normalizer_sup_zpowers
    (by rw [hn₁]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁))
    (Subgroup.mem_sup_right hn₂))
  exact Y₀.mul_mem hnY₀ (hL₂ hl)

theorem ReducedNongeneration.le_of_le_centralizer (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤)
    (hL₁ : ¬ L₁ ≤ Y₀) (hL₂ : L₂ ≤ Y₀) {U : Subgroup Y}
    (hU : U ≤ Subgroup.centralizer (L₁ : Set Y)) (hU1 : U ≠ ⊥)
    (hCU : Subgroup.centralizer (L₁ : Set Y) ≤ Subgroup.normalizer (U : Set Y)) : L₂ ≤ U := by
  have hne : L₁ ≠ L₂ := fun heq => hL₁ (heq ▸ hL₂)
  have : L₂.Normal := (h.normal_of_two_components hcyc h₁ h₂ hL₁ hL₂).2
  have hCC := h.centralizer_inf_centralizer_eq_bot h₁ h₂ hne (hcyc L₁ h₁) (hcyc L₂ h₂)
    (h.pCore_eq_bot_of_two_components h₂ h₁ hne.symm (hcyc L₂ h₂) hL₁)
  have : IsSimpleGroup L₂ :=
    isSimpleGroup_of_center_eq_bot h₂ (h.center_eq_bot_of_isCyclic h₂ (hcyc L₂ h₂))
  refine le_of_not_le_centralizer ((le_centralizer_of_component_ne h₂ h₁ hne.symm).trans hCU)
    (le_top.trans (Subgroup.normalizer_eq_top (H := L₂)).ge) fun hUC => hU1 ?_
  exact le_bot_iff.mp (hCC ▸ le_inf hU hUC)

end Reduced

end CFSG.AGLEmbedding
