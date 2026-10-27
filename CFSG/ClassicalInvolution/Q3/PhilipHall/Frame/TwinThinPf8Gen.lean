module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem commutes_of_map_le_gen {P : Set (Subgroup G)} (hPΩ : P ⊆ CoreAssembly.conjClass K₀) {n : ℕ}
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hne : L₁ ≠ L₂) {T : Subgroup (AE.AEQ n)} (hT2 : IsPGroup 2 T)
    (h₁T : (L₁.subgroupOf (pSpan P)).map I.φ ≤ T) (h₂T : (L₂.subgroupOf (pSpan P)).map I.φ ≤ T) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have hQ2 : IsPGroup 2 ((T.comap I.φ).map (pSpan P).subtype) :=
    (hT2.comap_of_ker_isPGroup I.φ hk).map _
  have hLQ : ∀ {L : Subgroup G}, L ∈ P → (L.subgroupOf (pSpan P)).map I.φ ≤ T →
      L ≤ (T.comap I.φ).map (pSpan P).subtype := by
    intro L hL hLS l hl
    exact ⟨⟨l, le_pSpan hL hl⟩, hLS (I.mem_map hL hl), rfl⟩
  exact S.commutes_of_le (hPΩ h₁) (hPΩ h₂) hne hQ2 (hLQ h₁ h₁T) (hLQ h₂ h₂T)

theorem isPGroup_map_gen {P : Set (Subgroup G)} (hPΩ : P ⊆ CoreAssembly.conjClass K₀) {n : ℕ}
    (I : AEIdent P n) {L : Subgroup G} (hL : L ∈ P) :
    IsPGroup 2 ((L.subgroupOf (pSpan P)).map I.φ) :=
  ((S.hs.two L (hPΩ hL)).of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).symm).map _

theorem eq_of_map_le_gen {P : Set (Subgroup G)} (hPΩ : P ⊆ CoreAssembly.conjClass K₀) {n : ℕ}
    (hn : 5 ≤ n) (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P)
    (hle : (L₁.subgroupOf (pSpan P)).map I.φ ≤ (L₂.subgroupOf (pSpan P)).map I.φ) : L₁ = L₂ := by
  by_contra hne
  have hc := S.commutes_of_map_le_gen hPΩ I hk h₁ h₂ hne (S.isPGroup_map_gen hPΩ I h₂) hle le_rfl
  obtain ⟨α, h, b, hlab⟩ := I.label L₁ h₁
  obtain ⟨x, hx, x', hx', hxx'⟩ := AE.exists_not_comm_memBar hn α h b
  rw [← hlab] at hx hx'
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map h₁ hx
  obtain ⟨l', hl', hl'e⟩ := I.exists_of_mem_map h₂ (hle hx')
  apply hxx'
  rw [← hl'e, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl l' hl')

theorem commutes_of_map_comm_gen {P : Set (Subgroup G)} (hPΩ : P ⊆ CoreAssembly.conjClass K₀)
    {n : ℕ} (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ P)
    (h₂ : L₂ ∈ P) (hne : L₁ ≠ L₂)
    (hc : ∀ x ∈ (L₁.subgroupOf (pSpan P)).map I.φ, ∀ y ∈ (L₂.subgroupOf (pSpan P)).map I.φ,
      x * y = y * x) :
    ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have hN : (L₁.subgroupOf (pSpan P)).map I.φ ≤
      Subgroup.normalizer ((L₂.subgroupOf (pSpan P)).map I.φ : Set (AE.AEQ n)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hc x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hc x hx _ hy
      have h2 : x * y * x⁻¹ = y :=
        mul_left_cancel (h1.trans (show x * y * x⁻¹ * x = x * y by group))
      rwa [h2] at hy
  have hsup := (S.isPGroup_map_gen hPΩ I h₁).to_sup_of_normal_right'
    (S.isPGroup_map_gen hPΩ I h₂) hN
  exact S.commutes_of_map_le_gen hPΩ I hk h₁ h₂ hne hsup le_sup_left le_sup_right

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
