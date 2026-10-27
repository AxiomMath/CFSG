module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dTag
public import CFSG.ClassicalInvolution.SmallCases.NDB5Sec

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

section Defs

variable {G : Type} [Group G]

@[expose] def WeakClosureAt (s : G) (L₁ : Subgroup G) : Prop :=
  ∀ h ∈ Subgroup.centralizer ({s} : Set G),
    (∀ x ∈ modOdd s (conjSub h L₁), ∀ y ∈ modOdd s L₁, x * y = y * x) →
      modOdd s (conjSub h L₁) = modOdd s L₁

@[expose] def NormalizesImageAt (s z₂ : G) (L₁ : Subgroup G) : Prop :=
  ∀ h : z₂ ∈ Subgroup.centralizer ({s} : Set G),
    conjSub (oddQuotMk s ⟨z₂, h⟩) (modOdd s L₁) = modOdd s L₁

theorem normalizesImageAt_of_conjSub_eq {s z₂ : G} {L₁ : Subgroup G} (h : conjSub z₂ L₁ = L₁) :
    NormalizesImageAt s z₂ L₁ := fun hc => by
  rw [← NDB.S.modOdd_conjSub hc, h]

theorem normalizesImageAt_of_layer {s z₂ : G} {Y L₁ : Subgroup G} (hz₂Y : z₂ ∈ Y)
    (hz₂C : z₂ ∈ Subgroup.centralizer ({s} : Set G))
    (hn : ∀ g ∈ Y, g ∈ Subgroup.centralizer ({s} : Set G) → conjSub g L₁ = L₁) :
    NormalizesImageAt s z₂ L₁ :=
  normalizesImageAt_of_conjSub_eq (hn z₂ hz₂Y hz₂C)

end Defs

section Route


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem tag_of_sComponent_wc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {A : Subgroup G} {s z₁ z₂ : G}
    {L₁ L₂ : Subgroup G} (hN : NormalizesLayer (NDB.S.sFamily s L₁ L₂) s)
    (D : LocalLieSystemAt p f (NDB.S.sFamily s L₁ L₂) s) (j₀ : Fin D.card)
    (R₁ R₂ : Subgroup (compModel D j₀).K)
    (hSC : NDB.S.SComponent A s z₁ z₂ L₁ L₂ hN D j₀ R₁ R₂) (hwc : WeakClosureAt s L₁) :
    (D.tag j₀ = .PSL ∧ D.rank j₀ = 3) ∨ (D.tag j₀ = .PSU ∧ D.rank j₀ = 3) ∨
      D.tag j₀ = .G2 ∨ D.tag j₀ = .trialityD4 := by
  by_cases hG2 : D.tag j₀ = .G2
  · exact Or.inr (Or.inr (Or.inl hG2))
  by_cases hD4 : D.tag j₀ = .trialityD4
  · exact Or.inr (Or.inr (Or.inr hD4))
  by_cases hA2 : D.tag j₀ = .PSL ∧ D.rank j₀ = 3
  · exact Or.inl hA2
  by_cases h2A2 : D.tag j₀ = .PSU ∧ D.rank j₀ = 3
  · exact Or.inr (Or.inl h2A2)
  exfalso
  set ψ := secComponentHom hN D j₀ with hψ
  have hA1 : ¬ (D.tag j₀ = .PSL ∧ D.rank j₀ = 2) := by
    intro h1
    apply hSC.ne
    rw [← hSC.img₁, ← hSC.img₂, NDB.WC.fund_eq_top_of_A1 D j₀ h1 hSC.fund₁,
      NDB.WC.fund_eq_top_of_A1 D j₀ h1 hSC.fund₂]
  have hq' : 5 ≤ p ^ D.exp j₀ := by
    rcases D.exp_eq j₀ with h1 | ⟨h1, -⟩
    · rw [h1]
      exact hq
    · exact absurd h1 hD4
  obtain ⟨S', hS', hSR, hc⟩ := NDB.WC.exists_commuting_partner hp2 hq' (D.isFundTag j₀)
    (D.admissible j₀) hA1 hA2 h2A2 hG2 hD4 hSC.fund₁
  obtain ⟨k, hk⟩ := ModelFacts.fundamentalSingleClass (D.tag j₀) (D.rank j₀) p (D.exp j₀)
    Fact.out (D.isFundTag j₀) (D.admissible j₀) hG2 hD4 R₁ hSC.fund₁ S' hS'
  obtain ⟨h, hhC, hhimg⟩ := hSC.conj₁ k
  have hkS : conjSub k R₁ = S' := hk.symm
  have hhimg' : S'.map ψ = modOdd s (conjSub h L₁) := by
    rw [← hkS]
    exact hhimg
  have hcomm : ∀ x ∈ modOdd s (conjSub h L₁), ∀ y ∈ modOdd s L₁, x * y = y * x := by
    rw [← hhimg', ← hSC.img₁]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc b hb a ha]
  have hwc' := hwc h hhC hcomm
  have h4 : 4 ≤ p ^ D.exp j₀ := by omega
  have hper : ∀ {R : Subgroup (compModel D j₀).K},
      R ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D → R ≤ ⁅R, R⁆ := fun hR =>
    ModelFacts.fundPerfect_core (D.tag j₀) (D.rank j₀) p (D.exp j₀) hp2 (D.isFundTag j₀)
      (D.admissible j₀) h4 _ hR
  refine hSR (RouteD.eq_of_map_eq_of_perfect ψ hSC.ker (hper hS') (hper hSC.fund₁) ?_)
  rw [hhimg', hwc', hSC.img₁]

end Route

end CFSG.ClassicalInvolution.Q3.Q3AM
