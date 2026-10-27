module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.Asc77.AscIHSectE
public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected

namespace MuTab

section Orth

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem muKind_pOmegaOdd_three (π : Bool) : muKind π .POmegaOdd 3 = .s4 := by
  cases π <;> simp [muKind]

theorem muKind_pOmegaMinus_four (π : Bool) : muKind π .POmegaMinus 4 = .s4 := by
  cases π <;> simp [muKind]

theorem shapeS4_pOmegaOdd3 (M : Ih8Model p f Ω .POmegaOdd 3 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty)
    (hsplit : ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K) : ShapeS4 Ω := by
  have hG2 : StatedLieTag.POmegaOdd ≠ .G2 := by decide
  have hD4 : StatedLieTag.POmegaOdd ≠ .trialityD4 := by decide
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
    noThree_odd3 hp2 hq' M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
      cAB cAS
  refine ⟨M.muTab_matching hΩ hp2 hq hG2 hD4 hMatch, M.muTab_edge hΩ hp2 hq hG2 hD4 ?_, hsplit⟩
  obtain ⟨R, hR, S, hS', hRS, hc⟩ := ih8SmallEdge p _ _ _ M.admissible hp2 hq'
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  exact ⟨R, M.fund_subset_cls hne hG2 hD4 hR, S, M.fund_subset_cls hne hG2 hD4 hS', hRS, hc⟩

theorem shapeS4_pOmegaMinus4 (M : Ih8Model p f Ω .POmegaMinus 4 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty)
    (hsplit : ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K) : ShapeS4 Ω := by
  have hG2 : StatedLieTag.POmegaMinus ≠ .G2 := by decide
  have hD4 : StatedLieTag.POmegaMinus ≠ .trialityD4 := by decide
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
    noThree_minus4 hp2 hq' M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
      cAB cAS
  refine ⟨M.muTab_matching hΩ hp2 hq hG2 hD4 hMatch, M.muTab_edge hΩ hp2 hq hG2 hD4 ?_, hsplit⟩
  obtain ⟨R, hR, S, hS', hRS, hc⟩ := ih8SmallEdge p _ _ _ M.admissible hp2 hq'
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  exact ⟨R, M.fund_subset_cls hne hG2 hD4 hR, S, M.fund_subset_cls hne hG2 hD4 hS', hRS, hc⟩

theorem split_pOmegaOdd3_plus (M : Ih8Model p f Ω .POmegaOdd 3 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq4 : p ^ f % 4 = 1) :
    ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K := by
  have hG2 : StatedLieTag.POmegaOdd ≠ .G2 := by decide
  have hD4 : StatedLieTag.POmegaOdd ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaOdd = .PSL ∧ (3 : ℕ) = 2) := by simp
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
    noThree_odd3 hp2 hq' M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
      cAB cAS
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_linearPair_pOmegaOdd hne
  obtain ⟨-, hnc⟩ := M.muTab_linear_ne_nc hp2 hq hD4 hR₁ hR₂ hW
  have hadj := M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 hR₁ hR₂ hW
  exact ⟨_, M.map_mem hR₁, M.muTab_dComp_ne hΩ hp2 hq hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

theorem split_pOmegaMinus4_plus (M : Ih8Model p f Ω .POmegaMinus 4 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq4 : p ^ f % 4 = 1) :
    ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K := by
  have hG2 : StatedLieTag.POmegaMinus ≠ .G2 := by decide
  have hD4 : StatedLieTag.POmegaMinus ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaMinus = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False := fun A hA B hB S hS' hAB hAS hBS cAB cAS =>
    noThree_minus4 hp2 hq' M.admissible (M.cls_sub hA) (M.cls_sub hB) (M.cls_sub hS') hAB hAS hBS
      cAB cAS
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := M.muTab_linearPair_pOmegaMinus hp2 hne
  obtain ⟨-, hnc⟩ := M.muTab_linear_ne_nc hp2 hq hD4 hR₁ hR₂ hW
  have hadj := M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 hR₁ hR₂ hW
  exact ⟨_, M.map_mem hR₁, M.muTab_dComp_ne hΩ hp2 hq hG2 hD4 hMatch hR₁ hR₂ hnc hadj⟩

end Orth

end MuTab

end CFSG.ClassicalInvolution.Asc77
