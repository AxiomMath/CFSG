module

public import CFSG.ClassicalInvolution.Q3.Q3NGInv
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement


section Count

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem tag3_ne_of_commuting_triple (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} {N₁ N₂ N₃ : Subgroup G}
    (h₁ : N₁ ∈ compMembers3 Ω x D i) (h₂ : N₂ ∈ compMembers3 Ω x D i)
    (h₃ : N₃ ∈ compMembers3 Ω x D i) (c₁₂ : Commutes N₁ N₂) (c₁₃ : Commutes N₁ N₃)
    (c₂₃ : Commutes N₂ N₃) {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n 3 1)
    (hk : D.kind i = CompData.model t n) : t ≠ .G2 ∧ t ≠ .trialityD4 := by
  by_contra hcon
  have ht : t = .G2 ∨ t = .trialityD4 := by
    by_cases h : t = .G2
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra h'
      exact hcon ⟨h, h'⟩
  have key : ∀ c : CompData, c = CompData.model t n → ∀ φ : c.G →* locQuot Ω x,
      locImg Ω x N₁ ≤ φ.range → locImg Ω x N₂ ≤ φ.range → locImg Ω x N₃ ≤ φ.range → False := by
    rintro c rfl φ hr₁ hr₂ hr₃
    exact G2D4.false_of_three_commuting_sl2 (p := 3) (by norm_num) ht hadm (Or.inl rfl) φ hr₁
      hr₂ hr₃ (commutes_locImg_of_commutes c₁₂) (commutes_locImg_of_commutes c₁₃)
      (commutes_locImg_of_commutes c₂₃) ((card_locImg3 hΩ hex h₁.1).trans card_sl2_gf3.symm)
      ((card_locImg3 hΩ hex h₂.1).trans card_sl2_gf3.symm)
      ((card_locImg3 hΩ hex h₃.1).trans card_sl2_gf3.symm)
      (card_center_locImg3_dvd_two hΩ hex h₁.1) (card_center_locImg3_dvd_two hΩ hex h₂.1)
  exact key _ hk (D.hom i) h₁.2 h₂.2 h₃.2

end Count

end CFSG.ClassicalInvolution.Q3.Q3W
