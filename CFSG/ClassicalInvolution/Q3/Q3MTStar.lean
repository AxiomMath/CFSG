module

public import CFSG.ClassicalInvolution.Q3.Q3MTModel4
public import CFSG.ClassicalInvolution.Q3.Q3MTDich

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups


section Star

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem star_commutes_lin3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hdich : StdDich3Lin t k)
    {R S : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) : Commutes R S := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  obtain ⟨eR, eS, s, hsS, hsN, hord, hzcomm⟩ := star_data3 M hΩ hG2 hD4 hR hS hJ
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]; norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hR)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  rcases hdich R hRl S hSl (sl2Inv eR) (sl2Inv eS) (sl2Inv_mem eR) (sl2Inv_mem eS)
    (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hzcomm.symm with h | h | ⟨W, hW⟩
  · exact absurd (by rw [h]) hJ.2.1
  · exact h
  · exact (false_of_linear_star3 hFcard hW hsS hsN hord).elim

theorem star_commutes_triv3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hdich : StdDich3Triv t k)
    {R S : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) : Commutes R S := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  obtain ⟨eR, eS, s, hsS, hsN, hord, hzcomm⟩ := star_data3 M hΩ hG2 hD4 hR hS hJ
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]; norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hR)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  rcases hdich R hRl S hSl (sl2Inv eR) (sl2Inv eS) (sl2Inv_mem eR) (sl2Inv_mem eS)
    (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hzcomm.symm with h | h
  · exact absurd (by rw [h]) hJ.2.1
  · exact h

end Star

end CFSG.ClassicalInvolution.Q3.Q3MT
