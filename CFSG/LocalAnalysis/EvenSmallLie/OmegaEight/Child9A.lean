module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelLevi
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Child
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Final

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child9

open Subgroup Stage1


theorem false_of_shapeA {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) {t : G} (hA : ShapeA t L) : False := by
  obtain ⟨U, Q, P, a, ψ, p, u, hR, -, hF, hAc, hk⟩ := exists_link_minus' hL
  obtain ⟨hS, hU⟩ := setup_of_linkFacts hA hF hR.odd
  exact hS.false_of_setup_minus hG hnab (Chain.l9_of_link_minus hG hnab hS hU hF hAc hk) hU

theorem endgameA9 : Stage0.EndgameA9 := fun _ _ _ _ _ hH _ hA =>
  false_of_shapeA hH.1.simple hH.1.nonab hH.2.2 hA

end CFSG.EvenSmallLie.OmegaEight.Child9
