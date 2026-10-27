module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainPlus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelQ3
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Child

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child7

open Subgroup Stage1


theorem false_of_shapeA {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G} (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) {t : G} (hA : ShapeA t L) :
    False := by
  obtain ⟨U, Q, P, a, ψ, p, u, hS, hU, hF, hAc, hU6, hNH, hQ₃⟩ :=
    exists_link_plus' hG hnab hZ hL hA
  exact hS.false_of_setup_plus hG hnab (Chain.l9_of_link_plus' hS hU hF hAc hU6 hNH hQ₃) hU

theorem endgameA7 : Stage0.EndgameA7 := fun _ _ _ _ _ hH _ hA =>
  false_of_shapeA hH.1.simple hH.1.nonab hH.2.1 hH.2.2 hA

end CFSG.EvenSmallLie.OmegaEight.Child7
