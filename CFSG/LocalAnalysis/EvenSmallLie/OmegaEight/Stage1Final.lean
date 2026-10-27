module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ShapeAB
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Link
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Model

variable {G : Type} [Group G]

theorem setup_of_linkFacts {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
    {p u : Fin 6 → G} (hA : ShapeA t L) (hF : LinkFacts ε L U Q P a ψ p u)
    (hodd : InvolutionsInOddPart L) : Setup ε t L U Q P a ψ p ∧ UGens ε U Q ψ u := by
  refine ⟨⟨hA.shapeAB hF.U_le_L hF.U_max hF.Q_le_L hF.P_eq hF.cent_Q ?_,
    hF.radicalData hodd⟩, ⟨hF.u_mem, hF.u_act, hF.U_le⟩⟩
  intro x hx y hy
  obtain ⟨v, rfl⟩ := hF.mem_ψ x hx
  obtain ⟨w, rfl⟩ := hF.mem_ψ y hy
  rw [← hF.ψ_add, ← hF.ψ_add, add_comm]

end CFSG.EvenSmallLie.OmegaEight.Stage1
