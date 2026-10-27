module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainFinal
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLevelTwo
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Link

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G] {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G}

theorem urRows_eq_uRows (ε : Eps) (k : Fin 6) : Stage2.urRows ε k = uRows ε k := by
  fin_cases k <;> cases ε <;> rfl

theorem uData_of_uGens (hu : UGens ε U Q ψ u) : UData ε U Q ψ u :=
  ⟨hu.u_mem, fun k v => by rw [hu.u_act, urRows_eq_uRows], hu.U_le⟩

theorem l9_of_link_minus [Finite G]
    (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hS : Setup .minus t L U Q P a ψ p)
    (hu : UGens .minus U Q ψ u) (_hF : LinkFacts .minus L U Q P a ψ p u) (_hA : AutCent L Q)
    (hk : ∃ k ∈ P, (∀ v, lin ψ k v = toMat 6 6 #[57, 30, 52, 24, 16, 32] *ᵥ v) ∧ k ^ 4 = 1) :
    L9 t Q :=
  l9_of_levelTwoKill hG hnab hS (uData_of_uGens hu)
    (levelTwoKill_minus hG hnab hS (uData_of_uGens hu) hk)

end CFSG.EvenSmallLie.OmegaEight.Chain
