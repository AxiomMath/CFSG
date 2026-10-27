module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

theorem commutator_sup_eq_bot_of_components {H : Type*} [Group H] [Finite H] {C N M : Subgroup H}
    {e : H} (hNC : N ≤ C) (hMC : M ≤ C) (hN : IsComponent (N.subgroupOf C))
    (hM : IsComponent (M.subgroupOf C)) (hNe : conjugate N e = N) (hMe : conjugate M e ≠ M) :
    ⁅M ⊔ conjugate M e, N⁆ = ⊥ := by
  have hNM : N.subgroupOf C ≠ M.subgroupOf C := by
    intro h1
    have h2 : N = M := by
      rwa [subgroupOf_inj, inf_of_le_left hNC, inf_of_le_left hMC] at h1
    exact hMe (h2 ▸ hNe)
  have h1 := (LocalCores.distinct_components_commute hN hM).resolve_left hNM
  have h2 : ⁅N, M⁆ = ⊥ := by
    have := congrArg (Subgroup.map C.subtype) h1
    rwa [map_commutator, map_subgroupOf_eq_of_le hNC, map_subgroupOf_eq_of_le hMC,
      Subgroup.map_bot] at this
  have h3 : ⁅M, N⁆ = ⊥ := by rw [commutator_comm]; exact h2
  have h4 : ⁅conjugate M e, N⁆ = ⊥ := by
    rw [← hNe, conjugate, conjugate, ← map_commutator, h3, Subgroup.map_bot]
  rw [commutator_eq_bot_iff_le_centralizer] at h3 h4 ⊢
  exact sup_le h3 h4

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

end Seven

end CFSG.ComponentClassification.GSThmB
