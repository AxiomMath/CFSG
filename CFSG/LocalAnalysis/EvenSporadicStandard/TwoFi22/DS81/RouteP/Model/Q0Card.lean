module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.S1
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section


theorem three_thousand_le_card_orbit_L0_x2 : 3510 ≤ Nat.card (MulAction.orbit ↥L0 x2) := by
  have hsub : (MulAction.orbit A1gen x2 : Set Ω) ⊆ (MulAction.orbit ↥L0 x2 : Set Ω) := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    exact ⟨⟨a, A1gen_le_L0 ha⟩, rfl⟩
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← commonNeighbors_x0_x1_eq, ncard_commonNeighbors_x0_x1] at h
  rw [Nat.card_coe_set_eq]
  exact h

theorem card_Q0_le : Nat.card Q0 * 3510 ≤ Nat.card L0 := by
  have h := card_orbit_subgroup_mul_card_inf_stabilizer L0 x2
  have hQ : L0 ⊓ MulAction.stabilizer Q3 x2 = Q0 := rfl
  rw [hQ] at h
  calc Nat.card Q0 * 3510 ≤ Nat.card Q0 * Nat.card (MulAction.orbit ↥L0 x2) :=
        Nat.mul_le_mul_left _ three_thousand_le_card_orbit_L0_x2
    _ = Nat.card L0 := by rw [mul_comm]; exact h

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
