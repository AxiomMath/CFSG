module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Local
public import CFSG.YGroups.Y443.Tri.AssemblyLit

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Monster.Existence


@[expose] def MonsterLocal : Prop :=
  ∃ z : ↥(cent tGriess), LocalAt ↥(cent tGriess) ⟨tGriess, self_mem_cent tGriess⟩ z ∧
    LocalR0 ↥(cent tGriess) ⟨tGriess, self_mem_cent tGriess⟩ z

theorem isTwoBCover_cent_tGriess : IsTwoBCover ↥(cent tGriess) := by
  obtain ⟨-, -, hperf, hcen, ⟨e⟩⟩ := CFSG.YGroups.Y443.monster_clauses_MGriess
  refine ⟨hperf, ?_, ⟨e⟩⟩
  have h1 : Nat.card (center ↥(cent tGriess)) =
      Nat.card ((center ↥(cent tGriess)).map (cent tGriess).subtype) :=
    (Subgroup.card_map_of_injective (cent tGriess).subtype_injective).symm
  rw [h1, hcen, Nat.card_zpowers, orderOf_tGriess]

theorem eq_of_mem_center_cent_tGriess {x : ↥(cent tGriess)} (hx : x ∈ center ↥(cent tGriess))
    (hx2 : orderOf x = 2) : x = ⟨tGriess, self_mem_cent tGriess⟩ := by
  have hmem : (x : MGriess) ∈ (center ↥(cent tGriess)).map (cent tGriess).subtype := ⟨x, hx, rfl⟩
  rw [center_cent_tGriess] at hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have hxo : orderOf (x : MGriess) = 2 := by rw [Subgroup.orderOf_coe]; exact hx2
  have hmod : tGriess ^ (k % 2) = tGriess ^ k := by
    simpa [orderOf_tGriess] using zpow_mod_orderOf tGriess k
  have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk2 with h0 | h1
  · rw [h0, zpow_zero] at hmod
    rw [← hk, ← hmod, orderOf_one] at hxo
    omega
  · rw [h1, zpow_one] at hmod
    exact Subtype.ext (hk.symm.trans hmod.symm)

theorem twoBLocal_of_monster (h : MonsterLocal) : TwoBLocalData := by
  intro L _ _ hcov t ht ht2
  obtain ⟨ψ⟩ := hcov.nonempty_mulEquiv isTwoBCover_cent_tGriess
  obtain ⟨z, hz, hz0⟩ := h
  have hψt : ψ t = ⟨tGriess, self_mem_cent tGriess⟩ := by
    apply eq_of_mem_center_cent_tGriess
    · rw [mem_center_iff]
      intro g
      have := mem_center_iff.1 ht (ψ.symm g)
      have h2 := congrArg ψ this
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    · rw [MulEquiv.orderOf_eq]; exact ht2
  refine ⟨ψ.symm z, ?_, ?_⟩
  · have := hz.map ψ.symm
    rwa [← hψt, ψ.symm_apply_apply] at this
  · have := hz0.map ψ.symm
    rwa [← hψt, ψ.symm_apply_apply] at this

end CFSG.EvenSporadicStandard.TwoB
