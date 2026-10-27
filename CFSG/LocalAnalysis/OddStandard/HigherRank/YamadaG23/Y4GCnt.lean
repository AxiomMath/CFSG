module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma relIndex_ne_zero_of_finite (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  haveI : (H.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite
  exact Subgroup.FiniteIndex.index_ne_zero

theorem y4_card_le_relIndex_mul {F C N : Subgroup G} (hC : C ≤ F) (hN : N ≤ F) :
    Nat.card C ≤ N.relIndex F * Nat.card ↥(C ⊓ N) := by
  have hcardC : Nat.card ↥C = N.relIndex C * Nat.card ↥(C ⊓ N) := by
    rw [← Subgroup.relIndex_mul_card N C, inf_comm]
  have hle : N.relIndex C ≤ N.relIndex F :=
    Subgroup.relIndex_le_of_le_right hC (relIndex_ne_zero_of_finite N F)
  calc Nat.card ↥C = N.relIndex C * Nat.card ↥(C ⊓ N) := hcardC
    _ ≤ N.relIndex F * Nat.card ↥(C ⊓ N) := Nat.mul_le_mul_right _ hle

end CFSG.OddStandard.HigherRank.YamadaG23
