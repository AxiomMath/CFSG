module

public import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

variable {G : Type} [Group G] [Finite G]

@[expose] def TwelveSevenA (M H Q : Subgroup G) : Prop :=
  ∃ e : ↥Q ≃* W3, IsMulCommutative (Q ⊓ jSub M H : Subgroup G) ∧
    Nat.card (Q ⊓ jSub M H : Subgroup G) = 27

theorem thompsonSubgroup_eq_inf_of_wreath {M H Q : Subgroup G}
    (e : ↥Q ≃* W3) (hA : IsMulCommutative (Q ⊓ jSub M H : Subgroup G))
    (hcard : Nat.card (Q ⊓ jSub M H : Subgroup G) = 27) :
    CFSG.thompsonSubgroup Q = Q ⊓ jSub M H := by
  have hcomm : ∀ a ∈ Q ⊓ jSub M H, ∀ b ∈ Q ⊓ jSub M H, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [CFSG.thompsonSubgroup_eq_ambientOrderThompson,
    ← CFSG.Open.thompsonSubgroup_eq_ambientOrderThompson, thompsonSubgroup_eq_baseIn e]
  exact (eq_baseIn_of_comm e inf_le_left hcomm (le_of_eq hcard.symm)).symm

theorem thompsonSubgroup_eq_inf_of_twelveSevenA {M H Q : Subgroup G}
    (h : TwelveSevenA M H Q) : thompsonSubgroup Q = Q ⊓ jSub M H := by
  obtain ⟨e, hA, hcard⟩ := h
  exact thompsonSubgroup_eq_inf_of_wreath e hA hcard

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
