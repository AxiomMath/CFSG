module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_sylow_map_quot {A : Type} [Group A] [Finite A] (N P : Subgroup A) [N.Normal]
    (hN : Odd (Nat.card N)) (hP : IsSylow2Of P ⊤) :
    P ⊓ N = ⊥ ∧ IsSylow2Of (P.map (QuotientGroup.mk' N)) ⊤ := by
  refine ⟨?_, le_top, hP.2.1.map (QuotientGroup.mk' N), ?_⟩
  ·
    rcases (hP.2.1.to_inf_left (K := N)).card_eq_or_dvd with h | h
    · exact Subgroup.eq_bot_of_card_eq (P ⊓ N) h
    · exact absurd (h.trans (Subgroup.card_dvd_of_le inf_le_right)) hN.not_two_dvd_nat
  ·
    rw [Subgroup.relIndex_top_right]
    intro h
    apply hP.2.2
    rw [Subgroup.relIndex_top_right]
    exact h.trans (Subgroup.index_map_dvd (H := P) (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N))

end CFSG.OddStandard.SmallF3.Omega
