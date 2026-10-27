module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Central
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Step3b

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L U T0 : Subgroup G} {z : G}

theorem trans_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hS : Setting L z) (hD : LocalData L U T0) :
    ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u :=
  (orbit_dichotomy hS (hD.U_le_T0.trans hD.T0_le_L) hD).resolve_left
    (fun hc => false_of_central hS hD hnonab hc)

theorem card_Csub [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hS : Setting L z) (hD : LocalData L U T0) {p q u0 : G} (hD11 : LocalData11 L U p q u0) :
    Nat.card (Csub U z) = 2 ^ 23 := by
  have htrans := trans_of_simple hnonab hS hD
  rcases Csub_eq_V_or_card hS hD with h | h
  · exact (false_of_Csub_eq_V hS hD htrans hD11 h).elim
  · exact h

end CFSG.EvenSporadicStandard.J4Std
