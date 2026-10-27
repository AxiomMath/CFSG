module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Thm24OneUse
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimpleCore

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem lt_pinnedOrder {s : TauCeti.SporadicName} (hs : s ∈ pinnedNames) :
    95040 < pinnedOrder s := by
  simp only [pinnedNames, Sol78Rows, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [pinnedOrder] <;> norm_num

theorem not_card_dvd_95040_of_cover (inp : Thm24ThreeSimpleInputs) {s : TauCeti.SporadicName}
    (hs : s ∈ pinnedNames) {H : Type} [Group H] [Finite H] {N L : Subgroup H} (hLN : L ≤ N)
    (hq : CFSG.IsQuasisimple ↥L) (hcq : IsSporadic (↥L ⧸ center ↥L) s) :
    ¬ Nat.card ↥N ∣ 95040 := by
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := hq.2.1
  have h1 : Nat.card (↥L ⧸ center ↥L) = pinnedOrder s := inp.card_pinned s hs _ hcq
  have h2 : Nat.card (↥L ⧸ center ↥L) ∣ Nat.card ↥L := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card ↥L ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hLN
  have h4 : Nat.card (↥L ⧸ center ↥L) ≤ Nat.card ↥N := Nat.le_of_dvd Nat.card_pos (h2.trans h3)
  exact not_dvd_95040_of_lt (lt_of_lt_of_le (lt_pinnedOrder hs) (h1 ▸ h4))

end CFSG.EvenSporadicStandard.Induction.Hyp
