module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeHyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDataCore

public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] {L : Subgroup X}

theorem center_eq_bot_of_simple (hs : IsSimpleGroup ↥L) (M : SDModel ↥L) : center ↥L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h : (MulAut.conj : ↥L →* MulAut ↥L) x = (MulAut.conj : ↥L →* MulAut ↥L) 1 := by
    rw [map_one]
    ext u
    have := mem_center_iff.mp hx u
    simp [MulAut.conj_apply, mul_assoc, ← this]
  exact mem_bot.mpr (M.conj_injective h)

theorem pPrimeCore_eq_bot_of_simple (hs : IsSimpleGroup ↥L) (M : SDModel ↥L) :
    pPrimeCore 2 ↥L = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [M.card_L]; norm_num)
  rcases (pPrimeCore_normal (p := 2) (G := ↥L)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥L)) := pPrimeCore_coprime_card
    rw [h, card_top, M.card_L] at hcop
    norm_num at hcop

theorem sdConfig_of_hyp {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (h : FritzHyp G t L) (M : SDModel ↥L) : SDConfig t L :=
  { orderOf_eq := h.orderOf_t
    le_centralizer := h.le_centralizer
    le_normalizer := h.le_normalizer
    pPrimeCore_eq_bot := pPrimeCore_eq_bot_of_simple h.isSimple M
    center_eq_bot := center_eq_bot_of_simple h.isSimple M
    isCyclic := h.isCyclic_C }

end CFSG.OddStandard.SmallF3.L33.KD
