module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.KStructure

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG CFSG.EvenSporadicStandard.TwoFi22

variable {G : Type} [Group G]

theorem isTwoConstrained_of_isCharacteristicP (H : Subgroup G) (h : IsCharacteristicP 2 ↥H) :
    IsTwoConstrained H := by
  intro x hx
  obtain ⟨hxH, hxC⟩ := mem_inf.1 hx
  have hmem : (⟨x, hxH⟩ : ↥H) ∈ centralizer ((pCore 2 ↥H : Subgroup ↥H) : Set ↥H) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hyG : (y : G) ∈ O2In H := ⟨y, hy, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.1 hxC _ hyG)
  exact ⟨⟨x, hxH⟩, h hmem, rfl⟩

theorem isCharacteristicP_of_isTwoConstrained (H : Subgroup G) (h : IsTwoConstrained H) :
    IsCharacteristicP 2 ↥H := by
  intro x hx
  rw [mem_pCore_iff_mem_O2In]
  refine h ⟨x.2, ?_⟩
  show (x : G) ∈ centralizer ((O2In H : Subgroup G) : Set G)
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact congrArg Subtype.val ((mem_centralizer_iff.1 hx) y hy)

theorem standardComponentOddCore_eq_pPrimeCore (H : Type*) [Group H] :
    CFSG.Open.standardComponentOddCore H = pPrimeCore 2 H := by
  unfold CFSG.Open.standardComponentOddCore pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem isTwoConstrained_iff_layer_eq_bot [Finite G] (H : Subgroup G)
    (hodd : CFSG.Open.standardComponentOddCore ↥H = ⊥) :
    IsTwoConstrained H ↔ layer ↥H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h => layer_eq_bot_of_isCharacteristicP _ 2
      (isCharacteristicP_of_isTwoConstrained H h),
    fun h => isTwoConstrained_of_isCharacteristicP H ?_⟩
  exact isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2
    (by rw [← standardComponentOddCore_eq_pPrimeCore]; exact hodd) h

end CFSG.EvenSporadicStandard.TwoB
