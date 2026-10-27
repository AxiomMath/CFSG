module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InPinned

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic CFSG.Sporadic.Fi24 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (fi24_isConj_cases)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] Subgroup.mul


theorem fi24in_base {Y : Type} [Group Y] [Finite Y] (hY : IsSporadic Y .Fi24Prime) {uY : Y}
    {KY : Subgroup Y} (hu2 : orderOf uY = 2) (hKu : ∀ k ∈ KY, k * uY = uY * k)
    (hKp : ⁅KY, KY⁆ = KY) (hcard : 2 * 64561751654400 ≤ Nat.card KY) :
    Fi24InBase Y uY KY := by
  obtain ⟨e⟩ := hY
  let e1 : Y ≃* ↥J := e.trans fi24EquivJ
  have hs2 : e1 uY * e1 uY = 1 := by
    rw [← map_mul, mul_self_eq_one_of_orderOf_eq_two hu2, map_one]
  have hs1 : e1 uY ≠ 1 := fun h => by
    have := (map_eq_one_iff e1 e1.injective).1 h
    rw [this, orderOf_one] at hu2
    omega
  rcases fi24_isConj_cases CFSG.Fischer.polarFacts hs2 hs1 with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    let φ : ↥J ≃* ↥(JR : Subgroup R) := (Subgroup.subgroupOfEquivOfLe J_le_R).symm
    obtain ⟨c', hc'⟩ : ∃ c' : ↥J, e1 uY = c' * tJ * c'⁻¹ := ⟨c⁻¹, by rw [← hc]; group⟩
    have h3 : φ tJ = (⟨tR * xb, fi24in_tRxb_mem_JR⟩ : ↥(JR : Subgroup R)) := Subtype.ext jR_tJ
    have h2 : (e1.trans φ) uY = φ c' * (⟨tR * xb, fi24in_tRxb_mem_JR⟩ : ↥(JR : Subgroup R)) *
        (φ c')⁻¹ := by
      show φ (e1 uY) = _
      rw [hc', map_mul, map_mul, map_inv, h3]
    refine fi24in_base_of_equiv (e1.trans φ) fi24in_base_pinned (φ c') h2 hKu hKp ?_
    rw [fi24in_card_subgroupOf fi24in_LE_le_JR, card_LE]
    omega
  · exfalso
    have hC := CFSG.Sporadic.FischerOddCore.card_centralizer_of_isConj h
    have hle : KY.map e1.toMonoidHom ≤ centralizer ({e1 uY} : Set ↥J) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [mem_centralizer_singleton_iff]
      show e1 k * e1 uY = e1 uY * e1 k
      rw [← map_mul, ← map_mul, hKu k hk]
    have h3 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective e1.injective] at h3
    have h4 := (CFSG.Sporadic.FischerOddCore.fi24R2_centralizer_structure).1
    have h5 : Nat.card ↥(centralizer ({e1 uY} : Set ↥J)) = 160526499840 := by
      rw [← hC]
      exact h4
    omega

end CFSG.EvenSporadicStandard.Induction
