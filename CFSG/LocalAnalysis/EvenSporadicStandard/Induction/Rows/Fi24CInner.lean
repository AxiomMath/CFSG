module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic CFSG.Sporadic.Fi24 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (fi24_isConj_cases)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Discharge

attribute [-instance] Subgroup.mul


theorem fi24_card_perfect_le_centralizer {Y : Type} [Group Y] [Finite Y]
    (hY : IsSporadic Y .Fi24Prime) {uY : Y} {P : Subgroup Y} (hu2 : orderOf uY = 2)
    (hPu : ∀ k ∈ P, k * uY = uY * k) (hP : ⁅P, P⁆ = P)
    (hcard : 64561751654400 ≤ Nat.card P) : Nat.card P = 2 * 64561751654400 := by
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
    obtain ⟨f, hf⟩ : ∃ f : Y ≃* ↥J, f = e1.trans (MulAut.conj c) := ⟨_, rfl⟩
    have hfu : f uY = tJ := by
      rw [hf]
      show c * e1 uY * c⁻¹ = tJ
      exact hc
    have hPc : P.map f.toMonoidHom ≤ centralizer ({tJ} : Set ↥J) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show f k * tJ = tJ * f k
      rw [← hfu, ← map_mul, ← map_mul, hPu k hk]
    have hPperf : ⁅P.map f.toMonoidHom, P.map f.toMonoidHom⁆ = P.map f.toMonoidHom := by
      rw [← Subgroup.map_commutator, hP]
    have hle := fi24in_base_J.le_of_perfect_le_centralizer hPperf hPc
    have hcP : Nat.card (P.map f.toMonoidHom) = Nat.card P :=
      Subgroup.card_map_of_injective f.injective
    have hK : ⁅fi24inK, fi24inK⁆ ≤ P.map f.toMonoidHom :=
      fi24in_commutator_le_of_card_le hle (by rw [fi24inK_card, hcP]; omega)
    rw [fi24inK_perfect] at hK
    have h1 := Subgroup.card_le_of_le hK
    have h2 := Subgroup.card_le_of_le hle
    rw [fi24inK_card] at h1 h2
    omega
  · exfalso
    have hC := CFSG.Sporadic.FischerOddCore.card_centralizer_of_isConj h
    have hle : P.map e1.toMonoidHom ≤ centralizer ({e1 uY} : Set ↥J) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show e1 k * e1 uY = e1 uY * e1 k
      rw [← map_mul, ← map_mul, hPu k hk]
    have h3 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective e1.injective] at h3
    have h4 := (CFSG.Sporadic.FischerOddCore.fi24R2_centralizer_structure).1
    have h5 : Nat.card ↥(centralizer ({e1 uY} : Set ↥J)) = 160526499840 := by
      rw [← hC]
      exact h4
    omega

end Discharge

end CFSG.EvenSporadicStandard.Induction
