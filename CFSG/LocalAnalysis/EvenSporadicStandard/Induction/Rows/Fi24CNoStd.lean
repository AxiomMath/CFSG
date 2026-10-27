module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24CInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiGiven

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

section Discharge

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem fi24NoStdFi22_proved : Fi24NoStdFi22 := by
  intro H _ _ N L hN hNs hidx hstd hcov
  have hLN : L ≤ N := le_of_isPerfect_of_index_le_two hN.normal hidx hcov.1.1
  obtain ⟨t, ht2, hcomp⟩ := hstd.2
  have hLt : L ≤ centralizer ({t} : Set H) := hcomp.le
  obtain ⟨e'⟩ := hcov.2.2
  have hQc : Nat.card (↥L ⧸ center ↥L) = 64561751654400 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Fi22.card_Fi22
  have hLcard : Nat.card ↥L = 64561751654400 * Nat.card (center ↥L) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
    rw [hQc] at this
    exact this
  by_cases htN : t ∈ N
  · have hu2 : orderOf (⟨t, htN⟩ : ↥N) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
    have hP : ⁅L.subgroupOf N, L.subgroupOf N⁆ = L.subgroupOf N :=
      commutator_subgroupOf_eq_self hLN hcov.1
    have hPu : ∀ k ∈ L.subgroupOf N, k * (⟨t, htN⟩ : ↥N) = ⟨t, htN⟩ * k := fun k hk =>
      Subtype.ext (mem_centralizer_singleton_iff.1 (hLt (Subgroup.mem_subgroupOf.1 hk)))
    have hcardP : Nat.card (L.subgroupOf N) = Nat.card ↥L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv
    have hZpos : 0 < Nat.card (center ↥L) := Nat.card_pos
    have h2 := fi24_card_perfect_le_centralizer hNs hu2 hPu hP
      (by rw [hcardP, hLcard]; exact Nat.le_mul_of_pos_right _ hZpos)
    rw [hcardP, hLcard] at h2
    have hZ2 : Nat.card (center ↥L) = 2 := by omega
    obtain ⟨k, hk⟩ := hcov.odd_center
    omega
  · have := hN.normal
    have hL' : CFSG.Assembly.IsComponentOf L (centralizer ({t} : Set H)) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hcomp.1).2
        hcomp.2
    obtain ⟨B, hB, ⟨eB⟩⟩ :=
      CFSG.ComponentClassification.RestrictedStd.Spor.exists_isComponent_fixSub_of_le
        (W := N) (a := t) hLN hL'
    have hα2 := CFSG.ComponentClassification.RestrictedStd.Spor.conjNormal_mul_self (W := N) ht2
    have hαinn : (MulAut.conjNormal t : MulAut ↥N) ∉
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥N := by
      rintro ⟨w, hw⟩
      apply htN
      have h : (w : H)⁻¹ * t ∈ centralizer (N : Set H) := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : H)) hw
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
        calc x * ((w : H)⁻¹ * t) = (w : H)⁻¹ * ((w : H) * x * (w : H)⁻¹) * t := by group
          _ = (w : H)⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
          _ = (w : H)⁻¹ * t * x := by group
      have h2 := hN.centralizer_le h
      have : t = (w : H) * ((w : H)⁻¹ * t) := by group
      rw [this]
      exact N.mul_mem w.2 h2
    have hBc : Nat.card (↥B ⧸ center ↥B) = 64561751654400 := by
      rw [Nat.card_congr (QuotientGroup.congr (center ↥B) (center ↥L) eB
        (Subgroup.map_center_eq eB)).toEquiv]
      exact hQc
    obtain ⟨e⟩ := hNs
    have e'' : ↥N ≃* CFSG.Blueprint.NativeSporadic.Fi24prime := e
    rcases CFSG.Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds ↥N ⟨e''⟩ _ hα2 hαinn
      B hB with h | h <;> omega

end Discharge

end CFSG.EvenSporadicStandard.Induction
