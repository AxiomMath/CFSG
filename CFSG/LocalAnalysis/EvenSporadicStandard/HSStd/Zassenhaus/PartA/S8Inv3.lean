module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv2

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Inv3

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem inv_KD (k : ↥(Cen a.ub)) (hf : ∀ y ∈ K, (k⁻¹ * (tG hb a.toPA6.toPA5 * k *
      (tG hb a.toPA6.toPA5)⁻¹)) * y = y * (k⁻¹ * (tG hb a.toPA6.toPA5 * k *
      (tG hb a.toPA6.toPA5)⁻¹))) :
    k⁻¹ * (tG hb a.toPA6.toPA5 * k * (tG hb a.toPA6.toPA5)⁻¹) = 1 ∨
      (k⁻¹ * (tG hb a.toPA6.toPA5 * k * (tG hb a.toPA6.toPA5)⁻¹) = ubG a.toPA6.toPA5 ∧
        a.dcase = DCase.d8) := by
  set T := tG hb a.toPA6.toPA5 with hT
  set f := k⁻¹ * (T * k * T⁻¹) with hfdef
  have hfF0 : (f : G) ∈ a.F₀ := inv_cent_F0 hb a hK hcj hall f hf
  have hTT := tG_mul_tG hb a.toPA6.toPA5
  have e : f * T = k⁻¹ * T * k := by rw [hfdef]; group
  have hfT : (f * T) * (f * T) = 1 := by
    rw [e]
    calc k⁻¹ * T * k * (k⁻¹ * T * k) = k⁻¹ * (T * T) * k := by group
      _ = 1 := by rw [hTT]; group
  have hftG : ((f : G) * t) * ((f : G) * t) = 1 := congrArg Subtype.val hfT
  cases hdc : a.dcase
  · rcases F0_elem_cases hb a hdc hfF0 hftG with h | h
    · left; exact Subtype.ext h
    · right; exact ⟨Subtype.ext h, rfl⟩
  · left
    obtain ⟨hF, hnc⟩ := a.F₀_e4 hdc
    rw [hF] at hfF0
    obtain ⟨n, hn⟩ := hfF0
    have hub2 := PA5.ub_sq a.toPA6.toPA5
    have hn' : a.ub ^ n = (f : G) := hn
    rcases zpow_sq_one hub2 n with h | h
    · exact Subtype.ext (by rw [← hn', h]; rfl)
    · exfalso
      apply hnc
      have hfub : f = ubG a.toPA6.toPA5 := Subtype.ext (by rw [← hn', h]; rfl)
      rw [hfub] at e
      have e' := congrArg Subtype.val e
      have htub := PA5.t_ub a.toPA6.toPA5 hb
      refine isConj_iff.2 ⟨((k⁻¹ : ↥(Cen a.ub)) : G), ?_⟩
      have e'' : a.ub * t = ((k : ↥(Cen a.ub)) : G)⁻¹ * t * ((k : ↥(Cen a.ub)) : G) := by
        simpa [ubG, tG, hT] using e'
      simp only [Subgroup.coe_inv, inv_inv]
      rw [← e'', htub]

end Inv3

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
