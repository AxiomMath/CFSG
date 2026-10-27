module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv7a

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Comm3

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem inv_comm_decomp (k l : ↥(Cen a.ub))
    (hk : k ∈ CT hb a.toPA6.toPA5 ∨ ∃ hd : a.dcase = DCase.d8, u1G a hd * k ∈ CT hb a.toPA6.toPA5)
    (hl : l ∈ CT hb a.toPA6.toPA5 ∨ ∃ hd : a.dcase = DCase.d8, u1G a hd * l ∈ CT hb a.toPA6.toPA5) :
    ∃ j : ↥(Cen a.ub), (j : G) ∈ derivedIn a.Abar ∧ ∃ z ∈ zpowers (ubG a.toPA6.toPA5),
      ⁅k, l⁆ = j * z := by
  have hZn : (zpowers (ubG a.toPA6.toPA5)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨i, rfl⟩ := hn
    have : g * (ubG a.toPA6.toPA5) ^ i * g⁻¹ = (ubG a.toPA6.toPA5) ^ i := by
      have h := (Commute.zpow_left (show Commute (ubG a.toPA6.toPA5) g from
        ubG_central a.toPA6.toPA5 g) i).eq
      calc g * (ubG a.toPA6.toPA5) ^ i * g⁻¹ = ((ubG a.toPA6.toPA5) ^ i * g) * g⁻¹ := by rw [← h]
        _ = (ubG a.toPA6.toPA5) ^ i := by group
    rw [this]; exact mem_zpowers_iff.2 ⟨i, rfl⟩
  by_cases hd : a.dcase = DCase.d8
  · have hrep : ∀ x : ↥(Cen a.ub), (x ∈ CT hb a.toPA6.toPA5 ∨ ∃ hd' : a.dcase = DCase.d8,
        u1G a hd' * x ∈ CT hb a.toPA6.toPA5) →
        ∃ ε : ℕ, ∃ c ∈ CT hb a.toPA6.toPA5, x = (u1G a hd) ^ ε * c := by
      intro x hx
      rcases hx with h | ⟨hd', h⟩
      · exact ⟨0, x, h, by simp⟩
      · refine ⟨1, u1G a hd * x, h, ?_⟩
        have hsq : u1G a hd * u1G a hd = 1 := Subtype.ext (u1_sq a hd)
        rw [pow_one, ← mul_assoc, hsq, one_mul]
    obtain ⟨ε, c, hc, hkc⟩ := hrep k hk
    obtain ⟨ε', c', hc', hlc⟩ := hrep l hl
    have hu : ∀ c ∈ (CT hb a.toPA6.toPA5 : Set ↥(Cen a.ub)),
        u1G a hd * c * (u1G a hd)⁻¹ * c⁻¹ ∈ zpowers (ubG a.toPA6.toPA5) := by
      intro c hc
      have h1 : (c : G) * t = t * c := congrArg Subtype.val ((mem_CT hb a.toPA6.toPA5).1 hc)
      have h2 : (c : G) * a.ub = a.ub * c := mem_Cen.1 c.2
      rcases PA7.u1_comm_c hb a hd h1 h2 with h | h
      · have : u1G a hd * c * (u1G a hd)⁻¹ * c⁻¹ = 1 :=
          Subtype.ext (by simpa [u1G, Subgroup.coe_mul, Subgroup.coe_inv] using h)
        rw [this]; exact one_mem _
      · have : u1G a hd * c * (u1G a hd)⁻¹ * c⁻¹ = ubG a.toPA6.toPA5 :=
          Subtype.ext (by simpa [u1G, ubG, Subgroup.coe_mul, Subgroup.coe_inv] using h)
        rw [this]; exact mem_zpowers _
    have hmem := comm_mod_central (zpowers (ubG a.toPA6.toPA5)) (u1G a hd)
      (CT hb a.toPA6.toPA5 : Set ↥(Cen a.ub)) hu hkc hlc hc hc'
    exact ⟨⁅c, c'⁆, CT_comm_mem_J hb a.toPA6.toPA5 hc hc', ⁅c, c'⁆⁻¹ * ⁅k, l⁆, hmem, by group⟩
  · have hk' : k ∈ CT hb a.toPA6.toPA5 := hk.resolve_right fun ⟨hd', _⟩ => hd hd'
    have hl' : l ∈ CT hb a.toPA6.toPA5 := hl.resolve_right fun ⟨hd', _⟩ => hd hd'
    exact ⟨⁅k, l⁆, CT_comm_mem_J hb a.toPA6.toPA5 hk' hl', 1, one_mem _, by simp⟩

end Comm3

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
