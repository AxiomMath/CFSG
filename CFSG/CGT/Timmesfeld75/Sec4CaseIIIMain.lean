module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIEightPlus
public import CFSG.CGT.Timmesfeld75.Sec4NoAAssembly

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

@[expose] def Sec4CaseIIIEight : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    Nat.card T = 2 * Nat.card (normIn T T₁) → Nat.card T = 8 →
      ∀ a ∈ normD T, a ∉ T ⊔ normIn T₁ T → ¬ ∀ l ∈ normIn T₁ T, ⁅a, l⁆ ∈ T

theorem sec4CaseIII_of_inputs (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hSz : Section3SzInput) (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) (hEight : Sec4CaseIIIEight) : Sec4CaseIII := by
  intro G _ T T₁ hy hS hSI hq a ha haL hcomm
  have hfin : Finite G := hy.finite
  have hsimple : IsSimpleGroup G := hy.simple
  obtain ⟨g, t, htT, ht1, hg⟩ := ha.1
  have h : Sec4Hyp T T₁ a (conjSubgroup g⁻¹ T) :=
    ⟨hy.pair, hS, hSI, ha, haL, hcomm, ⟨g⁻¹, rfl⟩, mem_conjSubgroup.mpr (by
      rw [inv_inv, hg]
      have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      rw [e]
      exact htT)⟩
  have hLP : IsPGroup 2 (normIn T T₁) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_of_le hy.pair.wc.1 (normIn_le T T₁))
  obtain ⟨m, hm⟩ := hLP.exists_card_eq
  have h4 : 4 ≤ Nat.card T := hy.card
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · interval_cases m
    · rw [pow_zero] at hm
      omega
    · exact h.false_of_card_four hq (by rw [hq, hm]; norm_num)
    · exact hEight G T T₁ hy hS hSI hq (by rw [hq, hm]; norm_num) a ha haL hcomm
  · refine h.false_of_card_ge_eight h214 hInv hSz hTO hBW hy.nonab hq ?_
    rw [hm]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3

end CFSG.CGT.Timmesfeld75
