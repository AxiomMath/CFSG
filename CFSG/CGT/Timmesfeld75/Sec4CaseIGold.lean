module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIPlus
public import CFSG.CGT.Timmesfeld75.Sec4CaseIOdd

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

@[expose] def Sec4I5Goldschmidt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SimpleCaseUpTo (Nat.card G) →
    ∀ (T T₁ T₂ : Subgroup G) (a : G), Sec4Hyp T T₁ a T₂ →
    2 * Nat.card (normIn T T₁) < Nat.card T → Nat.card T ≠ 16 →
      Sec4FourHolds T T₁ T₂ → Sec4PlusHolds T T₁ T₂ →
        ∀ g ∈ Subgroup.normalizer (T : Set G), conjSubgroup g (normIn T T₁) = normIn T T₁

theorem sec4CaseI_of_inputs
    (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hAsc : AschbacherNoPolarInput) (hA : Sec4I4TrivialAction) (hC : Sec4I4OuterAction)
    (hC' : Sec4I5OuterAction) (hG : Sec4I5Goldschmidt) : Sec4CaseI := by
  intro G _ T T₁ hy hS hSI hq h16 a ha haL hcomm
  have hfin : Finite G := hy.finite
  have hsimple : IsSimpleGroup G := hy.simple
  obtain ⟨g, t, htT, ht1, hg⟩ := ha.1
  have h : Sec4Hyp T T₁ a (conjSubgroup g⁻¹ T) :=
    ⟨hy.pair, hS, hSI, ha, haL, hcomm, ⟨g⁻¹, rfl⟩, mem_conjSubgroup.mpr (by
      rw [inv_inv, hg]
      have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      rw [e]
      exact htT)⟩
  have hAn := hG G hy.nonab hy.ind T T₁ _ a h hq h16
    (h.sec4FourHolds hy.nonab hy.ind hAsc hA hC hq h16)
    (h.sec4PlusHolds hy.nonab hy.ind hAsc hA hC hC' hq h16)
  exact false_of_normal_of_maxPair hTO hBW h214 hInv hy.nonab h.pair h.sec3 hAn

end CFSG.CGT.Timmesfeld75
