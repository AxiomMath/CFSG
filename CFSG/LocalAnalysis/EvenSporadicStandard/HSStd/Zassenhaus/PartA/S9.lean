module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Twist
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9E4

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section

set_option linter.unusedSectionVars false


theorem e4_numbers {G : Type} [Group G] [Finite G] {u : G} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (e : QuotT u ≃* NativeSporadic.HS) :
    Nat.card ↥(Cen u) = 88704000 ∧ {g : G | g ∈ Cen u ∧ orderOf g = 2}.ncard ≤ 42351 := by
  have hQ : IsSporadic (QuotT u) .HS := ⟨e⟩
  have hQcard : Nat.card (QuotT u) = 44352000 := card_eq_of_isSporadic_hs hQ
  have hw2 : wOf u * wOf u = 1 := Subtype.ext hu2
  have hw1 : wOf u ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hwo : orderOf (wOf u) = 2 := orderOf_eq_two_of_sq hw2 hw1
  constructor
  · have := (zpowers (wOf u)).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_zpowers, hwo] at this
    rw [this]
    change Nat.card (QuotT u) * 2 = 88704000
    rw [hQcard]
  · have hker : ∀ g : ↥(Cen u), mkT u g = 1 → g = 1 ∨ g = wOf u := by
      intro g hg
      have : mkT u g = mkT u 1 := by rw [hg, map_one]
      rcases (mkT_eq_mkT_iff hu2).1 this with h | h
      · left; exact h.symm
      · right
        have : g = (wOf u)⁻¹ := by
          exact eq_inv_of_mul_eq_one_left h.symm
        rw [this, inv_eq_of_mul_eq_one_right hw2]
    have h1 := ncard_involutions_le_of_quotient (mkT u) (wOf u) hker (Set.toFinite _)
    rw [ncard_involutions_hs hQ] at h1
    have himg : {g : G | g ∈ Cen u ∧ orderOf g = 2} =
        (Cen u).subtype '' {c : ↥(Cen u) | orderOf c = 2} := by
      ext g
      constructor
      · rintro ⟨hg, hg2⟩
        exact ⟨⟨g, hg⟩, by
          show orderOf (⟨g, hg⟩ : ↥(Cen u)) = 2
          rw [← Subgroup.orderOf_coe]
          exact hg2, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c.2, by simpa [← Subgroup.orderOf_coe] using hc⟩
    rw [himg, Set.ncard_image_of_injective _ (Cen u).subtype_injective]
    omega

theorem s9_of_quot (hQ : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup
    G) (z : G) (_hb : PAB G L t E W z) (a : PA8 L t E z), a.ub = t * a.u → a.dcase = DCase.e4 →
    Nonempty (QuotT a.u ≃* NativeSporadic.HS)) : StepS9 := by
  intro G _ _ L t E W z hb a
  by_cases hub : a.ub = a.u
  · exact ⟨{ a with ub_eq := hub }⟩
  exfalso
  have hub' : a.ub = t * a.u := a.ub_cases.resolve_left hub
  cases hc : a.dcase
  · exact twisted_d8_false hb a hub' hc
  · obtain ⟨hu2, hu1⟩ := PA8.u_sq_twisted hb a hub'
    obtain ⟨hC, hI⟩ := e4_numbers hu2 hu1 (hQ G L t E W z hb a hub' hc).some
    exact twisted_e4_false hb a hub' hc hC hI

theorem s9 (hHiS : Harris311HiS) : StepS9 :=
  s9_of_quot (fun _ _ _ _ _ _ _ _ hb a hub he4 => e4_quot_hs hHiS hb a hub he4)

end

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
