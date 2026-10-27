module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.ConjIota

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem eq_one_or_eq_gammaConj_of_centralizes [IsSimpleGroup G] (hF : IsF5Type a z)
    (hL : F5Local G a z) (hlines : LinesThrough a z) (hperp : PerpThreeA a)
    (σ : Gamma a ≃g Gamma a) (hc : ∀ g ∈ Gx a, σ * gammaConj a g = gammaConj a g * σ) :
    σ = 1 ∨ σ = gammaConj a a := by
  have hinj := gammaConj_injective hF hL
  have h2 : ∀ b ∈ orb2A a a, act σ b = b := by
    intro b hb
    have hbG : b ∈ Gx a := mem_Gx.2 (comm_of_adj hF (IsConj.refl a) hb.1 hb.2)
    have h1 : σ * gammaConj a b * σ⁻¹ = gammaConj a b := by
      rw [hc b hbG]
      group
    rw [conj_gammaConj hF hL hlines hperp σ hb.1] at h1
    exact hinj h1
  by_cases hfix : ∃ y ∈ orb3A a a, act σ y = y
  · left
    obtain ⟨y, hy, hσy⟩ := hfix
    refine eq_one_of_fix_two_three hF hL hlines σ h2 fun x hx => ?_
    obtain ⟨g, hg, hgx⟩ := (isConjOrbit_orb3A hL).transitive y hy x hx
    have hx' : act (gammaConj a g) y = x := by rw [act_gammaConj g hy.1, hgx]
    calc act σ x = act σ (act (gammaConj a g) y) := by rw [hx']
      _ = act (σ * gammaConj a g) y := (act_mul _ _ hy.1).symm
      _ = act (gammaConj a g * σ) y := by rw [hc g hg]
      _ = act (gammaConj a g) (act σ y) := act_mul _ _ hy.1
      _ = x := by rw [hσy, hx']
  · right
    push_neg at hfix
    exact eq_gammaConj_base hF hL hlines hperp σ h2 hfix

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
