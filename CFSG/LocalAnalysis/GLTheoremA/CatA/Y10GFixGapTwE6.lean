module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRTwE6
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Blueprint
open CFSG.LocalAnalysis.GLTheoremA


theorem twE6_model_simple {G : Type} [Group G] {p f : ℕ}
    (h : ChevalleyExceptionalModel G .twistedE6 p f) :
    IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨hnt, hs⟩ := CFSG.LieType.Simplicity.fam_2e6_simplicity G p f h
  haveI := hnt
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = (p ^ f) ^ 2 := hK
  have hθ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, CFSG.LieType.Simplicity.pow_pow_card_sq hK2]
  have h4 : 4 ≤ Nat.card K := by
    rw [hK2]
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    nlinarith
  exact ⟨hs, exists_mul_ne_of_equiv_centerQuot
    (CFSG.LieType.Simplicity.isQuasisimple_derived_twistedFixedGroup σ hθ h4).1 e⟩

theorem fixGapTwE6_holds : FixGapTwE6 := by
  intro n p K _ _ hn hK hp hp2 f hf hord
  obtain ⟨hpn, D, hD, k₀, _, _, hk₀, ⟨e⟩⟩ := FR.subBody_twE6 hn hK hp hp2 ∅ f hf hord
  have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hchev₀ : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) k₀ LargeEvenRhoE6 (n / p)))
      .twistedE6 2 (n / p) :=
    ⟨⟨Nat.prime_two, hm, rfl⟩, twistedChevalleyModel_largeEven .E6 hk₀⟩
  obtain ⟨hs₀, hna₀⟩ := twE6_model_simple hchev₀
  refine ⟨hpn, _, inferInstance, ⟨.twE6, 0, n / p⟩, hs₀, hna₀, ?_, rfl, ?_,
    nonempty_ggFixDer_equiv hD hna₀ e⟩
  · unfold LargeEvenInLambda2
    exact ⟨hm, rfl⟩
  · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    exact ⟨k₀, inferInstance, inferInstance, hk₀, ⟨MulEquiv.refl _⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
