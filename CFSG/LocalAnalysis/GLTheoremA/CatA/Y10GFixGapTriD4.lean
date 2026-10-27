module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRTD4
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTri
public import CFSG.LieType.Simplicity.TrialityD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Blueprint
open CFSG.LocalAnalysis.GLTheoremA


theorem triD4_model_simple {G : Type} [Group G] {p f : ℕ}
    (h : ChevalleyExceptionalModel G .trialityD4 p f) :
    IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨hnt, hs⟩ := CFSG.LieType.Simplicity.fam_3d4_simplicity G p f h
  haveI := hnt
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  exact ⟨hs, exists_mul_ne_of_equiv_centerQuot
    (CFSG.LieType.Steinberg.TwistedD4.isQuasisimple_derived_twistedFixedGroup_D4 σ hq hK3 hσ).1 e⟩

theorem fixGapTriD4_holds : FixGapTriD4 := by
  intro n p K _ _ hn hK hp hp2 hp3 f hf hord
  have hchev : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      .trialityD4 2 n :=
    ⟨⟨Nat.prime_two, hn, rfl⟩, twistedChevalleyModel_largeEven .D4 hK⟩
  obtain ⟨hs, hna⟩ := triD4_model_simple hchev
  have hF := innFree_of_ggRawInnField (RawAutTri.ggRawInnField_triD4 hn K hK hp.one_lt.ne') hs hna
  obtain ⟨hpn, D, hD, k₀, _, _, hk₀, ⟨e⟩⟩ :=
    FR.subBody_td4 hn hK hp hp2 hp3 (LargeEvenChevIDImage LargeEvenCartanD4 K _) _ hF f hf hord
  have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hchev₀ : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 k₀ LargeEvenRhoD4 (n / p)))
      .trialityD4 2 (n / p) :=
    ⟨⟨Nat.prime_two, hm, rfl⟩, twistedChevalleyModel_largeEven .D4 hk₀⟩
  obtain ⟨hs₀, hna₀⟩ := triD4_model_simple hchev₀
  refine ⟨hpn, _, inferInstance, ⟨.triD4, 0, n / p⟩, hs₀, hna₀, ?_, rfl, ?_,
    nonempty_ggFixDer_equiv hD hna₀ e⟩
  · unfold LargeEvenInLambda2
    exact ⟨hm, rfl⟩
  · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    exact ⟨k₀, inferInstance, inferInstance, hk₀, ⟨MulEquiv.refl _⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
