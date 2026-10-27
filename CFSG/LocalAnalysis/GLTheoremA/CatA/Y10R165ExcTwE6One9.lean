module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.SeitzReduction CFSG.StandardType
  CFSG.LieType.Steinberg.Exceptional CFSG.SectionRank CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Minuscule
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One

theorem center_fixedGroup_eq_bot_of_not_three_dvd {k : Type} [Field k] [Finite k] {f : ℕ}
    (θ : k →+* k) (hk : Nat.card k = (2 ^ f) ^ 2) (hθ : ∀ c, θ c = c ^ (2 ^ f))
    (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    Subgroup.center ↥(fixedGroup k θ) = ⊥ := by
  letI : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  have hcard : Nat.card ↥(Subgroup.center ↥(fixedGroup k θ)) = 1 := by
    rw [card_center_fixedGroup_pow_two θ hk hθ]
    have hc : Nat.Coprime 3 (2 ^ f + 1) := Nat.prime_three.coprime_iff_not_dvd.2 h3
    simpa using hc.gcd_eq_one
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  haveI : Fintype ↥(Subgroup.center ↥(fixedGroup k θ)) := Fintype.ofFinite _
  haveI : Subsingleton ↥(Subgroup.center ↥(fixedGroup k θ)) :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      rw [← Nat.card_eq_fintype_card, hcard])
  have h := Subsingleton.elim (⟨x, hx⟩ : ↥(Subgroup.center ↥(fixedGroup k θ)))
    ⟨1, Subgroup.one_mem _⟩
  exact Subtype.ext_iff.mp h

theorem ker_twistedIsogenyC_eq_bot_of_not_three_dvd {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2)
    (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    (twistedIsogenyC hf hk (frobQ 2 f) (fun c => frobQ_apply 2 f c)).ker = ⊥ := by
  rw [ker_twistedIsogenyC hf hk (frobQ 2 f) (fun c => frobQ_apply 2 f c)]
  exact center_fixedGroup_eq_bot_of_not_three_dvd (frobQ 2 f) hk
    (fun c => frobQ_apply 2 f c) h3

noncomputable def twistedIsogenyCMulEquiv {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2)
    (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    ↥(fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
  MulEquiv.ofBijective (twistedIsogenyC hf hk (frobQ 2 f) (fun c => frobQ_apply 2 f c))
    ⟨(MonoidHom.ker_eq_bot_iff _).1
        (ker_twistedIsogenyC_eq_bot_of_not_three_dvd hf hk h3),
      twistedIsogenyC_surjective hf hk (frobQ 2 f) (fun c => frobQ_apply 2 f c)⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
