module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenCommon
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakRes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Model
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Push
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LieType.Multipliers.U43
public import Certificates.Certificate9705

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open TauCeti CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.SectionRank
  CFSG.LieType.Multipliers.U43 CFSG.AGLEmbedding.R3

theorem coverPointDatum_X₀ :
    CoverPointDatum X₀ 3 :=
  coverPointDatum_of_surjective (p := 3) U43Seed.toX₀ U43Seed.toX₀_surjective
    (fun k hk hk3 => U43Seed.eq_one_of_toX₀_eq_one k hk hk3)
    (coverPointDatum_of_mulEquiv U43Seed.seedEquiv
      (coverPointDatum_of_check (spec3 8) (D := U43Three.cpSpec) (by show Nat.Prime 3; norm_num)
        Certificates.certificate9705.1 Certificates.certificate9705.2))

theorem weakGenU43 :
    WeakGenU43 := by
  intro q hv hq
  have hdvd : q.p ∣ 3 := by
    rw [← hq, PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  have hq1 : q.exponent = 1 := by
    have h : 3 ^ q.exponent = 3 ^ 1 := by
      rw [← hp3, ← PrimePower.card_def, hq, hp3, pow_one]
    exact Nat.pow_right_injective (by norm_num) h
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
    (G := (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (MulEquiv.refl _)
  rw [hp3, hq1] at hmod
  obtain ⟨e⟩ := nonempty_mulEquiv_X₀
    (X := (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (Or.inl ⟨by decide, hmod⟩)
  have : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  exact coverWeakGen_of_mulEquiv e.symm
    (coverWeakGen_of_coverPointDatum (by norm_num) coverPointDatum_X₀)

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
