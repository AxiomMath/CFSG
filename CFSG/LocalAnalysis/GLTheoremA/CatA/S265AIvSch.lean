module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
public import CFSG.LieType.Steinberg.CentralExt.GriessFFourTwo
public import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.Blueprint
  CFSG.Blueprint.Chevalley
open CFSG.Open (GLAPPrimeCore)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts (isPGroup_center_of_glaPPrimeCore_eq_bot)

@[expose] def SchurF4Three : Prop :=
  ∀ (J : Type) [Group J], CFSG.Open.IsQuasisimple J → IsPGroup 3 (Subgroup.center J) →
    catalogIs (J ⧸ Subgroup.center J) S9.isF4two → Subgroup.center J = ⊥

theorem center_eq_bot_of_card_hopf_two {J X : Type} [Group J] [Group X] [Finite X]
    (hJq : CFSG.Open.IsQuasisimple J) (hZ : IsPGroup 3 (Subgroup.center J))
    (e : J ⧸ Subgroup.center J ≃* X) (hM : Nat.card (CFSG.Open.griessHopfMultiplier X) = 2) :
    Subgroup.center J = ⊥ := by
  have hCQ : CFSG.IsQuasisimple J :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr hJq
  haveI : Finite J :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hCQ e
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hCQ e
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv,
    hM] at hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
  rw [hn] at hdvd
  apply Subgroup.eq_bot_of_card_eq
  rw [hn]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero]
  · exact absurd ((dvd_pow_self 3 hpos.ne').trans hdvd) (by norm_num)

theorem schurF4_holds :
    SchurF4Three := by
  intro J _ hJq hZ hcat
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatB.I2610.exists_adjointGroup_of_catalogIs_isF4two hcat
  have hZK : Subgroup.center ↥(adjointGroup Tag.F4 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eQ : AdjointQuotient Tag.F4 K ≃* ↥(adjointGroup Tag.F4 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  haveI : Finite (AdjointQuotient Tag.F4 K) := Finite.of_equiv _ eQ.symm.toEquiv
  exact center_eq_bot_of_card_hopf_two hJq hZ (e.trans eQ.symm)
    (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.f4_two_card_griessHopfMultiplier hK).2

theorem center_eq_bot_of_schurF4 (hS : SchurF4Three) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hq : CFSG.Open.IsQuasisimple ↥S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hcat : catalogIs (PSimple 3 S) S9.isF4two) :
    Subgroup.center ↥S = ⊥ ∧ catalogIs ↥S S9.isF4two := by
  let e1 : PQuot 3 S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let e2 : PSimple 3 S ≃* (↥S ⧸ Subgroup.center ↥S) :=
    QuotientGroup.congr (Subgroup.center (PQuot 3 S)) (Subgroup.center ↥S) e1
      (Subgroup.map_center_eq e1)
  have hcat' : catalogIs (↥S ⧸ Subgroup.center ↥S) S9.isF4two := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hcat
    exact ⟨i, hi, ⟨e2.symm.trans f⟩⟩
  have hZ : Subgroup.center ↥S = ⊥ :=
    hS ↥S hq (isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_three hcore) hcat'
  refine ⟨hZ, ?_⟩
  let eS : ↥S ≃* (↥S ⧸ Subgroup.center ↥S) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat'
  exact ⟨i, hi, ⟨eS.trans f⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
