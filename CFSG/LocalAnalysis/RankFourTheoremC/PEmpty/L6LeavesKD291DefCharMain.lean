module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharClass
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Defs
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open TauCeti CFSG.Assembly.LowTwoRank

@[expose] def InExc (t : StatedLieTag) : Prop :=
  ∀ (p f : ℕ), p.Prime → 5 ≤ p → 1 ≤ f → ∀ (G : Type) [Group G] [Finite G],
    CFSG.Blueprint.ChevalleyExceptionalModel G t p f → RankThreeCent p G

@[expose] def InG2Two : Prop :=
  ∀ (p f : ℕ), p.Prime → 5 ≤ p → 2 ≤ f → ∀ (G : Type) [Group G] [Finite G],
    CFSG.Blueprint.ChevalleyExceptionalModel G .G2 p f →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) → RankThreeCent p G

@[expose] def InG2Prime : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (G : Type) [Group G] [Finite G],
    CFSG.Blueprint.ChevalleyExceptionalModel G .G2 p 1 → CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3

structure DefCharInputs : Prop where
  uni : InUni
  omegaOdd : InOmegaOdd
  omegaPlus : InOmegaPlus
  omegaMinus : InOmegaMinus
  f4 : InExc .F4
  e6 : InExc .E6
  e7 : InExc .E7
  e8 : InExc .E8
  twistedE6 : InExc .twistedE6
  trialityD4 : InExc .trialityD4
  g2Two : InG2Two
  g2Prime : InG2Prime

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open Subgroup CFSG.Open TauCeti CFSG.Assembly.LowTwoRank KD291DC

theorem kd291DefCharL_of_inputs
    (hI : DefCharInputs) : KD291DefCharL := by
  intro p hp hp5 L _ _ _ _ ⟨dv, hch, ⟨e⟩⟩ h3 y hyo hyc
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, hv⟩ := dv
  have hch' : d.characteristic = p := hch
  cases d with
  | A r q => exact (kd291DC_A hp5 r q hv (by simpa using hch') e h3 hyo hyc).elim
  | twistedA r q =>
    exact (kd291DC_twistedA hp5 hI.uni r q hv (by simpa using hch') e h3 hyo hyc).elim
  | B r q => exact kd291DC_B hp5 hI.omegaOdd r q hv (by simpa using hch') e h3 hyo hyc
  | C r q => exact (kd291DC_C hp5 r q hv (by simpa using hch') e hyo hyc).elim
  | D r q => exact (kd291DC_D hp5 hI.omegaPlus r q hv (by simpa using hch') e hyo hyc).elim
  | twistedD r q =>
    exact (kd291DC_twistedD hp5 hI.omegaMinus r q hv (by simpa using hch') e hyo hyc).elim
  | E6 q =>
    have hqp : q.p = p := by simpa using hch'
    have hq2 : q.p ≠ 2 := by omega
    subst hqp
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .E6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hq2 e⟩
    exact (false_of_rankThreeCent (hI.e6 q.p q.exponent q.prime_p hp5 q.exponent_pos L hm) hyo
      hyc).elim
  | E7 q =>
    have hqp : q.p = p := by simpa using hch'
    have hq2 : q.p ≠ 2 := by omega
    subst hqp
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .E7 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hq2 e⟩
    exact (false_of_rankThreeCent (hI.e7 q.p q.exponent q.prime_p hp5 q.exponent_pos L hm) hyo
      hyc).elim
  | E8 q =>
    have hqp : q.p = p := by simpa using hch'
    have hq2 : q.p ≠ 2 := by omega
    subst hqp
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .E8 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hq2 e⟩
    exact (false_of_rankThreeCent (hI.e8 q.p q.exponent q.prime_p hp5 q.exponent_pos L hm) hyo
      hyc).elim
  | F4 q =>
    have hqp : q.p = p := by simpa using hch'
    have hq2 : q.p ≠ 2 := by omega
    subst hqp
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .F4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hq2 e⟩
    exact (false_of_rankThreeCent (hI.f4 q.p q.exponent q.prime_p hp5 q.exponent_pos L hm) hyo
      hyc).elim
  | G2 q =>
    have hqp : q.p = p := by simpa using hch'
    have hq2 : q.p ≠ 2 := by omega
    subst hqp
    have h3q : 3 ≤ q.p ^ q.exponent := by
      have h := ((LieTypeIndex.valid_iff _).1 hv).1
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .G2 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl, h3q⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hq2 e⟩
    by_cases hf : q.exponent = 1
    · rw [hf] at hm
      exact ⟨le_antisymm (hI.g2Prime q.p q.prime_p hp5 L hm) h3, Or.inr hm⟩
    · exact (false_of_rankThreeCent (hI.g2Two q.p q.exponent q.prime_p hp5
        (by have := q.exponent_pos; omega) L hm h3) hyo hyc).elim
  | twistedE6 q =>
    have hqp : q.p = p := by simpa using hch'
    have hq2 : q.p ≠ 2 := by omega
    subst hqp
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .twistedE6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv hq2 (by decide) e⟩
    exact (false_of_rankThreeCent (hI.twistedE6 q.p q.exponent q.prime_p hp5 q.exponent_pos L hm)
      hyo hyc).elim
  | trialityD4 q =>
    have hqp : q.p = p := by simpa using hch'
    have hq2 : q.p ≠ 2 := by omega
    subst hqp
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel L .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hq2 (by decide) e⟩
    exact (false_of_rankThreeCent (hI.trialityD4 q.p q.exponent q.prime_p hp5 q.exponent_pos L hm)
      hyo hyc).elim
  | suzuki m => simp at hch'; omega
  | reeG2 m => simp at hch'; omega
  | reeF4 m => simp at hch'; omega
  | tits => simp at hch'; omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
