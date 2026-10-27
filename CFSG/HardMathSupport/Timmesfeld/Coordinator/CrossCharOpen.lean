module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpB
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TitsP3NoElemAbelian
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalFinal
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Family
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousReeF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Vacuous

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration

structure CrossCharOpen : Prop where
  twistedA : CrossCharFamAt .twistedA regimeTwistedAThreeTwo
  D : CrossCharFamAt .D fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
    idx.1 = .D r q ∧ q.card = 2
  twistedD : CrossCharFamAt .twistedD fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
    idx.1 = .twistedD r q ∧ q.card = 2
  E6 : CrossCharFamAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
    3 ≤ degCount CFSG.Blueprint.Chevalley.Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))
  E7 : CrossCharFamAt .E7 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
    3 ≤ degCount CFSG.Blueprint.Chevalley.Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))
  E8 : CrossCharFamAt .E8 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
    3 ≤ degCount CFSG.Blueprint.Chevalley.Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))
  F4 : CrossCharFamAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
    3 ≤ degCount CFSG.Blueprint.Chevalley.Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))
  G2 : CrossCharFamAt .G2 fun idx p => ¬ regimeG2Vac idx p ∧ ¬ regimeG2Field idx p
  twistedE6 : CrossCharFamAt .twistedE6 fun idx p =>
    ¬ regimeExcVac TauCeti.LieTypeIndex.twistedE6 degCountTw idx p
  trialityD4 : CrossCharFamAt .trialityD4 fun idx p => ¬ regimeTrialityD4Vac idx p
  reeF4 : CrossCharFamAt .reeF4 fun idx p => ¬ regimeReeF4Vac idx p

theorem crossCharFamCat_tits_holds :
    CrossCharFamCat .tits :=
  crossCharFamCat_of_at (fun _ p => p ≠ 3) crossCharFamAt_tits
    (CrossCharFamAt.mono (fun _ _ h => not_not.mp h) crossCharFamAt_tits_three_proved)

theorem crossCharFamCat_G2_of_open
    (h : CrossCharFamAt .G2 fun idx p => ¬ regimeG2Vac idx p ∧ ¬ regimeG2Field idx p) :
    CrossCharFamCat .G2 :=
  crossCharFamCat_of_at regimeG2Vac crossCharFamAt_G2_vac fun idx hk p hp hp2 hc hv => by
    by_cases hf : regimeG2Field idx p
    · exact crossCharFamAt_G2_field idx hk p hp hp2 hc hf
    · exact h idx hk p hp hp2 hc ⟨hv, hf⟩

theorem localThreeBalanceCrossChar_of_open
    (h : CrossCharOpen) : LocalThreeBalanceCrossChar :=
  localThreeBalanceCrossChar_of_families fun k => CrossCharFam.of_cat (by
    cases k
    · exact crossCharFamCat_A
    · exact crossCharFamCat_twistedA_of_threeTwo h.twistedA
    · exact crossCharFamCat_B
    · exact crossCharFamCat_C
    · exact crossCharFamCat_of_at regimeDAll5 crossCharFamAt_D_all5
        (crossCharFamAt_not_regimeDAll5_iff.2 h.D)
    · exact crossCharFamCat_of_at regimeTwistedDAll4 crossCharFamAt_twistedD_all4
        (crossCharFamAt_not_regimeTwistedDAll4_iff.2 h.twistedD)
    · exact crossCharFamCat_E6_of_ge_three h.E6
    · exact crossCharFamCat_E7_of_ge_three h.E7
    · exact crossCharFamCat_E8_of_ge_three h.E8
    · exact crossCharFamCat_F4_of_ge_three h.F4
    · exact crossCharFamCat_G2_of_open h.G2
    · exact crossCharFamCat_of_at _ crossCharFamAt_twistedE6_vac h.twistedE6
    · exact crossCharFamCat_of_at _ crossCharFamAt_trialityD4_vac h.trialityD4
    · exact crossCharFamCat_suzuki
    · exact crossCharFamCat_reeG2
    · exact crossCharFamCat_of_at _ crossCharFamAt_reeF4_vac h.reeF4
    · exact crossCharFamCat_tits_holds)

end CFSG.HardMathSupport.Timmesfeld.Coordinator
