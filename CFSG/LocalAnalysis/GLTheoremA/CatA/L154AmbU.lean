module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Amb
public import CFSG.Milestones.ASVolI.A3L3.U3Facts
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU3Char3Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate14953
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem l154AmbU33_twistedA {d : TauCeti.LieTypeIndex} (hv : d.Valid)
    (h : l154AmbU33 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    ∃ q : TauCeti.PrimePower, d = .twistedA 2 q ∧ q.card = 3 := by
  revert h
  cases d
  case twistedA r q =>
    match r, q with
    | 2, q => exact fun h => ⟨q, rfl, h⟩
    | 0, q => exact fun h => False.elim h
    | 1, q => exact fun h => False.elim h
    | r + 3, q => exact fun h => False.elim h
  all_goals exact fun h => False.elim h

theorem l154_oddInner_unitaryPSU_three {K : Type} [Field K] (hU : UnitaryFieldData 3 1 K) :
    ∀ φ : MulAut (unitaryPSU hU 3), Odd (orderOf φ) → ∃ g : unitaryPSU hU 3, φ = MulAut.conj g := by
  intro φ hφ
  haveI : Finite K := hU.finite
  haveI : CharP K 3 := hU.charP
  have two_ne : (2 : K) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff K 3] at h2'
    omega
  obtain ⟨x, y, cc, hdet, hx, hy, hc⟩ := CFSG.ASVolI.burnsideA315y_u3_exists_xyc hU (by norm_num)
  have hrange := CFSG.ASVolI.burnsideA315y_u3_hoddc hU two_ne hdet hx hy hc φ hφ
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK432.U3Char3.isInnerAut_of_mem_psuConj_range_of_mod
    hU (by norm_num) hrange
  exact ⟨g, hg.symm⟩

theorem l154_oddInner_of_u33 {S : Type} [Group S] (h : catalogIs S l154AmbU33) :
    ∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    obtain ⟨q, rfl, h3⟩ := l154AmbU33_twistedA hv hi
    have hM := CFSG.Models.lieModel_twistedA 2 q hv e
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 2 q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
    rw [hc, hf] at hM
    have hsc : CFSG.Open.StatedClassicalModel S .PSU (2 + 1) q.p q.exponent :=
      hM.2.resolve_right (fun h => absurd h.1 (by norm_num))
    obtain ⟨-, K, instK, finK, hcardK, ⟨e₀⟩⟩ : CFSG.Open.StatedLieAdmissible .PSU (2 + 1) q.p q.exponent ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
          Nonempty (S ≃* CFSG.Open.StatedProj
            (CFSG.Open.StatedSU (2 + 1) (q.p ^ q.exponent) K)) := hsc
    have hq3 : q.p ^ q.exponent = 3 ^ 1 :=
      ((TauCeti.PrimePower.card_def q).symm.trans h3).trans (pow_one 3).symm
    rw [hq3] at hcardK e₀
    have hU : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hcardK]; norm_num⟩
    exact oddInner_transport (e₀.trans (unitaryPSUEquiv hU (by norm_num)).symm)
      (l154_oddInner_unitaryPSU_three hU)

section Certs


theorem l154NIDOn_ambU33 : L154NIDOn l154AmbU33 := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_odd_inner hp hp2 hK hKc hyN hyp hField (l154_oddInner_of_u33 hQ)).elim

theorem l154TD4On_ambU33 : L154TD4On l154AmbU33 := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_odd_inner hp hp2 hK hKc hyN hyp hField (l154_oddInner_of_u33 hQ)).elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155X
