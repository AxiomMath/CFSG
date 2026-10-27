module

public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofExc
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open


theorem noSmall_lie_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq : q.card = 2) :
    HStdExcl.NoSmall (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  intro α hα3 hα1 I hI hsmall
  have hq' : q.card = 2 ^ 1 := by rw [pow_one]; exact hq
  have hcard : Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group =
      CFSG.Open.ordTrialityD4 (2 ^ 1) := by
    rw [CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_trialityD4_carrier q hv, hq']
  have h5 : 5 ∣ Nat.card (↥I ⧸ Subgroup.center ↥I) := by
    rcases hsmall with h | h <;> rw [h] <;> norm_num
  have hdvd1 : Nat.card (↥I ⧸ Subgroup.center ↥I) ∣ Nat.card ↥I :=
    ⟨Nat.card ↥(Subgroup.center ↥I),
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥I)⟩
  have hdvd2 : Nat.card ↥I ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
    have h : Nat.card ↥I ∣ Nat.card ↥(⊤ : Subgroup
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :=
      Subgroup.card_dvd_of_le (le_top : I ≤ ⊤)
    simpa [Subgroup.card_top] using h
  have h5S : 5 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group :=
    h5.trans (hdvd1.trans hdvd2)
  rw [hcard] at h5S
  exact CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof.not_five_dvd_ordTrialityD4
    (f := 1) (by decide) h5S

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
