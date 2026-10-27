module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Sec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Gen
public import CFSG.Quasithin.Background.E1Sections
public import CFSG.GroupTheory.FixedCentralQuotientFamily
public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.Holt.General.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.WeakClosure81.EightNine
public import CFSG.LocalAnalysis.WeakClosure81.SevenNine
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenFour
public import CFSG.LocalAnalysis.WeakClosure81.W18PackFix
public import CFSG.LocalAnalysis.WeakClosure81.W18PackRank
public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Hyp197
public import CFSG.LocalAnalysis.WeakClosure81.W19Min
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B3Facts
public import CFSG.Quasithin.Background.B3FourConj
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E2TwoLieQuotLift
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.H16TwoM22
public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB45SL3Label
public import CFSG.Quasithin.Background.SmithB45SL3Outer
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.Vol2.Ch10SecA1011B
public import CFSG.Quasithin.Vol2.Ch10SecANat3
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch7NotFFS7
public import CFSG.Quasithin.Vol2.Ch8Sec2L825O
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Timmesfeld.Bridge.RootSetsSolv
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix5
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public noncomputable section

open scoped commutatorElement

namespace CFSG.GroupTheory.FixedCentralQuotientFamily

variable {X : Type} [Group X]
  {ι : Type*} (Z : Subgroup X) [Z.Normal] (ψ : ι → MulAut X)
  (hinv : ∀ i, Z.map (ψ i).toMonoidHom = Z)

theorem isSolvable_commonFixed_of_quotientFixed
    (hcentral : Z ≤ Subgroup.center X)
    (hsolv : Group.IsSolvable ↥(quotientFixed Z ψ hinv)) :
    Group.IsSolvable ↥(commonFixed ψ) := by
  let C : Subgroup X := commonFixed ψ
  let Q : Subgroup (X ⧸ Z) := quotientFixed Z ψ hinv
  let φ : ↥C →* ↥Q :=
    (projection Z ψ hinv).comp (Subgroup.inclusion (commonFixed_le Z ψ hinv))
  have hker : φ.ker ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxZ : x.val ∈ Z := by
      have h1 : (QuotientGroup.mk' Z) x.val = 1 := by
        exact congrArg (fun q : ↥Q => (q : X ⧸ Z)) hx
      exact (QuotientGroup.eq_one_iff x.val).mp h1
    exact Subgroup.mem_center_iff.mp (hcentral hxZ) y.val
  haveI : Group.IsSolvable ↥Q := hsolv
  exact Group.isSolvable_of_ker_le_range (Subgroup.center ↥C).subtype φ (by
    rw [Subgroup.range_subtype]
    exact hker)

variable [Finite X]

theorem hasNormalPComplement_commutator_quotientFixed {p : ℕ}
    (hcentral : Z ≤ Subgroup.center X)
    (hNPC : HasNormalPComplement p ↥(commonFixed ψ)) :
    HasNormalPComplement p ↥(⁅quotientFixed Z ψ hinv, quotientFixed Z ψ hinv⁆) := by
  have hNPC_D : HasNormalPComplement p
      ↥(⁅fixedPreimage Z ψ hinv, fixedPreimage Z ψ hinv⁆) :=
    hasNormalPComplement_of_le p
      (commutator_fixedPreimage_le_commonFixed Z ψ hinv hcentral) hNPC
  have h := CFSG.RankThree.Coprime.hasNormalPComplement_map
    (p := p) (f := QuotientGroup.mk' Z)
    (K := ⁅fixedPreimage Z ψ hinv, fixedPreimage Z ψ hinv⁆) hNPC_D
  rw [map_commutator_fixedPreimage_eq Z ψ hinv] at h
  exact h

end CFSG.GroupTheory.FixedCentralQuotientFamily
