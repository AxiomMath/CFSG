module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47L216Normalizer
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GroupTheory.SylowIntersectionControl.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bConj
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitConjugate
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LinearAlgebra.ScalarGraphAction
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.GH74.GLS.C3.Layer1.BackAuxCI
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.GH74.GLS.Prop27.Balance
public import CFSG.GroupTheory.SuzukiTwoGroupsCoprime
public import CFSG.Quasithin.EmptyFaithful.SBc16SAut
public import CFSG.LocalAnalysis.ComponentClassification.FooteProperFixedA7
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldCentralizer
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Walter.Bender1970.S2.Involutions
public import TauCeti.GroupTheory.DerivedCentralQuotient
public import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsB
public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCA7
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import Certificates.Certificate5007

public section

namespace CFSG.ComponentClassification.Foote47L216

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ABGLocalTools
open scoped commutatorElement

local notation "PSL216BalanceT" =>
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)
local notation "PSL24BalanceT" =>
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

set_option maxHeartbeats 800000 in
theorem psl216_all_odd_aut_inner
    (a : MulAut PSL216BalanceT) (haodd : Odd (orderOf a)) :
    a ∈ (MulAut.conj : PSL216BalanceT →* MulAut PSL216BalanceT).range := by
  classical
  let q : MulAut CFSG.Quasithin.SBc16.L216 →* MulAut CFSG.Quasithin.SBc16.L216 ⧸ CFSG.Quasithin.SBc16.innerL216 :=
    QuotientGroup.mk' CFSG.Quasithin.SBc16.innerL216
  let β : MulAut CFSG.Quasithin.SBc16.L216 :=
    MulAut.congr (CFSG.Quasithin.SBc16.equivPSL2.symm) a
  have hβodd : Odd (orderOf β) := by
    rw [show β = MulAut.congr (CFSG.Quasithin.SBc16.equivPSL2.symm) a from rfl,
      MulEquiv.orderOf_eq]
    exact haodd
  have hqodd : Odd (orderOf (q β)) := hβodd.of_dvd_nat (orderOf_map_dvd q β)
  have hq1 : q β = 1 :=
    CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd
      CFSG.Quasithin.SBc16.isPGroup_quotient_innerL216 hqodd (pow_orderOf_eq_one _)
  have hβ : β ∈ CFSG.Quasithin.SBc16.innerL216 := (QuotientGroup.eq_one_iff _).mp hq1
  have hβrange : β ∈ (MulAut.conj : CFSG.Quasithin.SBc16.L216 →* MulAut CFSG.Quasithin.SBc16.L216).range := hβ
  have haPSL : a ∈ (MulAut.conj : PSL216BalanceT →* MulAut PSL216BalanceT).range := by
    have h := (FooteLit.congr_mem_innAut_iff CFSG.Quasithin.SBc16.equivPSL2 β).mpr hβrange
    have hcongr : MulAut.congr CFSG.Quasithin.SBc16.equivPSL2 β = a := by
      apply MulEquiv.ext
      intro x
      simp [β, MulAut.congr_apply, MulEquiv.trans_apply]
    simpa [FooteLit.innAut, hcongr] using h
  exact haPSL

theorem psl216_equiv_all_odd_aut_inner
    {S : Type} [Group S] (e : S ≃* PSL216BalanceT)
    (a : MulAut S) (haodd : Odd (orderOf a)) :
    a ∈ (MulAut.conj : S →* MulAut S).range := by
  let γ : MulAut PSL216BalanceT := MulAut.congr e a
  have hγodd : Odd (orderOf γ) := by
    rw [show γ = MulAut.congr e a from rfl, MulEquiv.orderOf_eq]
    exact haodd
  have hγin : γ ∈ (MulAut.conj : PSL216BalanceT →* MulAut PSL216BalanceT).range :=
    psl216_all_odd_aut_inner γ hγodd
  exact (FooteLit.congr_mem_innAut_iff e a).mp hγin

end CFSG.ComponentClassification.Foote47L216
