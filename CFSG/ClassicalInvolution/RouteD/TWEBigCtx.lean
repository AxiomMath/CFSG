module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootCtx
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE
public import CFSG.ClassicalInvolution.Asc77.WP3L54Thm54
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.Big

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open scoped commutatorElement

set_option linter.unusedSectionVars false

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Shape

variable {p f : ℕ} [Fact p.Prime]

@[expose] def BigTwin (t : LTag) (n : ℕ) : Prop :=
  (t = .PSp ∧ n = 2) ∨ (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4) ∨ (t = .POmegaOdd ∧ 3 ≤ n) ∨
    (t = .POmegaPlus ∧ 4 ≤ n) ∨ (t = .POmegaMinus ∧ 4 ≤ n)

@[expose] def TwinShapeData {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) : Prop :=
  D.card = 3 ∧ ∃ i₀ i₁ i₂ : Fin D.card, i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₀ ≠ i₂ ∧ D.tag i₀ = .PSL ∧
    D.rank i₀ = 2 ∧ D.tag i₂ = .PSL ∧ D.rank i₂ = 2 ∧ BigTwin (D.tag i₁) (D.rank i₁)

variable {G : Type} [Group G] [Finite G]

@[expose] def TwinLieShape (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∃ D : LocalLieSystemAt p f (exactFamily Ω z) z, TwinShapeData D

@[expose] def TwinExactShape (p f : ℕ) [Fact p.Prime] (K : Subgroup G) (z : G) : Prop :=
  TwinLieShape p f (CoreAssembly.conjClass K) z ∧
    ∃ T ∈ CoreAssembly.conjClass K, Commutes K T ∧ IsClassicalMember p f T z

end Shape

section Fin3

theorem eq_cases_of_card_three {n : ℕ} (hn : n = 3) {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (j : Fin n) : j = a ∨ j = b ∨ j = c := by
  have hj := j.2
  have h0 := a.2
  have h1 := b.2
  have h2 := c.2
  have n01 : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have n12 : b.val ≠ c.val := fun e => hbc (Fin.ext e)
  have n02 : a.val ≠ c.val := fun e => hac (Fin.ext e)
  by_contra hcon
  push Not at hcon
  have a1 : j.val ≠ a.val := fun e => hcon.1 (Fin.ext e)
  have a2 : j.val ≠ b.val := fun e => hcon.2.1 (Fin.ext e)
  have a3 : j.val ≠ c.val := fun e => hcon.2.2 (Fin.ext e)
  omega

end Fin3

section Ctx

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure TwinShapeCtx (Ω : Set (Subgroup G)) (z : G) extends XCtx p f Ω z where
  card_eq : D.card = 3
  i₀ : Fin D.card
  i₁ : Fin D.card
  i₂ : Fin D.card
  ne₀₁ : i₀ ≠ i₁
  ne₁₂ : i₁ ≠ i₂
  ne₀₂ : i₀ ≠ i₂
  tag₀ : D.tag i₀ = .PSL
  rank₀ : D.rank i₀ = 2
  tag₂ : D.tag i₂ = .PSL
  rank₂ : D.rank i₂ = 2
  listed : BigTwin (D.tag i₁) (D.rank i₁)

variable {p f} {Ω : Set (Subgroup G)} {z : G}

namespace TwinShapeCtx

variable (C : TwinShapeCtx p f Ω z)

include C

theorem listed_tag_ne : C.D.tag C.i₁ ≠ .G2 ∧ C.D.tag C.i₁ ≠ .trialityD4 := by
  rcases C.listed with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    exact ⟨by decide, by decide⟩

structure Spec : Prop where
  hK₀ : modOdd z (exactCore z C.K) = (C.psi C.i₀).range
  hcls : oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi C.i₂).range

variable {C}

theorem classical_of_range {N : Subgroup G} (hN : N ∈ tqMembers Ω z) {w : G}
    (hw : IsClassicalMember p f N w) {j : Fin C.D.card}
    (hmod : modOdd z (exactCore z N) = (C.psi j).range)
    (hz : oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi j).range) : w = z := by
  have hzC := XCtx.hzC z
  have hU := C.isUniqueInvolution_modOdd hN hw
  rw [hmod] at hU
  have hzsq : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨z, hzC⟩ = 1 :=
      Subtype.ext C.hKz.sq
    rw [this, map_one]
  have hz1 : oddQuotMk z ⟨z, hzC⟩ ≠ 1 := fun h =>
    C.hKz.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h))
  have heq : oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩ = oddQuotMk z ⟨z, hzC⟩ :=
    ((hU.unique _ hz hzsq).resolve_left hz1).symm
  have hwY : w ∈ exactLayer Ω z :=
    exactCore_le_exactLayer hN (C.involution_mem_exactCore hN hw)
  obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY C.z_mem_exactLayer
    (isCentralInvolution_of_isClassicalMember hw).sq C.hKz.sq heq
  rw [hwo]
  exact conj_eq_of_mem_centralizer_singleton
    (exactLayer_le_centralizer Ω z (oddCoreIn_le _ ho))

variable (C)

theorem exists_twin (S : C.Spec) : ∃ T ∈ Ω, IsClassicalMember p f T z ∧
    modOdd z T = (C.psi C.i₂).range := by
  have hj : C.D.tag C.i₂ = .PSL ∧ C.D.rank C.i₂ = 2 := ⟨C.tag₂, C.rank₂⟩
  obtain ⟨R, hR, -⟩ := C.D.meets C.i₂
  obtain ⟨N, hN, hNmod⟩ := C.exists_member_of_fund C.i₂
    (C.single C.i₂ (by rw [C.tag₂]; decide) (by rw [C.tag₂]; decide)) hR
  rw [C.fund_eq_top C.i₂ hj hR, Subgroup.map_top] at hNmod
  obtain ⟨w, hw⟩ := C.hΩ.classical N hN.1
  have hwz : w = z := classical_of_range hN hw hNmod S.hcls
  subst hwz
  have hNc : N ≤ Subgroup.centralizer ({w} : Set G) := le_centralizer_of_isClassicalMember hw
  have hNeq : exactCore w N = N := exactCore_eq_self hw.perfect hNc
  rw [hNeq] at hNmod
  exact ⟨N, hN.1, hw, hNmod⟩

theorem rng_ne (S : C.Spec) : (C.psi C.i₀).range ≠ (C.psi C.i₂).range := by
  intro h
  refine C.range_not_comm_of_A1 C.i₀ ⟨C.tag₀, C.rank₀⟩ ?_ ?_
  · rw [← S.hK₀]
    exact oddQuotMk_mem_modOdd (C.involution_mem_exactCore C.K_tq C.K_cl) (XCtx.hzC z)
  · intro a ha b hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', hb'⟩ : b ∈ (C.psi C.i₂).range := h ▸ hb
    rw [← hb']
    exact C.psi_commute C.ne₀₂ a' b'

end TwinShapeCtx

end Ctx

section Build

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem exists_twinShapeCtx (X : XCtx p f Ω z) (hD : TwinShapeData X.D) {T : Subgroup G}
    (hT : T ∈ Ω) (hTz : IsClassicalMember p f T z) (hcomm : Commutes X.K T) :
    ∃ C : TwinShapeCtx p f Ω z, Nonempty C.Spec := by
  obtain ⟨hcard, a₀, a₁, a₂, -, -, -, -, -, -, -, hlist⟩ := hD
  have hA₁ : ¬ (X.D.tag a₁ = .PSL ∧ X.D.rank a₁ = 2) := by
    rintro ⟨h1, h2⟩
    rcases hlist with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h1] at h
      exact absurd h (by decide)
    · omega
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
  have hzC := XCtx.hzC z
  obtain ⟨j, hj, hjK⟩ := X.exists_A1_of_K
  obtain ⟨j', hj', hjT⟩ := X.exists_A1_of_member hT hTz
  have hzT : oddQuotMk z ⟨z, hzC⟩ ∈ (X.psi j').range := by
    rw [← hjT]
    exact oddQuotMk_mem_modOdd hTz.mem hzC
  have hne : j ≠ j' := by
    intro h
    subst h
    refine X.range_not_comm_of_A1 j hj ?_ ?_
    · rw [← hjK]
      exact oddQuotMk_mem_modOdd (X.involution_mem_exactCore X.K_tq X.K_cl) hzC
    · intro a ha b hb
      rw [← hjK] at ha
      rw [← hjT] at hb
      obtain ⟨k, hk, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [X.exactCore_K] at hk
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hcomm _ hk _ hy))
  let C : TwinShapeCtx p f Ω z :=
    { toXCtx := X
      card_eq := hcard
      i₀ := j
      i₁ := a₁
      i₂ := j'
      ne₀₁ := fun h => hA₁ (by rw [← h]; exact hj)
      ne₁₂ := fun h => hA₁ (by rw [h]; exact hj')
      ne₀₂ := hne
      tag₀ := hj.1
      rank₀ := hj.2
      tag₂ := hj'.1
      rank₂ := hj'.2
      listed := hlist }
  exact ⟨C, ⟨⟨hjK, hzT⟩⟩⟩

end Build

end CFSG.ClassicalInvolution.RouteD.TWE.Big
