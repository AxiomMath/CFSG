module

public import CFSG.ClassicalInvolution.ModelFacts.FundCentralizerNormalizer
import CFSG.ClassicalInvolution.Q3.Q3OFShG2
import CFSG.ClassicalInvolution.Asc77.AscIHD4
import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Model
import CFSG.Quasithin.Vol2.Ch10SecQ3CZO
import CFSG.ClassicalInvolution.AschTight.Sec6Gen64O
import CFSG.RankThree.PartOne.TCX.Ree.SL2Facts
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.TwinLookup
public import CFSG.ClassicalInvolution.AschTight.S1911P3a
public import CFSG.ClassicalInvolution.AschTight.S1911P3b
public import CFSG.ClassicalInvolution.AschTight.S1911SecG
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
import CFSG.ClassicalInvolution.Q3.OddCoreCentral
import CFSG.ClassicalInvolution.Q3.Q3NTAlpha
import CFSG.ClassicalInvolution.Q3.Q3OFModelU
import CFSG.ClassicalInvolution.Q3.Q3OFProd
import CFSG.ClassicalInvolution.Q3.Q3OFShCrit
import CFSG.ClassicalInvolution.Q3.Q3OFUnique
import CFSG.ClassicalInvolution.Q3.Q3URDict
import CFSG.ClassicalInvolution.Q3.Q3URStd
import CFSG.ClassicalInvolution.Q3.Q3URTransfer
import CFSG.ClassicalInvolution.Q3.Q3WAComp
import CFSG.ClassicalInvolution.Q3.Q3WAEDict
import CFSG.ClassicalInvolution.Q3.Q3WARow
import CFSG.ClassicalInvolution.Q3.Q3WMain
import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
import CFSG.Mathlib.RingTheory.UnitOrderOf
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.A1cA133Three
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.InternalSecB51
import CFSG.Quasithin.EmptyFaithful.S14117Coprime
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecALiftCore
import CFSG.Quasithin.Vol2.Ch10SecB3FactsE
import CFSG.Quasithin.Vol2.Ch10SecB3Obl
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecE22OneB
import CFSG.Quasithin.Vol2.Ch10SecEOver
import CFSG.Quasithin.Vol2.Ch10SecQ3CC
import CFSG.Quasithin.Vol2.Ch10SecQ3CJ
import CFSG.Quasithin.Vol2.Ch10SecQ3CV
import CFSG.Quasithin.Vol2.Ch10SecQ3CZF
import CFSG.Quasithin.Vol2.Ch10SecQ4S7
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11SecBDerived
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsE
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.KLC.LayerData
import CFSG.RankThree.PartOne.KLCE.EngineGroup
import CFSG.RankThree.PartOne.KLCE.TypeSL
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem commutator_eq_bot_of_mulEquiv_sl2_of_card_lt {G : Type} [Group G] [Finite G]
    {B L : Subgroup G} {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']
    (h4 : 4 ≤ Nat.card F') (hlt : Nat.card F < Nat.card F') (eB : ↥B ≃* SL(2, F))
    (eL : ↥L ≃* SL(2, F')) (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) : ⁅B, L⁆ = ⊥ := by
  refine CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.commutator_eq_bot_of_quasisimple
    (CFSG.Open.IsQuasisimple.of_mulEquiv eL
      (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two h4)) hLB hBL fun hle => ?_
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_congr eL.toEquiv, Nat.card_congr eB.toEquiv] at hcard
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  exact absurd hcard (not_le.mpr (CFSG.RankThree.PartOne.TCX.Ree.sl2_card_lt h2 hlt))

variable {p e : ℕ} [Fact p.Prime]


theorem commutator_eq_bot_of_mem_fundamentalSubgroups_trialityD4 (hp2 : p ≠ 2) {n : ℕ}
    (hfund : Generic.IsFundTag .trialityD4) (hadm : StatedLieAdmissible .trialityD4 n p e)
    {R R' : Subgroup (Generic.modelUniv .trialityD4 n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups .trialityD4
      (Generic.modelUniv .trialityD4 n p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups .trialityD4
      (Generic.modelUniv .trialityD4 n p e Fact.out).D)
    (hne : R ≠ R') {z : (Generic.modelUniv .trialityD4 n p e Fact.out).K}
    (hz : Generic.IsUniqueInvolution R z) (hz' : Generic.IsUniqueInvolution R' z) :
    ⁅R, R'⁆ = ⊥ := by
  have hn : n = 0 := hadm.2.2
  subst hn
  have he : 1 ≤ e := hadm.2.1
  have hWR := centralizer_le_normalizer_of_mem_fundamentalSubgroups hp2 hfund hadm hR hz
  have hWR' := centralizer_le_normalizer_of_mem_fundamentalSubgroups hp2 hfund hadm hR' hz'
  have hRN : R ≤
      Subgroup.normalizer (R' : Set (Generic.modelUniv .trialityD4 0 p e Fact.out).K) :=
    (Disconnected.AschTight.Sec6Gen.le_centralizer_of_isUniqueInvolution hz).trans hWR'
  have hR'N : R' ≤
      Subgroup.normalizer (R : Set (Generic.modelUniv .trialityD4 0 p e Fact.out).K) :=
    (Disconnected.AschTight.Sec6Gen.le_centralizer_of_isUniqueInvolution hz').trans hWR
  by_cases hconj : ∃ g, R' = R.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    have hg' : R' = Generic.conjSub g R := hg
    exact absurd (hg'.trans (G2D4Models.noTwinsFund_td4 hp2 hadm R hR z hz g (hg' ▸ hz'))).symm hne
  have hcardne : Nat.card ↥R ≠ Nat.card ↥R' :=
    Asc77.d4OrdersDiffer p .trialityD4 0 e rfl hadm R hR R' hR' hconj
  have := finite_modelUniv hp2 Fact.out hfund hadm
  have hlt : Nat.card (GaloisField p e) < Nat.card (GaloisField p (3 * e)) := by
    rw [GaloisField.card p e (by omega), GaloisField.card p (3 * e) (by omega)]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
    rw [GaloisField.card p (3 * e) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le 2
      _ ≤ p ^ (3 * e) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR with
    ⟨⟨eR⟩⟩ | ⟨-, ⟨eR⟩⟩ <;>
  rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR' with
    ⟨⟨eR'⟩⟩ | ⟨-, ⟨eR'⟩⟩
  · exact absurd (by rw [Nat.card_congr eR.toEquiv, Nat.card_congr eR'.toEquiv]) hcardne
  · exact commutator_eq_bot_of_mulEquiv_sl2_of_card_lt h4 hlt eR eR' hR'N hRN
  · rw [Subgroup.commutator_comm]
    exact commutator_eq_bot_of_mulEquiv_sl2_of_card_lt h4 hlt eR' eR hRN hR'N
  · exact absurd (by rw [Nat.card_congr eR.toEquiv, Nat.card_congr eR'.toEquiv]) hcardne

theorem commutator_eq_bot_of_mem_fundamentalSubgroups (hp2 : p ≠ 2) {t : StatedLieTag} {n : ℕ}
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R R' : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hne : R ≠ R') {z : (Generic.modelUniv t n p e Fact.out).K}
    (hz : Generic.IsUniqueInvolution R z) (hz' : Generic.IsUniqueInvolution R' z) :
    ⁅R, R'⁆ = ⊥ := by
  by_cases hD4 : t = .trialityD4
  · subst hD4
    exact commutator_eq_bot_of_mem_fundamentalSubgroups_trialityD4 hp2 hfund hadm hR hR' hne hz hz'
  · by_cases hG2 : t = .G2
    ·
      subst hG2
      have hn : n = 0 := hadm.2.2.1
      subst hn
      have hz2 : orderOf z = 2 :=
        orderOf_eq_prime (by simpa [pow_two] using hz.sq) hz.ne_one
      rcases CFSG.ClassicalInvolution.Q3.Q3OF.g2_dichotomy hp2 hadm.2.1 R hR R' hR' z hz.mem
        hz'.mem hz2 with h | h
      · exact absurd h hne
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (h x hx y hy).symm
    ·
      have hsingle : Generic.FundamentalSingleClass t (Generic.modelUniv t n p e Fact.out).D :=
        CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass t n p e Fact.out hfund hadm
          hG2 hD4
      have hWR := centralizer_le_normalizer_of_mem_fundamentalSubgroups hp2 hfund hadm hR hz
      obtain ⟨g, hg⟩ := hsingle R hR R' hR'
      have hg' : R' = Generic.conjSub g R := hg
      have hz'' : Generic.IsUniqueInvolution (Generic.conjSub g R) z := hg' ▸ hz'
      have hzeq : z = g * z * g⁻¹ := hz''.eq (hz.conj g)
      have hgmem : g ∈
          Subgroup.centralizer ({z} : Set (Generic.modelUniv t n p e Fact.out).K) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g * z = (g * z * g⁻¹) * g := by group
          _ = z * g := by rw [← hzeq]
      exfalso
      exact hne (hg'.trans (Generic.conjSub_eq_of_mem_normalizer (hWR hgmem))).symm

end CFSG.ClassicalInvolution.ModelFacts
