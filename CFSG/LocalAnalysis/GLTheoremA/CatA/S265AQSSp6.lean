module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AP2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp6Big
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA S265
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddSchurTrivial_statedSp)

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

omit [Finite Ω] in
private theorem three_dvd_card_of_sp6 (hJ : catalogIs (PSimple 3 K) S9.isSp6two) :
    3 ∣ Nat.card ↥K := by
  obtain ⟨e⟩ := CatB.bridge_sp6two hJ
  have hc : Nat.card (StatedSp 3 (ZMod 2)) = 1451520 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
      show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by norm_num),
      Finset.prod_pair (by norm_num)]
    norm_num
  have h3 : 3 ∣ Nat.card (PSimple 3 K) := by
    rw [(Nat.card_congr e.toEquiv).trans hc]
    norm_num
  exact h3.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))

private theorem card_lt_of_sp6 (h : QSNL 3 S B T x D K)
    (hJ : catalogIs (PSimple 3 K) S9.isSp6two) : Nat.card B < 27 * Nat.card D :=
  lt_of_not_ge fun h27 => false_of_sp6_big (h.nlAct (three_dvd_card_of_sp6 hJ)) h.cfg.elem hJ h27

private theorem center_pQuot_eq_bot_of_oddSchur {X J : Subgroup Ω} (hJ : GLAPComponent 3 X J)
    (hS : OddSchurTrivial (PSimple 3 J)) : Subgroup.center (PQuot 3 J) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hodd : Odd (Nat.card ↥(QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (I2611.isPGroup_center_pQuot' Nat.prime_three J).exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hinj := hS (PQuot 3 J) ⟨hq.1⟩ (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le hodd
  rw [← QuotientGroup.ker_mk' (Subgroup.center (PQuot 3 J))]
  exact (MonoidHom.ker_eq_bot_iff _).2 hinj

theorem QSNL.card_eq_nine_mul_of_sp6 (h : QSNL 3 S B T x D K)
    (hJ : catalogIs (PSimple 3 K) S9.isSp6two) : Nat.card B = 9 * Nat.card D := by
  obtain ⟨-, -, hD9, -, -, -, -⟩ := h.cfg.std
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlt := card_lt_of_sp6 h hJ
  have hbig := h.cfg.big
  obtain ⟨k, hk⟩ := h.cfg.elem.isPGroup.exists_card_eq
  rw [hD9, hk] at hlt ⊢
  rw [hk] at hbig
  have h4 : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 hbig
  have h5' : 3 ^ k < 3 ^ 5 := by
    norm_num at hlt ⊢
    omega
  have h5 : k < 5 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5'
  obtain rfl : k = 4 := by omega
  norm_num


theorem QSNL.commutator_ne_bot_of_sp6 (h : QSNL 3 S B T x D K)
    (hJ : catalogIs (PSimple 3 K) S9.isSp6two) : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥ := by
  obtain ⟨-, hDe, -, -, -, -, hDK⟩ := h.cfg.std
  obtain ⟨e⟩ := CatB.bridge_sp6two hJ
  have hN := h.nlAct (three_dvd_card_of_sp6 hJ)
  have hZ := center_pQuot_eq_bot_of_oddSchur hN.comp
    ((oddSchurTrivial_statedSp 3 (ZMod 2)).of_mulEquiv e.symm)
  obtain ⟨E, -, hED, hcard⟩ :=
    exists_big_torus_of_sp6 hZ hDe (fun d hd => (hDK.le hd).2) e
  refine h.cfg.maxc.resolve_right fun hmax => ?_
  have h1 := hmax.1 _ hED
  have h2 := card_lt_of_sp6 h hJ
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
