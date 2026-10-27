module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
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
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
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
import CFSG.Blueprint.LieModelAPI
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.LargeExtraspecial.OfFStar
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.Models.Transport
import CFSG.RankThree.GroupTheory.ClassTwoThree
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem qsConcl_of_fix_pair {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSCfg 3 S B T x D K) {d e : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (heB : e ∈ B) (heD : e ∉ D)
    (hdN : d ∈ Subgroup.normalizer (S : Set Ω)) (heN : e ∈ Subgroup.normalizer (S : Set Ω))
    (hlay : GLAPLayer 3 (fixSubgroup (chevAut 3 S ⟨d, hdN⟩) ⊓
      fixSubgroup (chevAut 3 S ⟨e, heN⟩)) ≠ ⊥) : QSConcl 3 S B D K := by
  haveI := Fact.mk Nat.prime_three
  obtain ⟨hDB, -, hDc, hxD, -⟩ := h.std
  have hdB : d ∈ B := hDB hdD
  have hordx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 x h.xB) h.x1]
  have hordd : Nat.card (Subgroup.zpowers d) = 3 := by
    have hd1 : d ≠ 1 := fun h1 => hdx (h1 ▸ (Subgroup.zpowers x).one_mem)
    rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 d hdB) hd1]
  have hcard : Nat.card ↥(Dgrp d x) = 3 ^ 2 := by
    rw [dgrp_eq]
    exact s265_card_sup Nat.prime_three h.elem (Subgroup.zpowers_le.2 h.xB)
      (by rw [hordx, pow_one]) hdB hdx hordd
  have hDeq : Dgrp d x = D :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le D).2 (by
      intro z hz
      rcases hz with rfl | rfl
      exacts [hdD, hxD])) (le_of_eq (by rw [hDc, hcard]))
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun g _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.xcen g)
  obtain ⟨E, hEB, hEab, hEc, hDE, hlayE⟩ := S265F3.exists_e3_of_layer Nat.prime_three h.elem h.xB
    h.x1 hSx hdB hdx heB (by rw [hDeq]; exact heD)
    (S265F3.glaPLayer_inf_cx_ne_bot_of_fix Nat.prime_three h.core hdN heN hlay)
  exact Or.inl ⟨E, ⟨hEB, hEab, hEc⟩, hDeq ▸ hDE, hlayE⟩

private theorem psuModel_of_twistedA_two {G : Type} [Group G] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.card = 2)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    StatedClassicalModel G .PSU (r + 1) 2 1 := by
  have hq' : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  obtain ⟨hp, hf⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq'
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rwa [hp, hf] at hm

private theorem eleven_dvd_card_of_u56 {G : Type} [Group G]
    (h : catalogIs G S9.isU5two ∨ catalogIs G S9.isU6two) : 11 ∣ Nat.card G := by
  rcases h with h | h
  · obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isU5two h
    rw [StatedAPI.card_of_statedClassicalModel_psu_five_two (psuModel_of_twistedA_two hv hq e)]
    norm_num
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · rw [StatedAPI.card_of_statedClassicalModel_psu_six_two (psuModel_of_twistedA_two hv hP e)]
        norm_num
      · exact hP.elim
    | _ => exact hP.elim

theorem exists_order_eleven_chevAut_ne_one {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSCfg 3 S B T x D K)
    (hK : catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two) :
    ∃ y ∈ K, orderOf y = 11 ∧
      ∀ hy : y ∈ Subgroup.normalizer (S : Set Ω), chevAut 3 S ⟨y, hy⟩ ≠ 1 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, -, hKc, -⟩ := h.std
  have hKS : K ≤ S := hKc.1.trans inf_le_left
  have h11 : 11 ∣ Nat.card K :=
    (eleven_dvd_card_of_u56 hK).trans (Subgroup.card_dvd_of_surjective (chevQuotHom_surjective 3 K))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 11 h11
  have hy11 : orderOf (y : Ω) = 11 := by rw [Subgroup.orderOf_coe]; exact hy
  refine ⟨y, y.2, hy11, fun hyN h1 => ?_⟩
  have hcm := centMod_iff.1 ((chevAut_eq_one_iff Nat.prime_three h.comp hyN).1 h1)
  have hO : GLAPPrimeCoreOf 3 S = ⊥ := CFSG.gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.2 h.core
  have hcen : (⟨y, hKS y.2⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h2 := hcm.2 s s.2
    rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact Subtype.ext h2
  have hN : (Subgroup.zpowers (⟨y, hKS y.2⟩ : ↥S)).Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hcen hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers (⟨y, hKS y.2⟩ : ↥S))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy]
    norm_num
  have h0 := CFSG.pPrimeCore_eq_bot_iff.1 h.core _ hN hcop
  rw [Subgroup.zpowers_eq_bot] at h0
  have h3 : (y : Ω) = 1 := congrArg Subtype.val h0
  rw [h3, orderOf_one] at hy11
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
