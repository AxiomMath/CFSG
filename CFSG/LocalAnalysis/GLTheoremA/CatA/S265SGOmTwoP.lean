module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.Adapters.LinearCatalog
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinOmega
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinZ
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmGaps
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGU
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Quasithin.Vol2.Ch11SecQ9aL34A
import CFSG.Timmesfeld.Orders.ClassicalLinearThree
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
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
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import CFSG.LargeExtraspecial.S14Defs
import CFSG.LargeExtraspecial.S14Inputs
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
import Certificates.Data.U62Rank.Check

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

private theorem lin_arith {N n : ℕ} (hn1 : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1) (hN : N ∣ 197406720)
    (hc : N * 3 = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) :
    n = 2 ∧ N = 20160 := by
  have hd : (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ∣ 197406720 * 3 := by
    rw [← hc]
    exact Nat.mul_dvd_mul_right hN 3
  have hle : (2 ^ n) ^ 3 ≤ N * 3 :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_dvd_of_pos hN (by norm_num)) (by norm_num)) ⟨_, hc⟩
  have hNle : N ≤ 197406720 := Nat.le_of_dvd (by norm_num) hN
  have hn : n < 10 := by
    by_contra hn
    have h2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega :
      10 ≤ n)) 3
    norm_num at h2
    omega
  obtain rfl : n = 2 := by
    revert h3 hd
    interval_cases n <;> decide +kernel
  norm_num at hc
  exact ⟨rfl, by omega⟩

private theorem uni_arith {N n : ℕ} (hq : 3 ≤ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) (hN : N ∣ 197406720)
    (hc : N * 3 = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1))) : False := by
  have hd : (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) ∣ 197406720 * 3 := by
    rw [← hc]
    exact Nat.mul_dvd_mul_right hN 3
  have hle : (2 ^ n) ^ 3 ≤ N * 3 :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_dvd_of_pos hN (by norm_num)) (by norm_num)) ⟨_, hc⟩
  have hNle : N ≤ 197406720 := Nat.le_of_dvd (by norm_num) hN
  have hn : n < 10 := by
    by_contra hn
    have h2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega :
      10 ≤ n)) 3
    norm_num at h2
    omega
  revert hq h3 hd
  interval_cases n <;> decide +kernel

theorem SG.tyF_three_of_dvd {X : Type} [Group X] (h : catalogIs X (tyF 3))
    (hX : Nat.card X ∣ 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17) :
    Nat.card X = 20160 ∧ ∀ x : X, orderOf x ≠ 15 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _ <;> try exact (hi : False).elim
  cases l
  case A r q =>
    obtain ⟨hr, hq2, h3⟩ := (hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1)
    obtain rfl : r = 2 := by omega
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    set eP := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
    have hF := GaloisField.card q.p q.exponent q.exponent_pos.ne'
    have hc := CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd
      (K := GaloisField q.p q.exponent)
    rw [← Nat.card_congr (eP.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 _)).toEquiv,
      hF, hq2] at hc
    rw [TauCeti.PrimePower.card_def, hq2] at h3
    rw [Nat.gcd_eq_left h3] at hc
    obtain ⟨hn, hN⟩ := lin_arith q.exponent_pos h3 (by simpa using hX) hc
    have hF4 : Nat.card (GaloisField q.p q.exponent) = 4 := by rw [hF, hq2, hn]; norm_num
    exact ⟨hN, fun x hx => CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.orderOf_ne_fifteen hF4 (eP x)
      (by rw [MulEquiv.orderOf_eq]; exact hx)⟩
  case twistedA r q =>
    obtain ⟨hr, hq2, h3⟩ := (hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1)
    obtain rfl : r = 2 := by omega
    have hq3 := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
    obtain ⟨⟨hp, hm, -⟩, F, _, _, hFc, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hc := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hm hFc
    rw [← Nat.card_congr eT.toEquiv, hq2] at hc
    rw [TauCeti.PrimePower.card_def, hq2] at h3 hq3
    rw [Nat.gcd_eq_left h3] at hc
    exact (uni_arith hq3 h3 (by simpa using hX) hc).elim
  all_goals exact (hi : False).elim

theorem SG.conclB_rPlus_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∀ X : Subgroup (OrthRest.RPlus K 4), IsElemAbelian 3 X → Nat.card X = 3 ^ 3 →
      ∀ d ∈ X, d ≠ 1 → ∀ J : Subgroup (OrthRest.RPlus K 4),
      IsComponentOf J (Subgroup.centralizer ({d} : Set (OrthRest.RPlus K 4))) →
      catalogIs (J ⧸ Subgroup.center J) (tyF 3) →
      ∃ Y ≤ X, d ∈ Y ∧ Nat.card Y = 3 ^ 2 ∧ ∃ A : Subgroup (OrthRest.RPlus K 4),
        A ≤ Subgroup.centralizer (Y : Set (OrthRest.RPlus K 4)) ∧ IsSimpleGroup A ∧
        (∃ a b : A, a * b ≠ b * a) ∧ 3 ∣ Nat.card A := by
  intro X hX _ d hdX hd1 J hJ hcat
  exfalso
  obtain ⟨φ⟩ := CatB.exists_ringEquiv_zmod_two hK
  obtain ⟨e⟩ : Nonempty (OrthRest.RPlus K 4 ≃* ↥CFSG.AGLEmbedding.Om8) :=
    ⟨CatB.statedProjEquivZMod2 φ (CatB.glCongr_statedOmega_plus φ 4)⟩
  have hs3 : (MulAut.conj (e d)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hX.2 d hdX, map_one, map_one]
  have hs1 : MulAut.conj (e d) ≠ 1 := fun h1 => hd1 (e.injective (by
    have hc : e d ∈ Subgroup.center ↥CFSG.AGLEmbedding.Om8 := Subgroup.mem_center_iff.2 fun g => by
      have h2 := congrArg (fun f : MulAut ↥CFSG.AGLEmbedding.Om8 => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * e d = e d * g * (e d)⁻¹ * e d := by rw [h2]
        _ = e d * g := inv_mul_cancel_right _ _
    rw [HSubT.center_aglOm8_eq_bot, Subgroup.mem_bot] at hc
    rw [hc, map_one]))
  have hJ' : IsComponentOf (J.map (e : OrthRest.RPlus K 4 →* ↥CFSG.AGLEmbedding.Om8))
      (Subgroup.centralizer ({e d} : Set ↥CFSG.AGLEmbedding.Om8)) := by
    have h := HSubT.isComponentOf_map_mulEquiv hJ e
    rwa [HSubT.map_centralizer_singleton e d] at h
  have hU := HSubT.omega_comp_om8 HSubT.guBlockFacts_holds
    (HSubT.omegaCentDecomp_of_gaps HSubT.center_aglOm8_eq_bot HSubT.omegaUnitaryInOm8_holds
      HSubT.omegaOrthRank2Solvable_holds HSubT.omegaOrthRank1U4_holds) (e d) hs3 hs1 hJ'
  set eL := J.equivMapOfInjective (e : OrthRest.RPlus K 4 →* ↥CFSG.AGLEmbedding.Om8) e.injective
  obtain ⟨g⟩ := CatB.bridge_u4two hU
  have hcard : Nat.card (J ⧸ Subgroup.center J) = 25920 := by
    rw [Nat.card_congr ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans g).toEquiv,
      CFSG.LieType.Multipliers.U42.card_PSp43]
  have h := (SG.tyF_three_of_dvd hcat (by rw [hcard]; norm_num)).1
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265

end
