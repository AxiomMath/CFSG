module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Orders
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructBase
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.RankThree.PartOne.S12.Sec1511AutL2
public import CFSG.GH74.KGroups.L28
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216
public import CFSG.GH74.KGroups.L34
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.Sporadic.J2
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CosetTableShort
public import CFSG.GH74.BNPair.Defs
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveOrderTwo
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate3085Base

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Blueprint

@[expose] def SmallOut (K : Type) [Group K] : Prop :=
  ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m

theorem smallOut_alt {K : Type} [Group K] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ≃* alternatingGroup (Fin n)) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  have h1 : Nat.card (MulAut (alternatingGroup (Fin n))) = Nat.card (Equiv.Perm (Fin n)) :=
    (Nat.card_eq_of_bijective _ hb).symm
  have h2 : Nat.card (alternatingGroup (Fin n)) * (alternatingGroup (Fin n)).index =
      Nat.card (Equiv.Perm (Fin n)) := Subgroup.card_mul_index _
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [alternatingGroup.index_eq_two] at h2
  refine ⟨2, ?_, by omega⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
  omega

theorem smallOut_L2odd {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h : LieModel K .PSL 2 p f)
    (hdvd : Nat.card K ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  rcases h with ⟨-, hadm, F, hFld, hFfin, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hFodd : Odd (Nat.card F) := by
      rw [hF]; exact (hp.odd_of_ne_two hp2).pow
    have hF3 : 3 < Nat.card F := by
      have h1 : 3 ≤ p := by
        rcases hp.eq_two_or_odd' with h2 | h2
        · exact absurd h2 hp2
        · have := hp.two_le
          rcases h2 with ⟨k, hk⟩
          omega
      have h2 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      have h3 : p ^ f ≠ 3 := by
        intro h3
        exact hadm.2.2.2.2 (by rw [h3])
      rw [hF]
      omega
    have hL2F : CFSG.GH74.GLS.IVK.L2Field F := ⟨hFodd, hF3⟩
    have hKcard : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
      CFSG.GH74.GLS.IVK.ivk_1_2b F hL2F K e
    have : Fact p.Prime := ⟨hp⟩
    have hAut : Nat.card (MulAut K) =
        Nat.card (MulAut (CFSG.GorensteinWalter.PSL2 F)) :=
      Nat.card_congr (MulAut.congr (e.trans (CFSG.GH74.GLS.IVK.L2.equivPSL F))).toEquiv
    rw [hAut, CFSG.RankThree.PartOne.Sec1511.card_aut_psl2_pk hp2 hf hF hF3]
    obtain ⟨m', hm'⟩ : 2 ∣ Nat.card F ^ 2 - 1 := by
      obtain ⟨k, hk⟩ := (hFodd.pow : Odd (Nat.card F ^ 2))
      omega
    have hK' : Nat.card K = Nat.card F * m' := by
      rw [hKcard, hm', ← mul_assoc, mul_comm (Nat.card F) 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    have hpK : p ^ f ∣ Nat.card K := ⟨m', by rw [hK', hF]⟩
    have hpM : p ^ f ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := hpK.trans hdvd
    have hf5 : f ≤ 5 := by
      have h1 := (hp.pow_dvd_iff_le_factorization (by norm_num)).1 hpM
      have h5 := CFSG.OddStandard.Seitz77.factorization_GL8_le_five hp hp2
      omega
    refine ⟨2 * f, ?_, by omega⟩
    rw [hm', hK']
    ring
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)

theorem smallOut_L28 {K : Type} [Group K]
    (h : LieModel K .PSL 2 2 3) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  refine ⟨3, ?_, by norm_num⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L28.equiv_of_lieModel h
  have hK : Nat.card K = 504 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.L28.QP_ok,
      CFSG.GH74.KGroups.L28.QP_valid.2]
  rw [CFSG.GH74.KGroups.L28.card_mulAut h, hK]

theorem smallOut_L216 {K : Type} [Group K]
    (h : LieModel K .PSL 2 2 4) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  refine ⟨4, ?_, by norm_num⟩
  obtain ⟨M, hP, hA⟩ := CFSG.GH74.Uniqueness.SU.K.R4.L216M.autModel h
  have hK : Nat.card K = 4080 := by
    rw [Nat.card_congr M.e.toEquiv, hP,
      CFSG.GH74.KGroups.card_group _ CFSG.GH74.Uniqueness.SU.K.R4.L216M.QP_ok,
      CFSG.GH74.Uniqueness.SU.K.R4.L216M.QP_valid.2]
  rw [M.card_mulAut, hA,
    CFSG.GH74.KGroups.card_group _ CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA_ok,
    CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA_valid.2, hK]

theorem smallOut_L34
    {K : Type} [Group K] (h : LieModel K .PSL 3 2 2) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L34.equiv_of_lieModel h
  refine ⟨12, ?_, by norm_num⟩
  rw [CFSG.GH74.KGroups.L34.card_mulAut e, Nat.card_congr e.toEquiv,
    CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.L34.QP CFSG.GH74.KGroups.L34.QP_ok,
    CFSG.GH74.KGroups.L34.QP_valid.2]

theorem smallOut_U33
    {K : Type} [Group K] (h : LieModel K .PSU 3 3 1) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  refine ⟨2, ?_, by norm_num⟩
  rw [CFSG.GH74.KGroups.U33.card_mulAut e, Nat.card_congr e.toEquiv,
    CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.U33.QP CFSG.GH74.KGroups.U33.QP_ok,
    CFSG.GH74.KGroups.U33.QP_valid.2]

theorem smallOut_U42 {K : Type} [Group K]
    (h : LieModel K .PSp 2 3 1) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43 in
  obtain ⟨e⟩ := equiv_of_lieModel h
  open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43 in
  obtain ⟨M, -, hA⟩ := exists_model e
  have hK : Nat.card K = 25920 := by
    open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43 in
    rw [Nat.card_congr e.toEquiv, card_group QP45 QP45_ok, QP45_valid.2]
  have hAut : Nat.card (MulAut K) = 51840 := by
    open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43 in
    rw [M.card_mulAut, hA, card_group QA45 QA45_ok, QA45_valid.2]
  exact ⟨2, by rw [hK, hAut], by norm_num⟩

theorem smallOut_J2 {K : Type}
    [Group K] (h : NativeSporadic.IsSporadic K .J2) :
    ∃ m : ℕ, Nat.card (MulAut K) = m * Nat.card K ∧ ¬ 60 ∣ m := by
  obtain ⟨e⟩ := h
  have e' : K ≃* NativeSporadic.J2 := e
  have hK : Nat.card K = 604800 := by
    rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.J2.card_J2]
  have hAut : Nat.card (MulAut K) = 1209600 := by
    rw [Nat.card_congr (MulAut.congr e').toEquiv,
      CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.1]
  exact ⟨2, by rw [hK, hAut], by norm_num⟩


section Main


theorem X_le_layer27 {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (c : Local27 N X t) (hcent : centralizer ((layer N : Subgroup N) : Set N) = ⊥)
    (hdvd : Nat.card ↥(layer N) ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127)
    (hS : Survivors27 ↥(layer N)) : X ≤ layer N := by
  have hchar : (layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨m, hm, h60⟩ : SmallOut ↥(layer N) := by
    rcases hS with ⟨n, hn7, hn10, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h | h | h | h | h | h
    · exact smallOut_alt (n := n) (by omega) (by omega) e
    · exact smallOut_L2odd hp hp2 hf h hdvd
    · exact smallOut_L28 h
    · exact smallOut_L216 h
    · exact smallOut_L34 h
    · exact smallOut_U33 h
    · exact smallOut_U42 h
    · exact smallOut_J2 h
  exact le_of_card_aut hcent c.isSimpleGroup_X c.card_eq_sixty hm h60

end Main

end CFSG.OddStandard.Seitz77
