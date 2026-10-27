module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoListGamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoMinimalSimple
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneDickson
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoAltTen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAltTenCase
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3ReeRank
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.ClassicalGroups
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.Bridge.McLSurj
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate9125
public import Certificates.Certificate9212
public import Certificates.Certificate9215
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def KFactTenFourteenTwoA5GammaRest : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) (K₁ J : Subgroup K),
    p.Prime → p ≠ 2 →
    (∃ i : TauCeti.CFSGIndex, RankOneCent.IsTenFourteenOneIndex p i ∧
      (∀ h, i ≠ .alternating 10 h) ∧ (∀ d m, i = .lie d → d.1 ≠ .reeG2 m) ∧
      Nonempty (K ≃* i.Group)) → center K = ⊥ →
    ¬ IsCaseTwoGroup p K → (∀ [Fact p.Prime] (a : ℕ), 2 ≤ a → IsEmpty (K ≃* PSL2GF p a)) →
    (RankOneCent.StepThreeGroup p K → IsEmpty (K ≃* alternatingGroup (Fin 10)) →
      ¬ (IsElemAbelian p (T : Subgroup K) ∧ Nat.card (T : Subgroup K) = p ^ 2)) →
    CFSG.Open.pRank p (T : Subgroup K) ≤ 2 → RankOneCent.narrowGamma p (T : Subgroup K) ≤ K₁ →
    K₁ ≠ ⊤ → IsSubnormal J K₁ → ⁅J, J⁆ = J → J ≠ ⊥ →
    (∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) →
    p = 5 ∧ Nonempty (J ≃* alternatingGroup (Fin 5))

private theorem eq_bot_of_perfect_of_le {X : Type*} [Group X] {J K₁ : Subgroup X} (hJK : J ≤ K₁)
    (hJp : ⁅J, J⁆ = J) (hs : Group.IsSolvable K₁) : J = ⊥ := by
  haveI := hs
  haveI : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJK)
  haveI : Group.IsPerfect J :=
    (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J).mpr hJp
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable J).solvable
  have htop : ∀ k, derivedSeries J k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [derivedSeries_succ, ih]
      exact (inferInstance : Group.IsPerfect J).commutator_eq_top
  rw [htop n] at hn
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : J) ∈ (⊥ : Subgroup J) := hn ▸ mem_top _
  exact (mem_bot.mpr (congrArg Subtype.val (mem_bot.mp this)))

theorem kFactTenFourteenTwoA5Gamma_of_rest
    (hMax : RankOneCent.KFactStepThreeMaximal)
    (hNS : RankOneCent.KFactStepThreeNormSolv) (hR : KFactTenFourteenTwoA5GammaRest) :
    KFactTenFourteenTwoA5Gamma := by
  intro p K _ _ T K₁ J hp hp2 hL hZ hrank hΓ hK₁ hJs hJp hJ1 hJirr
  haveI : Fact p.Prime := ⟨hp⟩
  have hns : ¬ Group.IsSolvable K₁ := fun hs => hJ1 (eq_bot_of_perfect_of_le hJs.le hJp hs)
  by_cases hC2 : IsCaseTwoGroup p K
  · exact (hns (isSolvable_of_ne_top_of_isCaseTwoGroup hC2 K₁ hK₁)).elim
  by_cases hL2 : ∃ a, 2 ≤ a ∧ Nonempty (K ≃* PSL2GF p a)
  · obtain ⟨a, ha, ⟨e⟩⟩ := hL2
    have hes : Function.Surjective e.toMonoidHom := by
      rw [MulEquiv.coe_toMonoidHom]
      exact e.surjective
    have hP := psl2GF_sylow p a (by omega) (T.mapSurjective hes)
    have hTe : IsElemAbelian p ((T : Subgroup K).map e.toMonoidHom) := hP.1
    have hTc : Nat.card ((T : Subgroup K).map e.toMonoidHom) = p ^ a := hP.2
    have hTc' : Nat.card (T : Subgroup K) = p ^ a := by
      rw [← hTc, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    have hTab : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x * y = y * x := by
      intro x hx y hy
      apply e.injective
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hTe.1.is_comm.comm ⟨e x, x, hx, rfl⟩ ⟨e y, y, hy, rfl⟩)
    have hTnc : ¬ IsCyclic (T : Subgroup K) := by
      intro hcyc
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (T : Subgroup K))
      have hgp : (e (g : K)) ^ p = 1 := hTe.2 _ ⟨g, g.2, rfl⟩
      have hgp' : g ^ p = 1 := by
        apply Subtype.ext
        apply e.injective
        rw [Subgroup.coe_pow, map_pow, hgp, OneMemClass.coe_one, map_one]
      have hdvd := orderOf_dvd_of_pow_eq_one hgp'
      rw [hg, hTc'] at hdvd
      have h1 : p ^ a ∣ p ^ 1 := by rwa [pow_one]
      have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
      omega
    obtain ⟨D, hDT, hD, hDc⟩ :=
      GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic hp2 T.isPGroup' hTnc
    have hTK₁ : (T : Subgroup K) ≤ K₁ := by
      intro t ht
      refine hΓ (RankOneCent.normalizer_le_narrowGamma hDT hD hDc
        (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun d hd => ?_)))
      exact hTab d (hDT hd) t ht
    exact (hK₁ (eq_top_of_sylow_le_of_equiv_psl2GF hp2 (by omega) e K₁ T hTK₁ hns)).elim
  by_cases hS3 : RankOneCent.StepThreeGroup p K ∧ IsEmpty (K ≃* alternatingGroup (Fin 10)) ∧
      IsElemAbelian p (T : Subgroup K) ∧ Nat.card (T : Subgroup K) = p ^ 2
  · obtain ⟨hS, hA10, hTe, hTc⟩ := hS3
    have hNK₁ : normalizer ((T : Subgroup K) : Set K) ≤ K₁ :=
      (RankOneCent.normalizer_le_narrowGamma le_rfl hTe hTc).trans hΓ
    have hco := hMax p K hS hA10 T
    have hEq : K₁ = normalizer ((T : Subgroup K) : Set K) := by
      by_contra hne
      exact hK₁ (hco.2 K₁ (lt_of_le_of_ne hNK₁ (Ne.symm hne)))
    have hsol := hNS p K ⊤ T normal_top
      (by rw [coe_top, centralizer_univ, hZ])
      (by
        obtain ⟨i, hi, ⟨e⟩⟩ := hS
        exact ⟨i, hi, ⟨Subgroup.topEquiv.trans e⟩⟩)
      (CFSG.ABGLocalTools.isSylowOf_iff.mpr
        ⟨le_top, T.isPGroup', by rw [relIndex_top_right]; exact T.not_dvd_index⟩)
    exact (hns (hEq ▸ hsol)).elim
  obtain ⟨i, hi, ⟨e⟩⟩ := hL
  by_cases hi10 : ∃ h, i = .alternating 10 h
  · obtain ⟨h, rfl⟩ := hi10
    obtain ⟨-, h6⟩ | ⟨rfl, -⟩ := hi
    · exact absurd h6 (by norm_num)
    have hTe := RankOneCent.sylow_five_altTen e T
    have hNK₁ : normalizer ((T : Subgroup K) : Set K) ≤ K₁ :=
      (RankOneCent.normalizer_le_narrowGamma le_rfl
        ⟨⟨⟨fun a b => Subtype.ext ((hTe a a.2).2 b b.2)⟩⟩, fun x hx => (hTe x hx).1⟩
        (RankOneCent.card_sylow_five_altTen e T)).trans hΓ
    exact ⟨rfl, nonempty_mulEquiv_alt5_of_altTen e T hNK₁ hK₁ hJs.le hJp hJ1 hJirr⟩
  push Not at hi10
  by_cases hRee : ∃ d m, i = .lie d ∧ d.1 = .reeG2 m
  · obtain ⟨d, m, rfl, hdm⟩ := hRee
    have hp3 : p = 3 := by
      rcases hi with ⟨q, -, -, h⟩ | ⟨q, -, h⟩ | ⟨hp3, -⟩ | ⟨-, h | h⟩
      all_goals first | exact hp3 | (rw [hdm] at h; cases h)
    subst hp3
    have hd : IsReeGTwoIndex 3 d := ⟨rfl, m, hdm⟩
    obtain ⟨E, hET, hE, hEc⟩ := kFactReeSylowElemAbelian K d hd ⟨e⟩ T
    have h6 := CFSG.SectionRank.le_pRank (by norm_num) hET hE hEc
    obtain ⟨-, m', hm', -, hfe⟩ := hd.exists_eq
    rw [hfe] at h6
    omega
  push Not at hRee
  exact hR p K T K₁ J hp hp2 ⟨i, hi, fun h => hi10 h, fun d m hd => hRee d m hd, ⟨e⟩⟩ hZ hC2
    (fun a ha => ⟨fun e => hL2 ⟨a, ha, ⟨e⟩⟩⟩) (fun h1 h2 h3 => hS3 ⟨h1, h2, h3⟩) hrank hΓ hK₁
    hJs hJp hJ1 hJirr

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
