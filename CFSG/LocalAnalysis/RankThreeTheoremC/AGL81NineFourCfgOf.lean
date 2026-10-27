module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeSevenFiveHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.IsoPlaneMain
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneCentralizer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeCfgHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeComponents
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.LocalAnalysis.GLTheoremA.S8.Close

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

namespace NineFour

theorem exists_central_of_one_le_pRank {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (R : Sylow p X) {N : Subgroup X} [N.Normal] (h : 1 ≤ Open.pRank p N) :
    ∃ z ∈ (R : Subgroup X) ⊓ N, orderOf z = p ∧ ∀ g ∈ (R : Subgroup X), g * z = z * g := by
  refine RankFourTheoremC.Nongeneration.exists_central_orderOf R fun hbot => ?_
  obtain ⟨E, hEN, -, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := p) (k := 1) (H := N) h
  have hpN : p ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hEN
    rwa [hEc, pow_one] at this
  apply Sylow.ne_bot_of_dvd_card (CFSG.QuasiDihedralFusion.sylowInfNormal R N) hpN
  rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_eq_bot, disjoint_iff]
  exact hbot

theorem le_glbCore_one_of_central {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {R E K : Subgroup X} (hER : E ≤ R) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (h3 : ¬ 3 ≤ Open.pRank p R) {z : X} (hzR : z ∈ R)
    (hzK : z ∈ Subgroup.centralizer (K : Set X)) (hzp : orderOf z = p)
    (hzc : ∀ g ∈ R, g * z = z * g) : K ≤ GLBCore p 1 E := by
  have hzpow : z ^ p = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzE : z ∈ E := by
    by_contra hzE
    obtain ⟨hA, hAc⟩ := CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hE hEc hzpow hzE
      fun e he => hzc e (hER he)
    have := CFSG.SectionRank.le_pRank hp.one_lt (sup_le hER (Subgroup.zpowers_le.2 hzR)) hA hAc
    omega
  have hrank : 1 ≤ Open.pRank p (Subgroup.zpowers z) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl (CFSG.Open.isElemAbelian_zpowers hzpow)
      (by rw [Nat.card_zpowers, hzp, pow_one])
  have hN : Subgroup.normalizer ((Subgroup.zpowers z : Subgroup X) : Set X) ≤ GLBCore p 1 E :=
    le_sSup ⟨Subgroup.zpowers z, Subgroup.zpowers_le.2 hzE, hrank, rfl⟩
  intro x hx
  refine hN (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_))
  rintro y ⟨n, rfl⟩
  exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.1 hzK x hx).symm n).eq

theorem false_of_two_components {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {R X₀ L₀ L₁ : Subgroup X}
    (hC : ∀ A : Subgroup X, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ Open.pRank p (R ⊓ Subgroup.centralizer (A : Set X)) →
      Subgroup.centralizer (A : Set X) ≤ X₀)
    (hL₀ : IsComponentOf L₀ ⊤) (hL₁ : IsComponentOf L₁ ⊤) (hne : L₀ ≠ L₁) (hL₀X : ¬ L₀ ≤ X₀)
    {u₀ : X} (hu₀R : u₀ ∈ R) (hu₀L : u₀ ∈ L₀) (hu₀p : orderOf u₀ = p)
    (hu₀c : u₀ ∉ Subgroup.centralizer (L₀ : Set X))
    {u : X} (huR : u ∈ R) (huL : u ∈ L₁) (hup : orderOf u = p)
    (huc : u ∉ Subgroup.centralizer (L₁ : Set X))
    {z : X} (hzR : z ∈ R) (hz₀ : z ∈ Subgroup.centralizer (L₀ : Set X))
    (hz₁ : z ∈ Subgroup.centralizer (L₁ : Set X)) (hzp : orderOf z = p) : False := by
  have hS7 := pRank_inf_centralizer_component_le_one hp hC hL₀X hu₀R hu₀L hu₀p (by
    by_contra hall
    push Not at hall
    exact hu₀c (Subgroup.mem_centralizer_iff.mpr fun c hc => (hall c hc).symm))
  have huz : u ∉ Subgroup.zpowers z := fun h => huc (Subgroup.zpowers_le.2 hz₁ h)
  have hab : u ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup X) : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨n, rfl⟩ := hy
      exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.mp hz₁ u huL).symm n).eq
  have h2 := CFSG.AGLEmbeddingD2.two_le_pRank_of_commute (H := R ⊓ Subgroup.centralizer
    (L₀ : Set X)) hp hzp hup hab huz ⟨hzR, hz₀⟩
    ⟨huR, le_centralizer_of_component_ne hL₁ hL₀ (Ne.symm hne) huL⟩
  omega

variable {G : Type} [Group G] [Finite G]

theorem exists_nineFourIndex_of_isSmallStrongP
    (hS : Setting G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {N : Subgroup G} {L : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hLs : IsSimpleGroup L)
    (h : IsSmallStrongP p L) :
    ∃ i : TauCeti.CFSGIndex, IsNineFourIndex p i ∧ Nonempty (L ≃* i.Group) := by
  rcases h with ⟨d, ⟨q, hq, hqp, hqe⟩, ⟨e⟩⟩ | ⟨d, ⟨q, hqp, -, hq⟩, ⟨e⟩⟩ | ⟨e⟩ | ⟨hp3, h⟩ |
    ⟨hp5, h⟩ | ⟨hp11, e⟩
  · exact ⟨.lie d, Or.inl ⟨q, hqp, by omega, hq⟩, ⟨e⟩⟩
  · exact ⟨.lie d, Or.inr (Or.inl ⟨q, hqp, hq⟩), ⟨e⟩⟩
  · have h5 : 5 ≤ 2 * p := by have := hp.two_le; omega
    by_cases hp7 : 7 ≤ p
    · exact (false_of_sevenFive hS kFactSevenFive_holds (Or.inl ⟨hp7, h5, rfl⟩) hLs e).elim
    have hp35 : p = 3 ∨ p = 5 := by
      have := hp.two_le
      interval_cases p <;> first | (left; rfl) | (right; rfl) | exact absurd rfl hp2 |
        exact absurd hp (by norm_num)
    refine ⟨.alternating (2 * p) h5, ?_, e⟩
    rcases hp35 with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rcases h with ⟨d, ⟨q, hq2, hqe, hq⟩, ⟨e⟩⟩ | e
    · exact ⟨.lie d, Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, Or.inr ⟨q, hq2, hqe, hq⟩⟩))), ⟨e⟩⟩
    · exact ⟨.sporadic .M11, Or.inl ⟨hp3, rfl⟩, e⟩
  · rcases h with ⟨d, hd, ⟨e⟩⟩ | e | e
    · exact ⟨.lie d, Or.inr (Or.inr (Or.inr (Or.inr ⟨hp5, Or.inr hd⟩))), ⟨e⟩⟩
    · exact ⟨.sporadic .McL, Or.inr (Or.inl ⟨hp5, rfl⟩), e⟩
    · exact (false_of_sevenFive hS kFactSevenFive_holds (Or.inr (Or.inr ⟨hp5, rfl⟩)) hLs e).elim
  · exact ⟨.sporadic .J4, Or.inr (Or.inr ⟨hp11, rfl⟩), e⟩

theorem exists_nineFourIndex_of_oneLie {p : ℕ} {K : Type} [Group K]
    (h : ∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨ (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
        IsReeGTwoIndex p d) ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ i : TauCeti.CFSGIndex, IsNineFourIndex p i ∧ Nonempty (K ≃* i.Group) := by
  obtain ⟨d, ⟨n, hn, q, hq, hqp, hqe⟩ | ⟨⟨q, hqp, hq⟩, -⟩ | hd, ⟨e⟩⟩ := h
  · exact ⟨.lie d, Or.inl ⟨q, hqp, by omega, hq⟩, ⟨e⟩⟩
  · exact ⟨.lie d, Or.inr (Or.inl ⟨q, hqp, hq⟩), ⟨e⟩⟩
  · exact ⟨.lie d, Or.inr (Or.inr (Or.inl hd)), ⟨e⟩⟩

end NineFour

variable {G : Type} [Group G] [Finite G]

section Cert


open NineFour in
theorem agl81NineFourCfg_holds
    : AGL81NineFourCfg G := by
  intro hS p P M H Q K hd _ h2 h1
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hp := he.prime
  have hp2 := he.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := H) p
  set π := QuotientGroup.mk' O
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hk := hd.kbar
  have hne : d1KBar p M H ≠ ⊥ := fun h => hd.not_le_X0 (by rw [hk, h]; exact bot_le)
  haveI : K.Normal := agl81NineThreeNormalCfg_holds hS p P M H Q K hd
  obtain ⟨R, hQR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hd.base hd.le_H
  set Rb : Sylow p (H ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (H ⧸ O)) = (R.subgroupOf H).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  have e1 : Open.pRank p (d1PlusCore p H K) =
      Open.pRank p (Subgroup.centralizer (K : Set (H ⧸ O))) := by
    unfold d1PlusCore
    rw [← pRank_map_mk_eq_pRank_map_subtype hp O hO,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
  rw [e1] at h1
  obtain ⟨z, ⟨hzR, hzC⟩, hzp, hzc⟩ :=
    exists_central_of_one_le_pRank Rb (N := Subgroup.centralizer (K : Set (H ⧸ O))) h1.ge
  obtain ⟨E, hER, hE, hEcard, hcore⟩ := cores_le_d1X0 he hd.base hQR hRM hR
  rw [← hRbeq] at hER hcore
  by_cases h3 : 3 ≤ Open.pRank p (Rb : Subgroup (H ⧸ O))
  swap
  · rw [if_neg h3] at hcore
    exact (hd.not_le_X0
      ((le_glbCore_one_of_central hp hER hE hEcard h3 hzR hzC hzp hzc).trans hcore)).elim
  rw [if_pos h3] at hcore
  have hnotW : ¬ K ≤ GLBWeakCore p (Rb : Subgroup (H ⧸ O)) := fun h =>
    hd.not_le_X0 (h.trans hcore)
  obtain ⟨L₀, hL₀, hL₀X, hK₀ | ⟨L₁, hL₁, hL₁X, hne01, hK01, -, -⟩⟩ :=
    d1KBar_eq_or_eq_sup_of_escape he hd.base hd.le_H hne
  swap
  · exfalso
    rw [← hk] at hK01
    have hCA : ∀ A : Subgroup (H ⧸ O), A ≤ Rb → IsElemAbelian p A → Nat.card A = p ^ 2 →
        3 ≤ Open.pRank p ((Rb : Subgroup (H ⧸ O)) ⊓ Subgroup.centralizer (A : Set (H ⧸ O))) →
        Subgroup.centralizer (A : Set (H ⧸ O)) ≤ d1X0 p M H := by
      rw [hRbeq]
      exact fun A hA hAe hAc h3 =>
        centralizer_le_d1X0_of_escape he hR.le hRM hR.isPGroup A hA hAe hAc h3
    obtain ⟨u₀, ⟨hu₀R, hu₀L⟩, hu₀p, hu₀c⟩ := exists_mem_sylow_inf_component hp hp2
      (primeComplementCore_quotient_eq_bot p) Rb hL₀
    obtain ⟨u, ⟨huR, huL⟩, hup, huc⟩ := exists_mem_sylow_inf_component hp hp2
      (primeComplementCore_quotient_eq_bot p) Rb hL₁
    have hL₀K : L₀ ≤ K := by rw [hK01]; exact le_sup_left
    have hL₁K : L₁ ≤ K := by rw [hK01]; exact le_sup_right
    exact false_of_two_components hp hCA hL₀ hL₁ hne01 hL₀X hu₀R hu₀L hu₀p hu₀c huR huL hup huc
      hzR (Subgroup.centralizer_le hL₀K hzC) (Subgroup.centralizer_le hL₁K hzC) hzp
  rw [← hk] at hK₀
  rw [← hK₀] at hL₀ hL₀X
  have hHtop : H ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hS.simple hS.nonab hd.maxH.1
  have hX : CatalogSimpleSections (H ⧸ O) :=
    (catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient _
  have hpc : CFSG.pCore p K = ⊥ :=
    _root_.GL83.I243.gl83ComponentPCoreTrivial_holds (H ⧸ O) hX p Rb K hp hp2 h3 hL₀ hnotW
  have hcoreK : primeComplementCore (G := K) p = ⊥ :=
    primeComplementCore_component_eq_bot (primeComplementCore_quotient_eq_bot p) hL₀
  have hZ : Subgroup.center K = ⊥ := by
    have hZp : IsPGroup p (Subgroup.center K) :=
      normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot p hp hcoreK _ inferInstance
        inferInstance
    have hle : Subgroup.center K ≤ CFSG.pCore p K := le_sSup ⟨inferInstance, hZp⟩
    rw [hpc] at hle
    exact le_bot_iff.1 hle
  have hzK : z ∉ K := fun hz => by
    have hmem : (⟨z, hz⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC g g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    have hz1 : z = 1 := congrArg Subtype.val hmem
    rw [hz1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hL₀.2.2.2
  let e₀ : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hs : IsSimpleGroup K := e₀.symm.isSimpleGroup
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hL₀.2.2
    exact ⟨e₀ a, e₀ b, fun h => hab (e₀.injective (by rw [map_mul, map_mul, h]))⟩
  have hcatK : IsCatalogGroup K := hX.simple_subgroup K hs hnonab
  set T := CFSG.QuasiDihedralFusion.sylowInfNormal Rb K
  have hTP : (T : Subgroup K).map K.subtype ≤ (Rb : Subgroup (H ⧸ O)) := by
    rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have h2' : 2 ≤ Open.pRank p (⊤ : Subgroup K) := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have hT2 : 2 ≤ Open.pRank p (T : Subgroup K) := by
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp T]
    exact h2'
  have hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤ := fun hΓ =>
    hnotW (ThreeOne.le_weakCore_of_gammaOne hp hzR hzC hzK hzp T hTP hT2 hΓ)
  have hTnc := RankFourTheoremC.Nongeneration.not_isCyclic_sylow_of_two_le_pRank h2' T
  refine ⟨hs, ?_⟩
  by_cases hle : Open.pRank p (⊤ : Subgroup K) ≤ 2
  · exact exists_nineFourIndex_of_isSmallStrongP hS hp hp2 hs
      (UniquenessCase.UCK.kFactSmallIdent_holds _ hs hnonab hcatK p hp hp2 T hTnc hΓ
        ((RankFourTheoremC.Nongeneration.pRank_top_subgroup_top hp).trans_le hle))
  · exact exists_nineFourIndex_of_oneLie (UniquenessCase.UCK.kFactOneLieIdent_holds _ hs hnonab
      hcatK p hp hp2 T hTnc hΓ fun h => hle ((CFSG.SectionRank.pRank_top_le_of_injective
        hp.one_lt _ (RankFourTheoremC.Nongeneration.conj_injective_of_center_eq_bot hZ)).trans h))

end Cert

end CFSG.LocalAnalysis.RankThreeTheoremC
