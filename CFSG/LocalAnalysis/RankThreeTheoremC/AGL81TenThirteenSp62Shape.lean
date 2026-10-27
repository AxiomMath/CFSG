module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSp62Local
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenReduce
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62RankDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseBlock
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

section HBar

variable {P : Sylow 3 G} {M H Q : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem sp62_normal (hd : AGL81CfgData 3 P M H Q K) : K.Normal := by
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hne : d1KBar 3 M H ≠ ⊥ := fun h => hd.not_le_X0 (by rw [hd.kbar, h]; exact bot_le)
  rw [hd.kbar]
  exact d1KBar_normal_of_escape he hd.base hd.le_H hne

theorem sp62_pRank_top_le (hS : Setting G) (hd : AGL81CfgData 3 P M H Q K) :
    Open.pRank 3 (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ 3 := by
  have h1 := pRank_map_mk_eq_pRank_map_subtype Nat.prime_three
    (primeComplementCore (G := H) 3) (primeComplementCore_coprime 3) (⊤ : Subgroup H)
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), Subgroup.map_top,
    Subgroup.range_subtype] at h1
  rw [h1]
  exact pRank_le_three_of_twoLocal hS hd.maxH.1

theorem sp62_centralizer_eq_bot (hLoc : KFactSp62CfgLocal) (hS : Setting G)
    (hd : AGL81CfgData 3 P M H Q K) {d : TauCeti.ValidLieTypeIndex} (hdK : IsSpSixTwoIndex d)
    (eK : Nonempty (K ≃* CatGroup d)) :
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥ := by
  haveI := sp62_normal hd
  obtain ⟨⟨E, hEK, hE, hEc⟩, hZ, -⟩ := hLoc _ K d hdK inferInstance eK
  set O := primeComplementCore (G := H) 3 with hO
  set C := Subgroup.centralizer (K : Set (H ⧸ O)) with hCdef
  have hC3 : Nat.Coprime 3 (Nat.card C) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hc' : orderOf (c : H ⧸ O) = 3 := by rw [Subgroup.orderOf_coe]; exact hc
    have hcE : (c : H ⧸ O) ∉ E := fun hcE => by
      have hmem : (c : H ⧸ O) ∈ K ⊓ C := ⟨hEK hcE, c.2⟩
      rw [hZ, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hc'
      norm_num at hc'
    have hcomm : ∀ e ∈ E, Commute e (c : H ⧸ O) := fun e he =>
      Subgroup.mem_centralizer_iff.mp c.2 e (hEK he)
    obtain ⟨hE', hcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE hc' hcomm hcE
    have h4 : 4 ≤ Open.pRank 3 (⊤ : Subgroup (H ⧸ O)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hE' (by rw [hcard, hEc]; norm_num)
    have h3 := sp62_pRank_top_le hS hd
    omega
  have hle := normal_coprime_le_primeComplementCore 3 C (Subgroup.normal_centralizer) hC3
  rw [primeComplementCore_quotient_eq_bot] at hle
  exact le_bot_iff.mp hle

theorem sp62_top_and_card (hLoc : KFactSp62CfgLocal) (hS : Setting G)
    (hd : AGL81CfgData 3 P M H Q K) {d : TauCeti.ValidLieTypeIndex} (hdK : IsSpSixTwoIndex d)
    (eK : Nonempty (K ≃* CatGroup d)) :
    K = ⊤ ∧ Nat.card (H ⧸ primeComplementCore (G := H) 3) = 1451520 := by
  haveI := sp62_normal hd
  have hC := sp62_centralizer_eq_bot hLoc hS hd hdK eK
  have hKtop := ((hLoc _ K d hdK inferInstance eK).2.2 hC).1
  refine ⟨hKtop, ?_⟩
  obtain ⟨q, hqp, hqe, hdq⟩ := hdK
  obtain ⟨e⟩ := eK
  rw [← Subgroup.card_top (G := H ⧸ primeComplementCore (G := H) 3), ← hKtop,
    Nat.card_congr e.toEquiv, card_catGroup_B_even (le_refl 3) hqp hdq, hqe]
  unfold ordBC
  decide

theorem sp62_not_dvd_card (hLoc : KFactSp62CfgLocal) (hS : Setting G)
    (hd : AGL81CfgData 3 P M H Q K) {d : TauCeti.ValidLieTypeIndex} (hdK : IsSpSixTwoIndex d)
    (eK : Nonempty (K ≃* CatGroup d)) : ¬ 3 ^ 5 ∣ Nat.card H := by
  have hcard := (sp62_top_and_card hLoc hS hd hdK eK).2
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (primeComplementCore (G := H) 3)
  rw [hcard] at hmul
  have hcop := primeComplementCore_coprime (G := H) 3
  intro h5
  have h5' : 3 ^ 5 ∣ 1451520 * Nat.card (primeComplementCore (G := H) 3) := hmul ▸ h5
  have h5'' : 3 ^ 5 ∣ 1451520 :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 5 hcop) h5')
  norm_num at h5''

end HBar

section Image

theorem sp62_commutator_le_of_relIndex_le_two {X : Type*} [Group X] [Finite X] {N A : Subgroup X}
    (hNA : N ≤ A) (hAN : A ≤ normalizer (N : Set X)) (h2 : N.relIndex A ≤ 2) : ⁅A, A⁆ ≤ N := by
  haveI : (N.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  have hcard : Nat.card (↥A ⧸ N.subgroupOf A) = N.relIndex A := (Subgroup.index_eq_card _).symm
  have hpos : 0 < Nat.card (↥A ⧸ N.subgroupOf A) := Nat.card_pos
  have hcomm : IsMulCommutative (↥A ⧸ N.subgroupOf A) := by
    refine IsMulCommutative.of_comm fun a b => Commute.of_orderOf_dvd_two (fun g => ?_) a b
    have h1 : orderOf g ∣ Nat.card (↥A ⧸ N.subgroupOf A) := orderOf_dvd_natCard g
    rcases (show Nat.card (↥A ⧸ N.subgroupOf A) = 1 ∨ Nat.card (↥A ⧸ N.subgroupOf A) = 2 by
      omega) with h | h
    · rw [h] at h1
      exact h1.trans (one_dvd 2)
    · rwa [h] at h1
  have hle : _root_.commutator ↥A ≤ N.subgroupOf A :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hcomm
  have hmap := Subgroup.map_mono (f := A.subtype) hle
  have h3 : (_root_.commutator ↥A).map A.subtype = ⁅A, A⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rwa [h3, Subgroup.map_subgroupOf_eq_of_le hNA] at hmap

theorem sp62_eq_of_perfect {X : Type} [Group X] [Finite X] {T Y₀ V₀ I : Subgroup X}
    (hV : Sp62InSitu T Y₀ V₀) (hIY : I ≤ Y₀) (hIp : ⁅I, I⁆ = I) (h25 : 25920 ∣ Nat.card I) :
    I = V₀ := by
  have hcomm : ⁅Y₀, Y₀⁆ ≤ V₀ :=
    sp62_commutator_le_of_relIndex_le_two hV.V_le hV.V_normal hV.V_index
  have hle : I ≤ V₀ := hIp ▸ (Subgroup.commutator_mono hIY hIY).trans hcomm
  obtain ⟨d, ψ, hd, hψ⟩ := hV.V_iso
  have hV25 : Nat.card V₀ = 25920 := by
    rw [Nat.card_congr (Equiv.ofBijective ψ hψ), (LeviBlock.catGroup_u42_facts hd).1]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hV25]
  exact Nat.le_of_dvd Nat.card_pos h25

variable {P : Sylow 3 G} {M H Q : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem sp62_card_dvd_image
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥)
    {I₀ : Subgroup G} (hI₀H : I₀ ≤ H) {T : Type*} [Group T] (f : ↥I₀ →* T)
    (hf : Function.Surjective f) (hker : (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker) :
    Nat.card T ∣
      Nat.card ((I₀.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))) := by
  set φ := (QuotientGroup.mk' (primeComplementCore (G := H) 3)).comp (Subgroup.inclusion hI₀H)
    with hφ
  have hφker : φ.ker = (d1PlusCore 3 H K).subgroupOf I₀ := by
    rw [← MonoidHom.comap_bot, ← hC]
    exact comap_centralizer_eq_subgroupOf (K := K) hI₀H
  rw [← CFSG.AGLEmbeddingD2.range_mk_comp_inclusion hI₀H, ← Subgroup.index_ker]
  have h1 : Nat.card T = f.ker.index := by
    rw [Subgroup.index_ker, (MonoidHom.range_eq_top).mpr hf, Subgroup.card_top]
  rw [h1]
  exact Subgroup.index_dvd_of_le (hφker ▸ hker)

theorem sp62_inSitu (hLoc : KFactSp62CfgLocal) (hS : Setting G)
    (hd : AGL81CfgData 3 P M H Q K) {d : TauCeti.ValidLieTypeIndex} (hdK : IsSpSixTwoIndex d)
    (eK : Nonempty (K ≃* CatGroup d)) (h25 : 25920 ≤ Nat.card (d1X0 3 M H)) :
    ∃ (R : Subgroup G) (Rb : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      Q ≤ R ∧ R ≤ M ∧ CFSG.Quasithin.IsSylowIn 3 R H ∧
      (Rb : Subgroup (H ⧸ primeComplementCore (G := H) 3)) =
        (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ∧
      Sp62InSitu (Rb : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (d1X0 3 M H) V₀ := by
  haveI := sp62_normal hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := primeComplementCore (G := H) 3 with hO
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  obtain ⟨R, hQR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hd.base hd.le_H
  set Rb : Sylow 3 (H ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (H ⧸ O)) = (R.subgroupOf H).map (QuotientGroup.mk' O) := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  obtain ⟨E, hER, hEab, hEcard, hcore⟩ := cores_le_d1X0 he hd.base hQR hRM hR
  have hrank : 3 ≤ Open.pRank 3 ((R.subgroupOf H).map (QuotientGroup.mk' O)) := by
    obtain ⟨E', hE'K, hE', hE'c⟩ := (hLoc _ K d hdK inferInstance eK).1
    have hE'p : IsPGroup 3 E' := IsPGroup.of_card hE'c
    obtain ⟨S, hES⟩ := hE'p.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (H ⧸ O) S Rb
    have hle : E'.map (MulAut.conj g).toMonoidHom ≤ (Rb : Subgroup (H ⧸ O)) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact Subgroup.map_mono hES
    rw [← hRbeq]
    refine CFSG.SectionRank.le_pRank (by norm_num) hle
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE' _) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE'c]
  rw [if_pos hrank] at hcore
  have hC := sp62_centralizer_eq_bot hLoc hS hd hdK eK
  have hKtop := (sp62_top_and_card hLoc hS hd hdK eK).1
  have hne : d1X0 3 M H ≠ ⊤ := fun h => hd.not_le_X0 (by rw [h]; exact le_top)
  obtain ⟨V₀, hV⟩ := ((hLoc _ K d hdK inferInstance eK).2.2 hC).2 Rb (d1X0 3 M H)
    (hRbeq ▸ hcore) hne h25
  exact ⟨R, Rb, V₀, hQR, hRM, hR, hRbeq, hV⟩

end Image

section Sylow

variable {P : Sylow 3 G} {M H Q : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem sp62_sylow_lift (hLoc : KFactSp62CfgLocal) (hS : Setting G)
    (hd : AGL81CfgData 3 P M H Q K) {d : TauCeti.ValidLieTypeIndex} (hdK : IsSpSixTwoIndex d)
    (eK : Nonempty (K ≃* CatGroup d)) {I₀ : Subgroup G} (hI₀H : I₀ ≤ H)
    (h81 : 3 ^ 4 ∣
      Nat.card ((I₀.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))) :
    ∃ R₀ J : Subgroup G, R₀ ≤ I₀ ∧ IsPGroup 3 R₀ ∧ Nat.card R₀ = 3 ^ 4 ∧ J ≤ R₀ ∧
      IsElemAbelian 3 J ∧ Nat.card J = 3 ^ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := sp62_normal hd
  set O := primeComplementCore (G := H) 3 with hO
  have hcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  have hH5 := sp62_not_dvd_card hLoc hS hd hdK eK
  have hHb := (sp62_top_and_card hLoc hS hd hdK eK).2
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥I₀))
  set R₀ := (S : Subgroup ↥I₀).map I₀.subtype with hR₀
  have hR₀I : R₀ ≤ I₀ := Subgroup.map_subtype_le _
  have hR₀H : R₀ ≤ H := hR₀I.trans hI₀H
  have hR₀p : IsPGroup 3 R₀ := S.isPGroup'.map _
  have hcardR₀S : Nat.card R₀ = Nat.card (S : Subgroup ↥I₀) :=
    Subgroup.card_map_of_injective I₀.subtype_injective
  have hI81 : 3 ^ 4 ∣ Nat.card I₀ := by
    refine h81.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI₀H).toEquiv]
  have hS81 : 3 ^ 4 ∣ Nat.card (S : Subgroup ↥I₀) := S.pow_dvd_card_of_pow_dvd_card hI81
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR₀p
  have hcardR₀ : Nat.card R₀ = 3 ^ 4 := by
    have h4 : 4 ≤ k := by
      rw [← hcardR₀S, hk] at hS81
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hS81
    have h5 : k < 5 := by
      by_contra hk5
      push Not at hk5
      exact hH5 ((Nat.pow_dvd_pow 3 hk5).trans (hk ▸ Subgroup.card_dvd_of_le hR₀H))
    rw [hk, show k = 4 by omega]
  set Rb := (R₀.subgroupOf H).map (QuotientGroup.mk' O) with hRb
  have hR₀Hp : IsPGroup 3 (R₀.subgroupOf H) := hR₀p.comap_subtype
  have hRbcard : Nat.card Rb = 3 ^ 4 := by
    rw [hRb, card_map_mk_of_isPGroup Nat.prime_three O hcop hR₀Hp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀H).toEquiv, hcardR₀]
  have hRbp : IsPGroup 3 Rb := hR₀Hp.map _
  obtain ⟨S₂, hRbS₂⟩ := hRbp.exists_le_sylow
  have hS₂ : (S₂ : Subgroup (H ⧸ O)) = Rb := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp S₂.isPGroup'
    have hm5 : m < 5 := by
      by_contra hm5
      push Not at hm5
      have h1 : 3 ^ 5 ∣ Nat.card (H ⧸ O) :=
        (Nat.pow_dvd_pow 3 hm5).trans (hm ▸ Subgroup.card_subgroup_dvd_card _)
      rw [hHb] at h1
      norm_num at h1
    refine (Subgroup.eq_of_le_of_card_ge hRbS₂ ?_).symm
    rw [hm, hRbcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨E, hEK, hE, hEc⟩ := (hLoc _ K d hdK inferInstance eK).1
  have hEp : IsPGroup 3 E := IsPGroup.of_card hEc
  obtain ⟨S₁, hES₁⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (H ⧸ O) S₁ S₂
  have hEg : E.map (MulAut.conj g).toMonoidHom ≤ (R₀.subgroupOf H).map (QuotientGroup.mk' O) := by
    rw [← hRb, ← hS₂, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hES₁
  obtain ⟨J, -, hJR, -, -, ψ, -⟩ :=
    exists_lift_of_le_map Nat.prime_three hR₀H hR₀p O hcop hEg
  refine ⟨R₀, J, hR₀I, hR₀p, hcardR₀, hJR, isElemAbelian_of_mulEquiv ψ
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _), ?_⟩
  rw [Nat.card_congr ψ.toEquiv, Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]

end Sylow

section Block

variable {P : Sylow 3 G} {M H Q : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem sp62_omegaEight (hLoc : KFactSp62CfgLocal) (hLevi : KFactBlockLeviU42)
    (hU : KFactU62ThreeRank) (hΩ : KFactOmegaMinusThreeRank) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h98 : AGL81NineEightFour G) (hS : Setting G)
    (hd : AGL81CfgData 3 P M H Q K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {I₀ : Subgroup G} (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hI₀c : IsTwoPrimeComponent I₀ I₀)
    (hN : H ⊓ L ≤ normalizer (I₀ : Set G)) {dK dJ : TauCeti.ValidLieTypeIndex}
    (hdK : IsSpSixTwoIndex dK) (hdJ : IsUFourTwoIndex dJ) (eK : Nonempty (K ≃* CatGroup dK))
    (f : ↥I₀ →* CatGroup dJ) (hf : Function.Surjective f)
    (hker : (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker) :
    (∃ d4 : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d4 ∧
      Nonempty (barM M L ≃* CatGroup d4)) ∧ ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := primeComplementCore (G := H) 3 with hO
  set π := QuotientGroup.mk' O with hπ
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hMloc : IsTwoLocal M := he.maxTwoLocal_M.1
  have hLM : IsSubnormal L M := hL.subnormal
  have hI₀M : I₀ ≤ H ⊓ M := le_inf_of_cZero hLM hI₀
  have hI₀HL : I₀ ≤ H ⊓ L := hI₀.le
  have hI₀H : I₀ ≤ H := hI₀M.trans inf_le_left
  have hC := sp62_centralizer_eq_bot hLoc hS hd hdK eK
  have hH5 := sp62_not_dvd_card hLoc hS hd hdK eK
  have h25 : 25920 ∣ Nat.card ((I₀.subgroupOf H).map π) := by
    have h := sp62_card_dvd_image hC hI₀H f hf hker
    rwa [(LeviBlock.catGroup_u42_facts hdJ).1] at h
  have hIX : (I₀.subgroupOf H).map π ≤ d1X0 3 M H := map_mk_le_d1X0 hI₀M
  have h25' : 25920 ≤ Nat.card (d1X0 3 M H) :=
    le_trans (Nat.le_of_dvd Nat.card_pos h25) (Subgroup.card_le_of_le hIX)
  obtain ⟨R, Rb, V₀, -, -, -, -, hV⟩ := sp62_inSitu hLoc hS hd hdK eK h25'
  have hperf : ⁅I₀, I₀⁆ = I₀ := hI₀c.perfect
  have hAperf : ⁅I₀.subgroupOf H, I₀.subgroupOf H⁆ = I₀.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hI₀H, hperf]
  have hIperf : ⁅(I₀.subgroupOf H).map π, (I₀.subgroupOf H).map π⁆ = (I₀.subgroupOf H).map π := by
    rw [← Subgroup.map_commutator, hAperf]
  have hIV : (I₀.subgroupOf H).map π = V₀ := sp62_eq_of_perfect hV hIX hIperf h25
  have hpiece : U42Piece (H ⊓ M) (GLBPrimeCore 3 H) I₀ := u42Piece_of_map_eq hV hI₀M hperf hIV
  obtain ⟨-, -, -, hKVN, hidx, ⟨d', ψ, hd', hψ, hker'⟩, -, hcent8⟩ := hpiece
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := (hd.nineEightFour' hS h98).2.1
  set N := GLBPrimeCore 3 H with hNdef
  set Pi := H ⊓ L with hPi
  have hPL : blockParabolic M (pCoreOf 2 H) L = barM M Pi := by
    show barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L) = barM M (H ⊓ L)
    rw [hNH]
  have hPiH : Pi ≤ H := inf_le_left
  have hPiM : Pi ≤ M := inf_le_right.trans hL.le
  have hPiK : Pi ≤ H ⊓ M := le_inf hPiH hPiM
  have hI₀Pi : I₀ ≤ Pi := hI₀HL
  have hPLnorm : ∀ Y : Subgroup G, (∀ x ∈ Pi, x ∈ normalizer (Y : Set G)) →
      barM M Pi ≤ normalizer (barM M Y : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Y hY
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    exact mem_normalizer_barM hxM (hY x (Subgroup.mem_subgroupOf.mp hx))
  have hPiNPi : ∀ x ∈ Pi, x ∈ normalizer ((Pi ⊓ N : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      le_normalizer_glbPrimeCore 3 H (hPiH hx)⟩
  have hPiNV : ∀ x ∈ Pi, x ∈ normalizer ((Pi ⊓ (I₀ ⊔ N) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      hKVN (hPiK hx)⟩
  have hrel : (barM M I₀ ⊔ barM M (Pi ⊓ N)).relIndex (barM M Pi) ≤ 2 := by
    rw [barM_sup_eq hI₀Pi hPiH hPiM]
    have hdv : (barM M (Pi ⊓ (I₀ ⊔ N))).relIndex (barM M Pi) ∣ (I₀ ⊔ N).relIndex Pi := by
      have h1 := relIndex_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
        (Subgroup.comap_mono (inf_le_left : Pi ⊓ (I₀ ⊔ N) ≤ Pi) :
          (Pi ⊓ (I₀ ⊔ N)).subgroupOf M ≤ Pi.subgroupOf M)
      have h2 : ((Pi ⊓ (I₀ ⊔ N)).subgroupOf M).relIndex (Pi.subgroupOf M) =
          (I₀ ⊔ N).relIndex Pi := by
        rw [Subgroup.relIndex_subgroupOf hPiM, Subgroup.inf_relIndex_left]
      rw [← h2]
      exact h1
    have hne1 : (I₀ ⊔ N).relIndex Pi ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    have hne2 : (I₀ ⊔ N).relIndex (H ⊓ M) ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    calc _ ≤ (I₀ ⊔ N).relIndex Pi := Nat.le_of_dvd (Nat.pos_of_ne_zero hne1) hdv
      _ ≤ (I₀ ⊔ N).relIndex (H ⊓ M) := Subgroup.relIndex_le_of_le_right hPiK hne2
      _ ≤ 2 := hidx
  have h81I : 3 ^ 4 ∣ Nat.card ((I₀.subgroupOf H).map π) :=
    (show 3 ^ 4 ∣ 25920 by norm_num).trans h25
  obtain ⟨R₀, J₀, hR₀I, hR₀p, hR₀c, hJR, hJe, hJc⟩ :=
    sp62_sylow_lift hLoc hS hd hdK eK hI₀H h81I
  have hR₀M : R₀ ≤ M := hR₀I.trans (hI₀M.trans inf_le_right)
  have hJM : J₀ ≤ M := hJR.trans hR₀M
  have hOcop2 := sp62Close_coprime_pCore_two M
  have hQ : ∀ Q' : Sylow 3 ↥(blockParabolic M (pCoreOf 2 H) L),
      Nat.card (Q' : Subgroup ↥(blockParabolic M (pCoreOf 2 H) L)) = 3 ^ 4 := by
    intro Q'
    have hbR : Nat.card (barM M R₀) = 3 ^ 4 := by
      have h1 : Nat.card (barM M R₀) = Nat.card (R₀.subgroupOf M) :=
        card_map_mk_of_isPGroup Nat.prime_three _ hOcop2 hR₀p.comap_subtype
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀M).toEquiv, hR₀c]
    have h81 : 3 ^ 4 ∣ Nat.card (blockParabolic M (pCoreOf 2 H) L) := by
      rw [hPL, ← hbR]
      exact Subgroup.card_dvd_of_le
        (Subgroup.map_mono (Subgroup.comap_mono (hR₀I.trans hI₀Pi)))
    have h5 : ¬ 3 ^ 5 ∣ Nat.card (blockParabolic M (pCoreOf 2 H) L) := by
      rw [hPL]
      intro h
      exact hH5 (h.trans ((card_barM_dvd hPiM).trans (Subgroup.card_dvd_of_le hPiH)))
    have hQ81 := Q'.pow_dvd_card_of_pow_dvd_card h81
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp Q'.isPGroup'
    have hmdvd : Nat.card (Q' : Subgroup ↥(blockParabolic M (pCoreOf 2 H) L)) ∣
        Nat.card (blockParabolic M (pCoreOf 2 H) L) := Subgroup.card_subgroup_dvd_card _
    rw [hm] at hQ81 hmdvd ⊢
    have h4 : 4 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hQ81
    have hm5 : m < 5 := by
      by_contra hm5
      push Not at hm5
      exact h5 ((Nat.pow_dvd_pow 3 hm5).trans hmdvd)
    rw [show m = 4 by omega]
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    intro h3
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    set zb : ↥M ⧸ CFSG.pCore 2 ↥M := ((z : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) with hzb
    have hzord : orderOf zb = 3 := by
      rw [hzb, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hz
    have hzc : ∀ e ∈ barM M L, e * zb = zb * e := fun e he =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨e, he⟩)
    set E₃ := barM M J₀ with hE₃
    have hE₃L : E₃ ≤ barM M L := Subgroup.map_mono (Subgroup.comap_mono
      (hJR.trans (hR₀I.trans (hI₀HL.trans inf_le_right))))
    have hE₃e : IsElemAbelian 3 E₃ :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
        (CFSG.Open.IsElemAbelian.subgroupOf hJe M) _
    have hE₃c : Nat.card E₃ = 3 ^ 3 := by
      have h1 : Nat.card (barM M J₀) = Nat.card (J₀.subgroupOf M) :=
        card_map_mk_of_isPGroup Nat.prime_three _ hOcop2 (IsPGroup.of_card hJc).comap_subtype
      rw [hE₃, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv, hJc]
    by_cases hzE : zb ∈ E₃
    ·
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hzE
      have hyJ : (y : G) ∈ J₀ := Subgroup.mem_subgroupOf.mp hy
      have hyK : (y : G) ∈ H ⊓ M := ⟨hI₀H (hR₀I (hJR hyJ)), y.2⟩
      have hyN : (y : G) ∈ N := by
        refine hcent8 (y : G) hyK fun v hv => ?_
        have hvM : v ∈ M := hI₀M hv |>.2
        have hvL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hvM⟩ ∈ barM M L :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ((hI₀HL hv).2))
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
            (y * ⟨v, hvM⟩ * y⁻¹ * (⟨v, hvM⟩ : ↥M)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyz, ← hzc _ hvL]
          group
        have h2 := (mk_eq_one_iff_coe_mem_pCoreOf _).mp h1
        have h3 : pCoreOf 2 H ≤ N := le_sSup ⟨pCoreOf_le 2 H,
          (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr
            (localGroup_le_normalizer_pCoreOf 2 H),
          by
            obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 H)
            rw [hk]
            exact Nat.Coprime.pow_right k (by norm_num)⟩
        exact h3 (hQS h2)
      have hy1 : (y : G) = 1 := by
        have hdJ : orderOf (y : G) ∣ 3 ^ 3 := by
          rw [← hJc]
          exact Subgroup.orderOf_dvd_natCard J₀ hyJ
        have hdN : orderOf (y : G) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hyN
        have hcop : Nat.Coprime (3 ^ 3) (Nat.card N) :=
          Nat.Coprime.pow_left 3 (glbPrimeCore_coprime 3 H)
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdJ hdN)
      have hy1' : y = 1 := Subtype.ext hy1
      rw [← hyz, hy1', map_one, orderOf_one] at hzord
      norm_num at hzord
    ·
      obtain ⟨hE', hcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE₃e hzord
        (fun e he => hzc e (hE₃L he)) hzE
      have hzL : zb ∈ barM M L := (z : ↥(barM M L)).2
      have hle : E₃ ⊔ Subgroup.zpowers zb ≤ barM M L :=
        sup_le hE₃L (Subgroup.zpowers_le.mpr hzL)
      have h4 : 4 ≤ Open.pRank 3 (barM M L) :=
        CFSG.SectionRank.le_pRank (by norm_num) hle hE' (by rw [hcard, hE₃c]; norm_num)
      have h3' := pRank_barM_le_three_of_setting hS hMloc hL.le
      omega
  have hLevi' := hLevi G M (pCoreOf 2 H) L hK hA hL (hT.nineThree hK h93 hL)
    (hT.nineThree_not_one hK h85 hD2 hL).1 (hT.not_isSylowTwoOf_inf hK h85 hD2 hL)
    (fun l hl hcond => hA.blockInnerNormalizer hK hT.maxTwoLocal_M hQS h84 h86 hD2 hL l hl hcond)
    (barM M (Pi ⊓ N)) I₀ (hI₀M.trans inf_le_right)
    (by rw [hPL]; exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
    (by rw [hPL]; exact Subgroup.map_mono (Subgroup.comap_mono hI₀Pi))
    (by rw [hPL]; exact hPLnorm _ hPiNPi)
    (Nat.Coprime.coprime_dvd_right ((card_barM_dvd (inf_le_left.trans hPiM)).trans
      (Subgroup.card_dvd_of_le inf_le_right)) (glbPrimeCore_coprime 3 H))
    (by rw [hPL, barM_sup_eq hI₀Pi hPiH hPiM]; exact hPLnorm _ hPiNV)
    (by rw [hPL]; exact hrel) hperf d' ψ hd' hψ hker' hQ hZ
  have h3 := pRank_barM_le_three_of_setting hS hMloc hL.le
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3
  refine ⟨?_, hZ⟩
  rcases hLevi' with ⟨d, hd6, e, -⟩ | ⟨m, d, hm, hdm, e, -⟩
  · exact absurd (hU _ d hd6 e) (by omega)
  · by_cases hm4 : m = 4
    · subst hm4
      exact ⟨d, hdm, e⟩
    · exact absurd (hΩ _ m d (by omega) hdm e) (by omega)

end Block

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
