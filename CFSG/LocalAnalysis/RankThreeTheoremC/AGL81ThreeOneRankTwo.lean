module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneAltSpor
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerMain
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section RankTwoCert


theorem sporTwo_cases
    {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {s : TauCeti.SporadicName} (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h2 : Open.pRank p (⊤ : Subgroup K) ≤ 2) (h3 : p ^ 3 ∣ Nat.card K) :
    IsNineThreeIndex p (.sporadic s) ∨ IsSporPlanePair s p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  have hcard : Nat.card K = sporOrd s := (Nat.card_congr (e.trans b.symm).toEquiv).trans
    (card_carrier_eq_sporOrd CFSG.Milestones.fam_m_finiteness s)
  have h3' : p ^ 3 ∣ sporOrd s := hcard ▸ h3
  have hrank : P1ThreeSporList p s → ¬ (s = .J3 ∧ p = 3) → ¬ (s = .M22 ∧ p = 3) →
      ¬ (s = .Fi24Prime ∧ p = 7) → ¬ (s = .M ∧ p = 13) → False := by
    intro hs hJ3 hM22 hFi hM
    haveI : Nontrivial K := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      have hle := Nat.le_of_dvd Nat.card_pos h3
      have hpow : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    have hT := three_le_pRank_of_weakCore_eq_top hp
      (weakCore_eq_top_spor hp hp2 e hs hJ3 hM22 hFi hM (default : Sylow p K))
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      (le_top : ((default : Sylow p K) : Subgroup K) ≤ ⊤)
    omega
  rcases offList_cases s p hp hp2 h3' with hl | hr
  · by_cases hJ3 : s = .J3 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := hJ3
      exact Or.inl (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩)
    by_cases hM22 : s = .M22 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := hM22
      norm_num [sporOrd] at h3'
    by_cases hFi : s = .Fi24Prime ∧ p = 7
    · obtain ⟨rfl, rfl⟩ := hFi
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)))
    by_cases hM : s = .M ∧ p = 13
    · obtain ⟨rfl, rfl⟩ := hM
      simp [IsSporPlanePair]
    exact (hrank hl hJ3 hM22 hFi hM).elim
  · unfold P1OffRow at hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp [IsNineThreeIndex, IsSporPlanePair]

variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

theorem Hyp.threeOne_two_lieChar
    (H : Hyp p K P E) (h3 : ¬ 3 ≤ Open.pRank p (P : Subgroup G))
    (hC : Subgroup.centralizer (K : Set G) = ⊥) (d : TauCeti.ValidLieTypeIndex)
    (hpd : p = d.1.characteristic) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    OnThreeOneList p K := by
  have hK2 : Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
    have := H.pRank_top_le
    omega
  have hsmall : CFSG.AGLEmbeddingD2.IsD2LieCharSmall p d.1 := by
    by_contra hns
    have := CFSG.AGLEmbeddingD2.kFactLieCharRank K d ⟨e⟩ p H.prime H.ne_two hpd hns
    omega
  have hPK : (P : Subgroup G) ≤ K := H.le_of_not_dvd_card_outer hC
    (CFSG.AGLEmbeddingD2.kFactLieCharOut K d ⟨e⟩ p H.prime H.ne_two hsmall)
  obtain ⟨q, hqp, ⟨hqe, hd⟩ | ⟨hqe, hd | hd⟩⟩ := hsmall
  · by_cases h1 : q.exponent = 1
    · exfalso
      have hr := CFSG.AGLEmbeddingD2.kFactLinTwoPrimeRank K d ⟨e⟩ p H.prime H.ne_two
        ⟨q, hqp, h1, hd⟩
      obtain ⟨hEl, hEc⟩ := H.elem_subgroupOf (H.E_le.trans hPK)
      have := CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian_of_pow_le_card H.prime hEl le_top
        (n := 2) (by rw [hEc])
      omega
    · have := q.exponent_pos
      exact ⟨.lie d, Or.inl (Or.inl ⟨q, hqp, by omega, hd⟩), ⟨e⟩⟩
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hqp, hqe, hd⟩)))), ⟨e⟩⟩
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inl ⟨q, hqp, hd⟩)), ⟨e⟩⟩

private theorem le_glbCore_one_of_seitz
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) (hp : p.Prime)
    (hp2 : p ≠ 2) [K.Normal] (hC : Subgroup.centralizer (K : Set G) = ⊥)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hpd : p ≠ d.1.characteristic)
    (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) : K ≤ GLBCore p 1 E := by
  have hφ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hC] at hxc
    exact Subgroup.mem_bot.mp hxc
  let ψ : G →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hψ : Function.Injective ψ := (MulAut.congr e).injective.comp hφ
  have hclos := hS d p hp hp2 hpd hex (E.map ψ) (hE.map ψ)
    (by rw [Subgroup.card_map_of_injective hψ, hcard])
  have hle : (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤
      ((GLBCore p 1 E).subgroupOf K).map e.toMonoidHom := by
    rw [← hclos, Subgroup.closure_le]
    rintro c ⟨ε, hε, hε1, hεc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hε
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    refine ⟨e.symm c, ?_, by simp⟩
    have h1 : ψ x c = e (MulAut.conjNormal (H := K) x (e.symm c)) := by
      simp [ψ, MulAut.congr_apply]
    have h2 : MulAut.conjNormal (H := K) x (e.symm c) = e.symm c := by
      apply e.injective
      rw [← h1, hεc, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul] at h3
    exact Subgroup.mem_subgroupOf.mpr (mem_glbCore_of_commute hp hE hx hx1 h3.symm)
  intro k hk
  obtain ⟨k', hk', hk'e⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_top (e ⟨k, hk⟩)))
  obtain rfl : k' = ⟨k, hk⟩ := e.injective hk'e
  exact hk'

theorem Hyp.threeOne_two_lieCross
    (H : Hyp p K P E) (h3 : ¬ 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBCore p 1 E) (hC : Subgroup.centralizer (K : Set G) = ⊥)
    (d : TauCeti.ValidLieTypeIndex) (hpd : p ≠ d.1.characteristic)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : OnThreeOneList p K := by
  have hZ := H.center_eq_bot_of_centralizer_eq_bot hC
  by_cases hex : CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1
  · rcases hex with ⟨hp3, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ |
        ⟨q, hq2, hq1, hd | hd⟩ | hd⟩ | ⟨hp5, hd | hd⟩
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hp3, Or.inl ⟨q, hq2, hq3, Or.inl hd⟩⟩)))))), ⟨e⟩⟩
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hp3, Or.inr (Or.inl ⟨q, hq2, hq2', hd⟩)⟩)))))), ⟨e⟩⟩
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inl ⟨q, Or.inr ⟨hp3, hq2, hq1, hd⟩⟩))), ⟨e⟩⟩
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hp3, Or.inr (Or.inr (Or.inl ⟨q, hq2, hq1, hd⟩))⟩)))))), ⟨e⟩⟩
    · subst hp3
      obtain ⟨hs, -, -⟩ := H.isCatalogGroup hZ
      haveI := hs
      have e₀ : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
      have hcyc : IsCyclic (Subgroup.center K) := by
        rw [hZ]
        infer_instance
      obtain ⟨T⟩ : Nonempty (Sylow 3 K) := inferInstance
      have h3T := three_le_pRank_of_weakCore_eq_top H.prime
        (kFactChevTwoInnerGen_of_certificates d ⟨q, hq2, hq1, Or.inl hd⟩ K H.quasi ⟨e₀⟩
          H.isPGroup_center hcyc T)
      have hTK : Open.pRank 3 (T : Subgroup K) ≤ Open.pRank 3 (⊤ : Subgroup K) :=
        CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 H.prime le_top
      have := H.pRank_top_le
      omega
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hp3, Or.inr (Or.inr (Or.inr hd))⟩)))))), ⟨e⟩⟩
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hp5, Or.inr (Or.inl hd)⟩)))))), ⟨e⟩⟩
    · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hp5, Or.inl hd⟩)))))), ⟨e⟩⟩
  · haveI := H.normal
    exact (hnot (le_glbCore_one_of_seitz
      CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds H.prime H.ne_two hC H.elem H.card_E d e
      hpd hex)).elim

theorem Hyp.threeOne_two_abelian
    (H : Hyp p K P E) (h3 : ¬ 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBCore p 1 E) (hZ : Subgroup.center K = ⊥) (hPK : (P : Subgroup G) ≤ K)
    (hcard : Nat.card (P : Subgroup G) = p ^ 2) : OnThreeOneList p K := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  obtain ⟨hs, hnab, hcat⟩ := H.isCatalogGroup hZ
  have hPE : (P : Subgroup G) = E :=
    (Subgroup.eq_of_le_of_card_ge H.E_le (by rw [hcard, H.card_E])).symm
  set T : Sylow p K := P.subtype hPK
  have hT : (T : Subgroup K) = E.subgroupOf K := by rw [Sylow.coe_subtype, hPE]
  obtain ⟨hEl, hEc⟩ := H.elem_subgroupOf (H.E_le.trans hPK)
  have hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤ := by
    rw [hT]
    exact fun h => hnot (le_glbCore_one_of_subgroupOf (H.E_le.trans hPK) h)
  have hK2 : 2 ≤ Open.pRank p (⊤ : Subgroup K) :=
    CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian_of_pow_le_card H.prime hEl le_top (n := 2)
      (by rw [hEc])
  have h2 : Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
    have := H.pRank_top_le
    omega
  exact onThreeOneList_of_isSmallStrongP H.prime H.ne_two
    (CFSG.LocalAnalysis.UniquenessCase.UCK.kFactSmallIdent_holds K hs hnab hcat p H.prime H.ne_two T
      (CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.not_isCyclic_sylow_of_two_le_pRank hK2 T)
      hΓ
        ((CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.pRank_top_subgroup_top H.prime).trans_le
          h2))

private theorem not_pow_three_dvd_card_alt
    {L : Type} [Group L] [Finite L] {n q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (e : L ≃* alternatingGroup (Fin n)) (hn : n < 3 * q) :
    ¬ q ^ 3 ∣ Nat.card L := by
  intro h
  rw [Nat.card_congr e.toEquiv] at h
  have hfac : q ^ 3 ∣ n.factorial := by
    have hA := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
    rw [Nat.card_perm, Nat.card_fin] at hA
    exact h.trans hA
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have hlog : Nat.log q n < 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact Nat.log_lt_of_lt_pow hn0.ne' (by nlinarith)
  rw [hq.pow_dvd_factorial_iff hlog, Finset.sum_Ico_eq_sum_range] at hfac
  simp only [Nat.reduceSub, Finset.sum_range_one, add_zero, pow_one] at hfac
  have : n / q < 3 := (Nat.div_lt_iff_lt_mul hq.pos).2 hn
  omega

theorem Hyp.threeOne_two_alt
    (H : Hyp p K P E) (h3 : ¬ 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBCore p 1 E) (hC : Subgroup.centralizer (K : Set G) = ⊥) (n : ℕ)
    (hn : 5 ≤ n) (e : K ≃* (TauCeti.CFSGIndex.alternating n hn).Group) :
    OnThreeOneList p K := by
  have e' : K ≃* alternatingGroup (Fin n) := e
  have hZ := H.center_eq_bot_of_centralizer_eq_bot hC
  have hPK : (P : Subgroup G) ≤ K := H.le_of_not_dvd_card_outer hC
    (not_dvd_card_outer_of_mulEquiv_of_not_dvd e'
      (not_dvd_card_outer_alternatingGroup n hn p H.prime H.ne_two))
  have hK2 : Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
    have := H.pRank_top_le
    omega
  by_cases h3p : 3 * p + 1 ≤ n
  · haveI : Fact p.Prime := ⟨H.prime⟩
    haveI : IsSimpleGroup K := (H.isCatalogGroup hZ).1
    have hT := three_le_pRank_of_weakCore_eq_top H.prime
      (weakCore_eq_top_of_three_mul_lt H.prime H.ne_two h3p e' (default : Sylow p K))
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p H.prime
      (le_top : ((default : Sylow p K) : Subgroup K) ≤ ⊤)
    omega
  · by_cases h23 : n = 2 * p ∨ n = 3 * p
    · exact ⟨.alternating n hn, Or.inr (Or.inr ⟨n, hn, rfl, h23⟩), ⟨e⟩⟩
    · exact H.threeOne_two_abelian h3 hnot hZ hPK (H.card_eq_sq_of_not_dvd hPK
        (not_pow_three_dvd_card_alt H.prime H.ne_two e' (by omega)))

theorem Hyp.threeOne_two_spor
    (H : Hyp p K P E) (hS : KFactThreeOneSporPlane)
    (h3 : ¬ 3 ≤ Open.pRank p (P : Subgroup G)) (hnot : ¬ K ≤ GLBCore p 1 E)
    (hC : Subgroup.centralizer (K : Set G) = ⊥) (s : TauCeti.SporadicName)
    (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : OnThreeOneList p K := by
  have hZ := H.center_eq_bot_of_centralizer_eq_bot hC
  have hPK : (P : Subgroup G) ≤ K :=
    H.le_of_not_dvd_card_outer hC (not_dvd_card_outer_spor H.prime H.ne_two e)
  by_cases hp3 : p ^ 3 ∣ Nat.card K
  · have h2 : Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
      have := H.pRank_top_le
      omega
    rcases sporTwo_cases H.prime H.ne_two e h2 hp3 with hi | hpair
    · exact ⟨.sporadic s, Or.inl hi, ⟨e⟩⟩
    · obtain ⟨hEl, hEc⟩ := H.elem_subgroupOf (H.E_le.trans hPK)
      exact (hnot (le_glbCore_one_of_subgroupOf (H.E_le.trans hPK)
        (hS s p hpair K ⟨e⟩ _ hEl hEc))).elim
  · exact H.threeOne_two_abelian h3 hnot hZ hPK (H.card_eq_sq_of_not_dvd hPK hp3)

theorem Hyp.threeOne_of_two
    (H : Hyp p K P E) (hS : KFactThreeOneSporPlane)
    (h3 : ¬ 3 ≤ Open.pRank p (P : Subgroup G)) (hnot : ¬ K ≤ GLBCore p 1 E) :
    OnThreeOneList p K ∧ Subgroup.center K = ⊥ := by
  have hC := H.centralizer_eq_bot_of_two h3 hnot
  have hZ := H.center_eq_bot_of_centralizer_eq_bot hC
  refine ⟨?_, hZ⟩
  obtain ⟨i, ⟨e⟩⟩ := (H.isCatalogGroup hZ).2.2
  cases i with
  | cyclic q hq => exact (H.false_of_cyclic e).elim
  | alternating n hn => exact H.threeOne_two_alt h3 hnot hC n hn e
  | lie d =>
    by_cases hpd : p = d.1.characteristic
    · exact H.threeOne_two_lieChar h3 hC d hpd e
    · exact H.threeOne_two_lieCross h3 hnot hC d hpd e
  | sporadic s => exact H.threeOne_two_spor hS h3 hnot hC s e

end RankTwoCert

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
