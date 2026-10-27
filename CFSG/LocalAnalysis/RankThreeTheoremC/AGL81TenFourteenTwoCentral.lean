module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNineTwoOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineCompetitorSplit
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeNormalRank
import CFSG.RankThree.OddKernel.ComponentRanks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_centralizer_not_le {p : ℕ} [Fact p.Prime] {M : Subgroup G} {a : G}
    (hao : orderOf a = p) (hC : ¬ centralizer ({a} : Set G) ≤ M) {U R : Subgroup G}
    (hUC : U ≤ centralizer ({a} : Set G)) (hUQ : IsAGLQ p M U) (hUR : U ≤ R) (haR : a ∈ R) :
    3 ≤ CFSG.Open.pRank p R := by
  have hp : p.Prime := Fact.out
  have hap : a ^ p = 1 := hao ▸ pow_orderOf_eq_one a
  rcases hUQ.2.2 with h3 | ⟨E, hEU, hE, hEc, hΓ⟩
  · exact (CFSG.SectionRank.pRank_coe_eq_openPRank p U ▸ h3).trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hUR)
  by_cases haE : a ∈ E
  · exfalso
    apply hC
    have hQE : zpowers a ≤ E := zpowers_le.mpr haE
    have hrank : 1 ≤ CFSG.Open.pRank p (zpowers a) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl (CFSG.Open.IsElemAbelian.mono hE hQE)
        (by rw [Nat.card_zpowers, hao, pow_one])
    have hN : normalizer (zpowers a : Set G) ≤ rankThreeGamma 1 p E := by
      rw [rankThreeGamma, GLBCore]
      exact le_sSup ⟨zpowers a, hQE, hrank, rfl⟩
    refine le_trans (fun x hx => ?_) (hN.trans hΓ)
    rw [mem_normalizer_iff]
    intro y
    have hxa : Commute x a := mem_centralizer_singleton_iff.mp hx
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [((hxa.zpow_right k).eq), mul_inv_cancel_right]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      calc a ^ k = x⁻¹ * a ^ k * x := by
            rw [(hxa.inv_left.zpow_right k).eq, inv_mul_cancel_right]
        _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [show a ^ k = x * y * x⁻¹ from hk]
        _ = y := by group
  · have h := CFSG.RankThree.OddKernel.succ_le_pRank_of_commute hp hE hEc
      (fun e he => mem_centralizer_singleton_iff.mp (hUC (hEU he))) hap haE
      (hEU.trans hUR) haR
    simpa using h

theorem not_dvd_card_of_d1KBar_eq_bot (h74 : AGL81SevenFourTwo)
    (hOut : KFactOutCyclic) (hS : Setting G) {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {a : G} (hao : orderOf a = p)
    (hC : ¬ centralizer ({a} : Set G) ≤ M) {U : Subgroup G}
    (hUC : U ≤ centralizer ({a} : Set G)) (hUQ : IsAGLQ p M U)
    (hK : d1KBar p M (centralizer ({a} : Set G)) = ⊥) {I : Subgroup G}
    (hIle : I ≤ centralizer ({a} : Set G) ⊓ M) (hI : ⁅I, I⁆ = I) : ¬ p ∣ Nat.card I := by
  intro hpI
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set N := centralizer ({a} : Set G) with hN
  have ha1 : a ≠ 1 := fun h => hp.one_lt.ne' (hao ▸ h ▸ orderOf_one)
  have hNtop : N ≠ ⊤ := by
    intro htop
    haveI := hS.simple
    rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hZ | hZ
    · refine ha1 ((Subgroup.mem_bot).mp (hZ ▸ Subgroup.mem_center_iff.mpr fun g => ?_))
      have hg : g ∈ N := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg a (Set.mem_singleton a)).symm
    · obtain ⟨x, y, hxy⟩ := hS.nonab
      exact hxy (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top y) x)
  obtain ⟨R, hUR, hRM, hRN, -⟩ := exists_isSylowIn_of_isAGLQ he hUQ hUC
  set T : Sylow p N := hRN.toSylow with hT
  have hTB : (T : Subgroup N).map N.subtype = R := by
    rw [hT, CFSG.Quasithin.IsSylowIn.coe_toSylow]
    exact Subgroup.map_subgroupOf_eq_of_le hRN.le
  have haN : a ∈ N := mem_centralizer_singleton_iff.mpr rfl
  have haR : a ∈ R := by
    set a' : N := ⟨a, haN⟩
    have hc : ∀ g : N, Commute g a' := fun g =>
      Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
    haveI : (zpowers a').Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      rw [((hc g).zpow_right k).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers a') k⟩
    have hap : orderOf a' = p := by rw [Subgroup.orderOf_mk, hao]
    have hzp : IsPGroup p (zpowers a') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hap, pow_one])
    rw [← hTB]
    exact ⟨a', hzp.le_sylow_of_normal T (mem_zpowers a'), rfl⟩
  have hR3 := three_le_pRank_of_centralizer_not_le hao hC hUC hUQ hUR haR
  have hRp : IsPGroup p R := hTB ▸ T.isPGroup'.map N.subtype
  obtain ⟨m, hm, hRP⟩ := Hyp111.exists_conj_le he.sylow_le hRp hRM
  have hP' : ((m • P : Sylow p G) : Subgroup G) =
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hP'M : ((m • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [hP']
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (he.sylow_le hx)) (M.inv_mem hm)
  have hW' : GLBWeakCore p ((m • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [hP']
    exact weakCore_conj_le hp he.weakCore_le hm
  have hcore : GLBPrimeCore p N ≤ M := by
    rw [← map_primeComplementCore_eq]
    exact core_le_of_base ⟨⟨H₁, R₁, he⟩⟩ hUQ hUC
  obtain ⟨Tb, -, hred⟩ := reducedNongeneration_of_not_le hp he.ne_two (m • P) hP'M hW' hC T
    (by rw [hTB, hP']; exact hRP) (by rw [hTB]; exact hR3) hcore
  have hX : CatalogSimpleSections (N ⧸ primeComplementCore (G := N) p) :=
    (catalogSimpleSections_of_isKProper hS.kProper N hNtop).quotient _
  have hle : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
      L ≤ d1X0 p M N := fun L hL => by
    by_contra hLX
    have hLK : L ≤ d1KBar p M N := le_iSup₂_of_le L ⟨hL, hLX⟩ le_rfl
    rw [hK] at hLK
    exact hLX (hLK.trans bot_le)
  have hlayer := layer_eq_bot_of_forall_component_le h74 hOut hred hX hle
  set O := primeComplementCore (G := N) p with hO
  set π := QuotientGroup.mk' O with hπ
  have hIN : I ≤ N := hIle.trans inf_le_left
  set J := (I.subgroupOf N).map π with hJ
  have hJY : J ≤ ((N ⊓ M).subgroupOf N).map π :=
    Subgroup.map_mono fun _ hx => hIle hx
  have hJperf : ⁅J, J⁆ = J := by
    rw [hJ, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hIN, hI]
  refine not_dvd_card_of_layer_eq_bot hred hlayer hJY hJperf ?_
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpI
  set x' : N := ⟨(x : G), hIN x.2⟩ with hx'
  have hx'o : orderOf x' = p := by rw [hx', Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx]
  have hord : orderOf (π x') = p := by
    have hxp : x' ^ p = 1 := hx'o ▸ pow_orderOf_eq_one x'
    refine orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) ?_
    intro h1
    have hxO : x' ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have hdvd : p ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨x', hxO⟩ : O)
      rwa [Subgroup.orderOf_mk, hx'o] at this
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p) hdvd
  have hmem : π x' ∈ J := ⟨x', x.2, rfl⟩
  have := orderOf_dvd_natCard (⟨π x', hmem⟩ : J)
  rwa [Subgroup.orderOf_mk, hord] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
