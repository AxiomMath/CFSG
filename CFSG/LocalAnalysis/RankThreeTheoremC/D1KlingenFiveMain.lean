module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFivePkg
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveBlock
import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveComp
import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Normalizes
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem kl5_mk_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M : Subgroup G} {z : G} (hzM : z ∈ M)
    (hz : orderOf z = p) : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ≠ 1 := by
  intro h1
  have hmem : z ∈ pCoreOf 2 M := coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) ⟨z, hmem⟩
  have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : p ∣ 2 ^ k := hz ▸ orderOf_dvd_of_pow_eq_one hzk
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd))

theorem kl5_pRank_pCore_le (hrank : evenRank G = 3) {M : Subgroup G} (hM : IsTwoLocal M) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) :
    Open.pRank s (CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ 3 := by
  have h1 : Open.pRank s (CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Open.pRank s (barM M M) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono s hs.one_lt (fun y _ => by
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) y
      exact ⟨m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩)
  have h2 := stmtBarPRankLift hs hs2 M M le_rfl
  have h3 := local_pRank_le_localRank s hs.one_lt M hM
  have h4 := rankThreeLocalRank_le_evenRank (G := G) s hs hs2
  rw [hrank] at h4
  omega

theorem kl5_mk_mem_of_hyperplane {p : ℕ} [Fact p.Prime] {M R X : Subgroup G} {σ z : G}
    (hpkg : D1KlingenFivePkg p R X σ z) (hR : IsPGroup p R) (hRM : R ≤ M)
    {F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hF : F.relIndex (barM M X) = p)
    (hσF : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨σ, hRM hpkg.σ_mem⟩ ∈
      Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hRM (hpkg.le_R hpkg.z_mem)⟩ ∈ F := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hXM : X ≤ M := hpkg.le_R.trans hRM
  have hσM : σ ∈ M := hRM hpkg.σ_mem
  let ρ : ↥X →* ↥M ⧸ CFSG.pCore 2 ↥M := mk.comp (Subgroup.inclusion hXM)
  have hrange : ρ.range = barM M X := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  set F' : Subgroup G := (F.comap ρ).map X.subtype with hF'
  have hF'sub : F'.subgroupOf X = F.comap ρ :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hF'X : F' ≤ X := Subgroup.map_subtype_le _
  have hF'rel : F'.relIndex X = p := by
    have h1 : F'.relIndex X = (F.comap ρ).index := by rw [Subgroup.relIndex, hF'sub]
    rw [h1, Subgroup.index_comap, hrange]
    exact hF
  have hmem : ∀ g : G, g ∈ F' ↔ ∃ hgX : g ∈ X, mk ⟨g, hXM hgX⟩ ∈ F := by
    intro g
    constructor
    · intro hg
      have hgX : g ∈ X := hF'X hg
      refine ⟨hgX, ?_⟩
      have h1 : (⟨g, hgX⟩ : ↥X) ∈ F'.subgroupOf X := hg
      rw [hF'sub] at h1
      exact h1
    · rintro ⟨hgX, hg⟩
      have h1 : (⟨g, hgX⟩ : ↥X) ∈ F.comap ρ := hg
      rw [← hF'sub] at h1
      exact h1
  have hσX : σ ∈ Subgroup.normalizer (X : Set G) := hpkg.le_normalizer hpkg.σ_mem
  have hσF' : σ ∈ Subgroup.normalizer (F' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hgX : g ∈ X
    · have hgX' : σ * g * σ⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hσX g).mp hgX
      have hconj : mk ⟨σ * g * σ⁻¹, hXM hgX'⟩ =
          mk ⟨σ, hσM⟩ * mk ⟨g, hXM hgX⟩ * (mk ⟨σ, hσM⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [hmem g, hmem (σ * g * σ⁻¹)]
      simp only [hgX, hgX', exists_true_left]
      rw [hconj]
      exact Subgroup.mem_normalizer_iff.mp hσF _
    · have hgX' : σ * g * σ⁻¹ ∉ X := fun h => hgX ((Subgroup.mem_normalizer_iff.mp hσX g).mpr h)
      exact ⟨fun h => absurd (hF'X h) hgX, fun h => absurd (hF'X h) hgX'⟩
  have hz := hpkg.mem_of_hyperplane hR hF'X hF'rel hσF'
  obtain ⟨hzX, hz'⟩ := (hmem z).mp hz
  exact hz'

theorem kl5_mk_mem_centralizer_pCore {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p) {P : Sylow p G} {M H R X : Subgroup G} {σ z : G}
    (hph : D1PhaseThree p P M H R) (hrank : evenRank G = 3) (hR : IsPGroup p R)
    (hpkg : D1KlingenFivePkg p R X σ z) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M (hpkg.le_R hpkg.z_mem)⟩ ∈
      Subgroup.centralizer ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup
        (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp : p.Prime := Fact.out
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  have hRM : R ≤ M := hph.le_M
  have hσM : σ ∈ M := hRM hpkg.σ_mem
  have hzM : z ∈ M := hRM (hpkg.le_R hpkg.z_mem)
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hσp : mk ⟨σ, hσM⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨σ, hσM⟩ : M) ^ p = 1 := Subtype.ext hpkg.σ_pow
    rw [this, map_one]
  refine oddCore_centralized_of_hyperplane hs hs2 hp hp5 hsp Sg (barM M X) (mk ⟨σ, hσM⟩)
    (mk ⟨z, hzM⟩) CFSG.pCore_isPGroup (kl5_pRank_pCore_le hrank hph.maxTwoLocal_M.1 hs hs2)
    (le_top.trans hSgN) (hSgN (Subgroup.mem_top _)) (isElemAbelian_barM hpkg.elem)
    (mem_normalizer_barM hσM (hpkg.le_normalizer hpkg.σ_mem)) (fun x _ => by
      rw [hσp, one_mul, inv_one, mul_one])
    ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hpkg.z_mem, rfl⟩ ?_
  intro F _ hF hσF
  exact kl5_mk_mem_of_hyperplane hpkg hR hRM hF hσF

theorem kl5_mk_mem_centralizer_component (hOut : KFactOutElemRank)
    (hK7 : KFactBlockHeisenbergInner) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {P : Sylow p G} {M H R X : Subgroup G} {σ z : G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar) (hph : D1PhaseThree p P M H R)
    (hpkg : D1KlingenFivePkg p R X σ z)
    (hY₀B : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer
        (((X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)))
    (hC : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer
        (((X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lbar ⊤) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M (hpkg.le_R hpkg.z_mem)⟩ ∈
      Subgroup.centralizer (Lbar : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp : p.Prime := Fact.out
  have hRM : R ≤ M := hph.le_M
  have hRp : IsPGroup p R := hcfg.ext.isPGroup
  have hrank : evenRank G = 3 := hcfg.glob.rank
  obtain ⟨L, hL2, rfl, hcase⟩ := hph.exists_weakSBlock_or_le_inf hLb
  by_contra hnotmem
  have hnot : ¬ ∀ y ∈ barM M L,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hRM (hpkg.le_R hpkg.z_mem)⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hRM (hpkg.le_R hpkg.z_mem)⟩ :=
    fun hc => hnotmem (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm)
  have hRL : R ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isPGroup_ge_five hrank hp hp5 hph.maxTwoLocal_M.1 hL2 hRp hRM
  have hfaith := kl5_inf_preimage_eq_bot hpkg hRp hRM hRL hnot
  rcases hcase with hw | hle
  · exact kl5_false_of_weakSBlock hp5 hK7 h84 h85 h86 h93 hD2 hph hrank hpkg hw hRL hfaith
  · have hXL : X ≤ Subgroup.normalizer (L : Set G) := hpkg.le_R.trans hRL
    have hpL := not_dvd_card_barM_of_le_inf hph hpkg.elem hY₀B hC hL2 hle hXL
    have hP3 : Open.pRank p R = 3 :=
      le_antisymm ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hcfg.ext.le_P).trans
        hcfg.pRank_eq_three.le) hcfg.ext.three_le_pRank
    have hMtop : M ≠ ⊤ := fun hMt => hph.not_le (hMt ▸ le_top)
    have hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      ((catalogSimpleSections_of_isKProper hph.glob.kProper M hMtop).quotient
        _).isCatalogGroup_center_quotient hL2.component
    exact hpL (dvd_card_barM_of_faithful hOut hp hp5 hP3 hRM hRL hL2.component hcat hfaith)

theorem stmtKlingenMSideFive3_of (hmod : StmtKlingenModel) (hk5 : KFactKlingenFiveLocal)
    (hK7 : KFactBlockHeisenbergInner) (hOut : KFactOutElemRank) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) :
    StmtKlingenMSideFive3 G := by
  intro p _ hp3 P M H R Rbar hcfg K hK huniq hnc hcent hKD hsp X hS hXel hXc hO
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have := hcfg.loc.ne_two
    omega
  have hred := hcfg.red
  have hph : D1PhaseThree p P M H R := hS.ph3
  obtain ⟨d, hd, ⟨e₁⟩⟩ := hsp
  have hZ : Subgroup.center K = ⊥ :=
    hmod.center K p d hcfg.loc.ne_two hd hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK₀ : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have eK : K ≃* CatGroup d := eK₀.trans e₁
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hCK := hcfg.centralizer_eq_bot hK huniq hcent hZ
  have hXH : X ≤ H := hS.le_R.trans hcfg.ext.le_H
  have hXp : IsPGroup p X := hcfg.ext.isPGroup.to_le hS.le_R
  have hXp' : IsPGroup p (X.subgroupOf H) := hXp.comap_subtype
  have hcard : Nat.card ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) = p ^ 3 := by
    rw [card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hXp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
  have hXRb : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hcfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hS.le_R)
  have hXe : IsElemAbelian p ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) := by
    refine elementary_abelian_map p ?_ _
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := (isMulCommutative_iff.mp hXel.1) ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (hXel.2 _ (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨hYB, hT, hZc⟩ := hk5 p hp5 d hd (H ⧸ primeComplementCore (G := H) p) K hKn ⟨eK⟩ hCK
    Rbar _ _ hXRb hXe hcard hred.weakCore_le hred.ne_top
  obtain ⟨σ, z, hpkg⟩ := exists_d1KlingenFivePkg hcfg hS hXel hXc hT hZc hKD
  have hCle := (kl5_centralizer_inf_le hS).trans hcfg.rbar.ge
  have hRM : R ≤ M := hph.le_M
  have hzM : z ∈ M := hRM (hpkg.le_R hpkg.z_mem)
  have hRp : IsPGroup p R := hcfg.ext.isPGroup
  have hrank : evenRank G = 3 := hcfg.glob.rank
  have hz1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ≠ 1 :=
    kl5_mk_ne_one hcfg.loc.ne_two hzM (orderOf_eq_prime (hpkg.elem.2 z hpkg.z_mem) hpkg.z_ne)
  have hzp : IsPGroup p (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩)) := by
    refine isPGroup_zpowers_of_pow_eq_one (k := 1) ?_
    have : (⟨z, hzM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hpkg.elem.2 z hpkg.z_mem)
    rw [pow_one, ← map_pow, this, map_one]
  have hle : Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) ≤
      CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_pCore_of_le_centralizer_components hzp (fun Lb hLb => ?_) fun l hl => ?_
    · exact Subgroup.zpowers_le.mpr (kl5_mk_mem_centralizer_component hOut hK7 h84 h85 h86 h93 hD2
        hp5 hcfg hph hpkg hYB hCle hLb)
    · by_cases hl2 : l = 2
      · rw [hl2, pCore_quotient_pCore_eq_bot']
        exact Subgroup.le_centralizer_iff.mp bot_le
      by_cases hlp : l = p
      · rw [hlp, hO]
        exact Subgroup.le_centralizer_iff.mp bot_le
      exact Subgroup.zpowers_le.mpr (kl5_mk_mem_centralizer_pCore hp5 hl hl2 hlp hph hrank hRp hpkg)
  have h1 := hle (Subgroup.mem_zpowers _)
  rw [hO, Subgroup.mem_bot] at h1
  exact hz1 h1

theorem d1KlingenResidue3_of_other (hmod : StmtKlingenModel) (hk3 : KFactKlingenThreeLocal)
    (hk5 : KFactKlingenFiveLocal) (hK7 : KFactBlockHeisenbergInner) (hOut : KFactOutElemRank)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hi : KFactBlockThreeOneOrbit) (h : D1CaseThreeKlingenOther3 G) : D1KlingenResidue3 G :=
  ⟨h, stmtKlingenMSide3_of_five hmod hk3 h84 h85 h86 h93 hD2 hK2 hC3 hK5 hi
    (stmtKlingenMSideFive3_of hmod hk5 hK7 hOut h84 h85 h86 h93 hD2)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
