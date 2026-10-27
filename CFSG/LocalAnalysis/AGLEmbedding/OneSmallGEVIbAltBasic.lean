module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.CommuteOfDecomp
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverStar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

namespace D1IbAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem prime (hc : D1IbAltConfig p P M H R Rbar K z) : p.Prime := hc.data.cfg.red.prime

theorem five_le (hc : D1IbAltConfig p P M H R Rbar K z) : 5 ≤ p := by
  rcases hc.prime57 with h | h <;> omega

theorem mem_M (hc : D1IbAltConfig p P M H R Rbar K z) : z ∈ M := hc.phase.le_M hc.elt.1

theorem le_centralizer (hc : D1IbAltConfig p P M H R Rbar K z) :
    R ≤ Subgroup.centralizer ({z} : Set G) :=
  hc.data.le_centralizer_czElt hc.elt

theorem card_d1LiftX (hc : D1IbAltConfig p P M H R Rbar K z) :
    Nat.card (d1LiftX p H R K) = p ^ 2 ∧ z ∉ d1LiftX p H R K := by
  obtain ⟨hzT, hT⟩ := hc.data.d1LiftX_facts hc.elt
  exact ⟨hT.trans hc.card_T, hzT⟩

theorem coprime_twoCore (hc : D1IbAltConfig p P M H R Rbar K z) :
    p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
  rw [hk]
  exact ((Nat.coprime_primes hc.prime Nat.prime_two).mpr hc.data.cfg.red.ne_two).pow_right k

theorem zbar_pow (hc : D1IbAltConfig p P M H R Rbar K z) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ^ p = 1 := by
  have : (⟨z, hc.mem_M⟩ : M) ^ p = 1 :=
    Subtype.ext (by simp [← hc.elt.2.1, pow_orderOf_eq_one])
  rw [← map_pow, this, map_one]

theorem isPGroup_zpowers (hc : D1IbAltConfig p P M H R Rbar K z) :
    IsPGroup p (Subgroup.zpowers z) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc.elt.2.1, pow_one])

theorem mem_normalizer_block (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    z ∈ Subgroup.normalizer (L : Set G) :=
  hc.phase.mem_normalizer_block_of_five hc.data.cfg.ind hB.h85 hB.h86 hB.h93 hB.hD2 hB.hK2
    hB.hC3 hB.hK5 hc.five_le ⟨hc.elt.2.2.1, hc.mem_M⟩ hc.elt.2.1 hL

theorem zbar_mem_normalizer (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  mem_normalizer_barM hc.mem_M (hc.mem_normalizer_block hB hL)

theorem zbar_fixed_le (hc : D1IbAltConfig p P M H R Rbar K z) (L : Subgroup G) :
    ∀ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * l *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩)⁻¹ = l →
      l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) :=
  hc.phase.fixed_le_barM_normalizer_inf hc.prime hc.data.cfg.red.ne_two hc.mem_M
    hc.isPGroup_zpowers hc.cz_le

theorem zbar_not_mem_centralizer (hc : D1IbAltConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro hzc
  apply hc.phase.barM_ne_of_isWeakSBlock hL
  refine le_antisymm (barM_mono inf_le_right) fun l hl => hc.zbar_fixed_le L l hl ?_
  rw [← Subgroup.mem_centralizer_iff.mp hzc l hl, mul_inv_cancel_right]

theorem zbar_mem_sup (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hN := hc.zbar_mem_normalizer hB hL
  obtain ⟨U, hUHM, hUp, hzU, hUN⟩ := hc.cover
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hUM : U ≤ M := hUHM.trans inf_le_right
  set V := barM M U
  have hVp : ⁅V, V⁆ = V := by
    have h1 : ⁅U.subgroupOf M, U.subgroupOf M⁆ = U.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUM, hUp]
    change ⁅(U.subgroupOf M).map mkM, (U.subgroupOf M).map mkM⁆ = (U.subgroupOf M).map mkM
    rw [← Subgroup.map_commutator, h1]
  have hVL : V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact mem_normalizer_barM u.2 (hUN L hL (Subgroup.mem_subgroupOf.mp hu))
  have hzV : mkM ⟨z, hc.mem_M⟩ ∈ V := ⟨⟨z, hc.mem_M⟩, Subgroup.mem_subgroupOf.mpr hzU, rfl⟩
  rcases blockType_ib hc.phase hB.h85 hB.h93 hB.hD2 hL with htype | ⟨hcl, -, -, -⟩
  · exact hB.hOP _ (barM M L) hL.component p hc.prime hc.five_le htype _ hN hc.zbar_pow
  rcases hcl with ⟨d, -, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨d, -, ⟨e⟩⟩
  · exact perfect_le_sup_centralizer_of_outer
      (isSolvable_outer_of_component hB.hSch hL.component ⟨_, ⟨e⟩⟩) hVp hVL hzV
  · exact hB.hOP _ (barM M L) hL.component p hc.prime hc.five_le (Or.inr ⟨n, Or.inr ⟨e⟩⟩) _
      hN hc.zbar_pow
  · exact perfect_le_sup_centralizer_of_outer
      (isSolvable_outer_of_component hB.hSch hL.component ⟨_, ⟨e⟩⟩) hVp hVL hzV

theorem normal_K (hc : D1IbAltConfig p P M H R Rbar K z) : K.Normal :=
  hc.data.cfg.red.normal_of_rankOne hc.data.comp hc.data.noncyclic

theorem centralizer_le_d1X0 (hc : D1IbAltConfig p P M H R Rbar K z) :
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H := by
  obtain ⟨zb, hzR, hzK, hzp, hzc⟩ := hc.data.z
  exact hc.data.cfg.red.centralizer_le_of_rankOne hc.data.noncyclic hzR hzK hzp hzc

theorem inf_centralizer_eq_bot (hc : D1IbAltConfig p P M H R Rbar K z) :
    K ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ :=
  inf_centralizer_eq_bot_of_center hc.data.center

theorem inf_d1X0_eq (hc : D1IbAltConfig p P M H R Rbar K z) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :
    K ⊓ d1X0 p M H = (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype := by
  obtain ⟨zb, hzR, hzK, hzp, hzc⟩ := hc.data.z
  obtain ⟨hN, hKX₀⟩ :=
    hc.data.cfg.red.rankOne_principle hc.data.comp hc.data.noncyclic hzR hzK hzp hzc
  have hne := hc.data.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT₁
  have hΓX : (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype ≤ d1X0 p M H :=
    glbCore_map_le_of_normalizer_le hc.prime hT₁ hN
  have hcomap : (d1X0 p M H).comap K.subtype = GLBCore p 1 (T₁ : Subgroup K) := by
    rcases (hc.uprime T₁ hne).1 ((d1X0 p M H).comap K.subtype)
      (Subgroup.map_le_iff_le_comap.mp hΓX) with h | h
    · exact h
    · exact absurd (fun k hk => (Subgroup.mem_comap.mp (h.ge (Subgroup.mem_top ⟨k, hk⟩)) :)) hKX₀
  rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]

theorem orderOf_zH (hc : D1IbAltConfig p P M H R Rbar K z) :
    orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hc.elt.2.2.1⟩) = p := by
  have : Fact p.Prime := ⟨hc.prime⟩
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · have : (⟨z, hc.elt.2.2.1⟩ : H) ^ p = 1 :=
      Subtype.ext (by simp [← hc.elt.2.1, pow_orderOf_eq_one])
    rw [← map_pow, this, map_one]
  · have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have h3 := Subgroup.orderOf_dvd_natCard _ h2
    rw [hc.elt.2.1] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hc.prime).mp (glbPrimeCore_coprime p H) h3

theorem orderOf_zbar (hc : D1IbAltConfig p P M H R Rbar K z) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩) = p := by
  have : Fact p.Prime := ⟨hc.prime⟩
  refine orderOf_eq_prime hc.zbar_pow fun h1 => hc.data.cfg.red.ne_two ?_
  have h2 := coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  have h3 := Subgroup.orderOf_dvd_natCard _ h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  rw [hk, hc.elt.2.1] at h3
  exact (Nat.prime_dvd_prime_iff_eq hc.prime Nat.prime_two).mp (hc.prime.dvd_of_dvd_pow h3)

theorem commute_of_mem_R (hc : D1IbAltConfig p P M H R Rbar K z) {a b : G} (ha : a ∈ R)
    (hb : b ∈ R) : a * b = b * a := by
  have : Fact p.Prime := ⟨hc.prime⟩
  exact commute_of_mem_of_decomp
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hc.card_d1LiftX.1) (d1LiftX_le p H R K)
    (fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer hr)) hc.dec ha hb

end D1IbAltConfig

end CFSG.AGLEmbedding
