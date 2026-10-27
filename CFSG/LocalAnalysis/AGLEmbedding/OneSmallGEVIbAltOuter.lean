module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltToral
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem mem_zpowers_of_mem_block (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hyL : y ∈ barM M L)
    (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    y ∈ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩) :=
  mem_zpowers_of_mem_block_of hc.prime hc.phase.le_M hc.mem_M hc.elt.2.1 hc.coprime_twoCore
    hc.le_centralizer hc.b0 hc.phase.isPGroup (hc.mem_normalizer_of_commute hB hL) hBL hyL hyz hy
theorem eq_one_of_mem_sup (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hBC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥)
    {t : G} (ht : t ∈ d1LiftX p H R K) (hRt : t ∈ M)
    (htL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, hRt⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : t = 1 :=
  eq_one_of_mem_sup_of_block hc.prime hc.phase.le_M hc.elt.1 hc.elt.2.1 hc.mem_M hc.le_centralizer
    hc.exp hc.card_d1LiftX.2 (fun hyL hyz _ hy => hc.mem_zpowers_of_mem_block hB hL hBL hyL hyz hy)
    hzbL hBC ht hRt htL
theorem false_of_rPart_C_eq_bot (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hBC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥) :
    False := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨hTcard, -⟩ := hc.card_d1LiftX
  set T := d1LiftX p H R K
  have hRM := hc.phase.le_M
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hcomm : ∀ t (ht : t ∈ T), mkM ⟨t, hRM (hTR ht)⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro t ht
    refine hc.mem_normalizer_of_commute hB hL ?_
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer (hTR ht))))
  have hpow : ∀ t (ht : t ∈ T), mkM ⟨t, hRM (hTR ht)⟩ ^ p = 1 := by
    intro t ht
    have : (⟨t, hRM (hTR ht)⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hc.exp t (hTR ht))
    rw [← map_pow, this, map_one]
  obtain ⟨t₀, ht₀T, ht₀1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra h
    push Not at h
    have : T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hTcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  rcases blockType_ib hc.phase hB.h85 hB.h93 hB.hD2 hL with htype | ⟨hcl, hpar, hne, hnB⟩
  · exact ht₀1 (hc.eq_one_of_mem_sup hB hL hBL hzbL hBC ht₀T (hRM (hTR ht₀T))
      (hB.hOP _ (barM M L) hL.component p hp hc.five_le htype _ (hcomm t₀ ht₀T)
        (hpow t₀ ht₀T)))
  set E := barM M T
  have hTp : IsPGroup p (T.subgroupOf M) := (hc.phase.isPGroup.to_le hTR).comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp (CFSG.pCore 2 ↥M)
    (by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact fun h => hc.data.cfg.red.ne_two
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
    _ hTp
  have hEcard : Nat.card E = p ^ 2 := by
    rw [← hTcard, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hTR.trans hRM)).toEquiv]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,
      MonoidHom.subgroupMap_surjective _ _⟩)).symm
  have hEel : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨s, hs, rfl⟩⟩ := a
      obtain ⟨_, ⟨t, ht, rfl⟩⟩ := b
      change mkM s * mkM t = mkM t * mkM s
      rw [← map_mul, ← map_mul]
      exact congrArg mkM (Subtype.ext (hc.commute_of_mem_R
        (hTR (Subgroup.mem_subgroupOf.mp hs)) (hTR (Subgroup.mem_subgroupOf.mp ht))))
    · rintro _ ⟨t, ht, rfl⟩
      exact hpow _ (Subgroup.mem_subgroupOf.mp ht)
  have hEN : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hcomm _ (Subgroup.mem_subgroupOf.mp ht)
  have hE1 : E ⊓ (barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) =
      ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨⟨t, ht, rfl⟩, hxL⟩ := hx
    have h1 := hc.eq_one_of_mem_sup hB hL hBL hzbL hBC (Subgroup.mem_subgroupOf.mp ht) t.2 hxL
    have : t = 1 := Subtype.ext h1
    rw [this, map_one]
  exact hB.hOR _ (barM M L) _ hL.component hcl hpar hne hnB p hc.prime57
    (hc.perfectSectionsAltSqC_block hB.hΓ hL) E hEN hEel hEcard hE1

theorem false_main (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    (hOrb : KFactSmallOrbits) : False := by
  obtain ⟨L, hL⟩ := hc.phase.exists_weakSBlock hB.h84 hB.hD2
  have hRM := hc.phase.le_M
  have hzbL := hc.zbar_mem_block hB hL
  have hzB : z ∈ rPart M R (barM M L) := (mem_rPart hRM hc.elt.1).mpr hzbL
  obtain ⟨h1, h2⟩ := hc.inv_subgroup hOrb inf_le_left (hc.rPart_inv hB hL le_rfl)
  obtain ⟨h3, h4⟩ := hc.inv_subgroup hOrb inf_le_left
    (hc.rPart_inv hB hL (normalizer_le_normalizer_centralizer _))
  have hzC : z ∉ rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
    fun h => hc.zbar_not_mem_centralizer hL ((mem_rPart hRM hc.elt.1).mp h)
  rcases h1 with hT | hT
  · refine hc.false_of_le_rPart hB hL fun r hr => ?_
    obtain ⟨t, ht, i, rfl⟩ := hc.dec r hr
    exact Subgroup.mul_mem _ (hT ht) (Subgroup.pow_mem _ hzB i)
  · have hBz := (h2 hT).1
    rcases h3 with hTC | hTC
    · exact hc.false_of_d1LiftX_le_C hOrb hL hBz hzbL hTC
    · exact hc.false_of_rPart_C_eq_bot hB hL hBz hzbL ((h4 hTC).2 hzC)

end D1IbAltConfig

end CFSG.AGLEmbedding
