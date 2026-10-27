module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltSections
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVZCore
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltPerm
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltUnique
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem barM_R (hc : D1IbAltConfig p P M H R Rbar K z) :
    IsElemAbelian p (barM M R) ∧ Nat.card (barM M R) = p ^ 3 :=
  hc.toZCore.barM_R

theorem barM_T (hc : D1IbAltConfig p P M H R Rbar K z) :
    IsElemAbelian p (barM M (d1LiftX p H R K)) ∧ Nat.card (barM M (d1LiftX p H R K)) = p ^ 2 := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨hTcard, -⟩ := hc.card_d1LiftX
  set T := d1LiftX p H R K
  have hRM := hc.phase.le_M
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hTp : IsPGroup p (T.subgroupOf M) := (hc.phase.isPGroup.to_le hTR).comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp (CFSG.pCore 2 ↥M)
    (by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact fun h => hc.data.cfg.red.ne_two
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
    _ hTp
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨s, hs, rfl⟩⟩ := a
    obtain ⟨_, ⟨t, ht, rfl⟩⟩ := b
    change mkM s * mkM t = mkM t * mkM s
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext (hc.commute_of_mem_R
      (hTR (Subgroup.mem_subgroupOf.mp hs)) (hTR (Subgroup.mem_subgroupOf.mp ht))))
  · rintro _ ⟨t, ht, rfl⟩
    have : t ^ p = 1 := Subtype.ext (by simpa using hc.exp t (hTR (Subgroup.mem_subgroupOf.mp ht)))
    rw [← map_pow, this, map_one]
  · rw [← hTcard, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hTR.trans hRM)).toEquiv]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,
      MonoidHom.subgroupMap_surjective _ _⟩)).symm

theorem exists_perfect_T (hc : D1IbAltConfig p P M H R Rbar K z) (hΓS : KFactAltTwoPGammaSylow) :
    ∃ W : Subgroup G, W ≤ H ⊓ M ∧ ⁅W, W⁆ = W ∧ W ≤ Subgroup.centralizer ({z} : Set G) ∧
      d1LiftX p H R K ≤ W := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, -⟩ := hc.data.exists_sylow
  set Γ := GLBCore p 1 (T₁ : Subgroup K)
  have hKX := hc.inf_d1X0_eq hT₁
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set Pc := (perfectCore Γ).map K.subtype
  have hPcX : Pc ≤ K ⊓ d1X0 p M H := by rw [hKX]; exact Subgroup.map_mono (perfectCore_le Γ)
  have hPcp : ⁅Pc, Pc⁆ = Pc := by rw [← Subgroup.map_commutator, perfectCore_perfect Γ]
  have hTPc : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ≤ Pc := by
    rw [← hT₁]
    exact Subgroup.map_mono (hΓS (↥K) p hp hc.five_le hc.alt T₁)
  set Y : Subgroup G := (Pc.comap π).map H.subtype ⊓ M ⊓ Subgroup.centralizer ({z} : Set G)
  have hYH : Y ≤ H := inf_le_left.trans (inf_le_left.trans (Subgroup.map_subtype_le _))
  set W := perfectCore Y
  have hWY : W ≤ Y := perfectCore_le Y
  set ψ := π.comp (Subgroup.inclusion hYH)
  have hmemY : ∀ g : G, ∀ hgH : g ∈ H, π ⟨g, hgH⟩ ∈ Pc → g ∈ M → g * z = z * g → g ∈ Y :=
    fun g hgH hgPc hgM hgz => ⟨⟨⟨⟨g, hgH⟩, hgPc, rfl⟩, hgM⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩
  have hrange : ψ.range = Pc := by
    refine le_antisymm ?_ fun γ hγ => ?_
    · rintro _ ⟨⟨y, ⟨⟨⟨h, hh, rfl⟩, -⟩, -⟩⟩, rfl⟩
      exact hh
    · have hγK := (hPcX hγ).1
      have hγz : γ * π ⟨z, hc.elt.2.2.1⟩ = π ⟨z, hc.elt.2.2.1⟩ * γ :=
        Subgroup.mem_centralizer_iff.mp hc.elt.2.2.2 γ hγK
      obtain ⟨g, hgA, hgz, hgH, hgγ⟩ := hc.exists_lift_centralizer (hPcX hγ).2 hγz
      exact ⟨⟨g, hmemY g hgH (hgγ ▸ hγ) hgA.2 hgz⟩, hgγ⟩
  have hW : (perfectCore (⊤ : Subgroup ↥Y)).map ψ = Pc := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, hrange]
    exact perfectCore_eq_self_of_perfect hPcp
  have hWU : (perfectCore (⊤ : Subgroup ↥Y)).map Y.subtype = W := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨W, hWY.trans (le_inf hYH (inf_le_left.trans inf_le_right)), perfectCore_perfect Y,
    hWY.trans inf_le_right, fun t ht => ?_⟩
  obtain ⟨h, ⟨hhR, hhK⟩, rfl⟩ := ht
  have htR : (h : G) ∈ R := hhR
  have hπR : π h ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hc.data.cfg.rbar]
    exact ⟨h, hhR, rfl⟩
  have htY : (h : G) ∈ Y := hmemY h h.2 (hTPc ⟨hπR, hhK⟩) (hc.phase.le_M htR)
    (Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer htR))
  have hπt : π h ∈ (perfectCore (⊤ : Subgroup ↥Y)).map ψ := by
    rw [hW]
    exact hTPc ⟨hπR, hhK⟩
  obtain ⟨w', hw'W, hw'z⟩ := hπt
  have hwW : (w' : G) ∈ W := hWU ▸ ⟨w', hw'W, rfl⟩
  set n : ↥Y := w'⁻¹ * ⟨h, htY⟩
  have hn : p.Coprime (orderOf n) := by
    have h1 : ψ n = 1 := by
      rw [map_mul, map_inv, hw'z]
      exact inv_mul_cancel _
    have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have h3 : orderOf (Subgroup.inclusion hYH n) ∣ Nat.card (GLBPrimeCore p H) := by
      have := Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H)
        (x := (Subgroup.inclusion hYH n : G)) h2
      rwa [Subgroup.orderOf_coe] at this
    rw [orderOf_injective _ (Subgroup.inclusion_injective hYH)] at h3
    exact (glbPrimeCore_coprime p H).coprime_dvd_right h3
  have hUn : (W.subgroupOf Y).Normal := perfectCore_normal Y
  set q := QuotientGroup.mk' (W.subgroupOf Y)
  have hqw : q w' = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwW)
  have hqz : q ⟨h, htY⟩ = q n := by
    rw [show n = w'⁻¹ * ⟨h, htY⟩ from rfl, map_mul, map_inv, hqw, inv_one, one_mul]
  have htp : (⟨h, htY⟩ : ↥Y) ^ p = 1 := Subtype.ext (by simpa using hc.exp _ htR)
  have h1 : orderOf (q ⟨h, htY⟩) ∣ p := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, htp, map_one]
  have h2 : orderOf (q ⟨h, htY⟩) ∣ orderOf n := hqz ▸ orderOf_map_dvd q n
  have h3 : orderOf (q ⟨h, htY⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hn) h2
  have h4 : ⟨h, htY⟩ ∈ W.subgroupOf Y :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  exact Subgroup.mem_subgroupOf.mp h4

theorem false_of_le_rPart (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hR : R ≤ rPart M R (barM M L)) :
    False := by
  have hp := hc.prime
  have hp5 := hc.five_le
  have hRM := hc.phase.le_M
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set zb := mkM ⟨z, hc.mem_M⟩
  set E := barM M R
  set PL := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)
  obtain ⟨hEel, hEcard⟩ := hc.barM_R
  have hEL : E ≤ barM M L := by
    rintro _ ⟨r, hr, rfl⟩
    exact (mem_rPart hRM (Subgroup.mem_subgroupOf.mp hr)).mp (hR (Subgroup.mem_subgroupOf.mp hr))
  have hzbL : zb ∈ barM M L := (mem_rPart hRM hc.elt.1).mp (hR hc.elt.1)
  have hEC : E ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hc.le_centralizer (Subgroup.mem_subgroupOf.mp hr))))
  have hEP : E ≤ PL := fun e he => hc.zbar_fixed_le L e (hEL he) (by
    show zb * e * zb⁻¹ = e
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEC he), mul_inv_cancel_right])
  have hPLs := hc.perfectSectionsAltSqC_block hB.hΓ hL
  have hdvdP : p ^ 3 ∣ Nat.card PL := hEcard ▸ Subgroup.card_dvd_of_le hEP
  have hdvdL : p ^ 3 ∣ Nat.card (barM M L) := hEcard ▸ Subgroup.card_dvd_of_le hEL
  have hn1 := hc.phase.nineThree_not_one hB.h85 hB.hD2 hL
  rcases hc.phase.nineThree hB.h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · obtain ⟨W, hWHM, hWp, hWz, hTW⟩ := hc.exists_perfect_T hB.hΓS
    obtain ⟨hFel, hFcard⟩ := hc.barM_T
    have hWM : W ≤ M := hWHM.trans inf_le_right
    have hWbp : ⁅barM M W, barM M W⁆ = barM M W := by
      have h1 : ⁅W.subgroupOf M, W.subgroupOf M⁆ = W.subgroupOf M := by
        apply Subgroup.map_injective M.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hWM, hWp]
      change ⁅(W.subgroupOf M).map mkM, (W.subgroupOf M).map mkM⁆ = (W.subgroupOf M).map mkM
      rw [← Subgroup.map_commutator, h1]
    have hWbC : barM M W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg mkM (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
        (hWz (Subgroup.mem_subgroupOf.mp hw))))
    have hWbN : barM M W ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      fun w hw => hc.mem_normalizer_of_commute hB hL (Subgroup.mem_centralizer_singleton_iff.mp
        (hWbC hw))
    have hFW : barM M (d1LiftX p H R K) ≤ barM M W := barM_mono hTW
    have hFL : barM M (d1LiftX p H R K) ≤ barM M L :=
      (barM_mono (d1LiftX_le p H R K)).trans hEL
    exact hB.hTA _ (barM M L) PL hL.component h2.1 h2.2.1 (hc.phase.barM_ne_of_isWeakSBlock hL)
      (ne_inf_normalizer_of_nineThreeTwo h2 (hn1.2 h2)) p hc.prime57 hPLs zb hzbL hc.zbar_pow
      (hc.zbar_not_mem_centralizer hL) (hc.zbar_fixed_le L) (barM M W) hWbp hWbN hWbC
      ⟨barM M (d1LiftX p H R K), le_inf hFW hFL, hFel, hFcard⟩
  · exact hB.hC3T G M (pCoreOf 2 H) L p hc.phase.isKGroup.1 hc.phase.asc81bHyp hL hn1.1
      (hc.phase.not_isSylowTwoOf_inf hB.h85 hB.hD2 hL) h3 hc.prime57 hPLs E hEP hEel hEcard
  · obtain ⟨-, hZ, ⟨e⟩, -⟩ := h4
    have hcard : Nat.card (barM M L) = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L)), hZ,
        Nat.card_congr e.toEquiv]
      have := two_mul_card_alternatingGroup_fin (n := 6) (by norm_num)
      rw [show Nat.factorial 6 = 720 by rfl] at this
      omega
    exact (not_pow_three_dvd_of_five_le hp hp5).1 (hcard ▸ hdvdL)
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    have hcard : Nat.card (barM M L) = 2520 := by
      rw [Nat.card_congr e.toEquiv]
      have := two_mul_card_alternatingGroup_fin (n := 7) (by norm_num)
      rw [show Nat.factorial 7 = 5040 by rfl] at this
      omega
    exact (not_pow_three_dvd_of_five_le hp hp5).2 (hcard ▸ hdvdL)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact false_of_quotient_perm_C hp hc.prime57 hPLs e hdvdP
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact false_of_quotient_perm_C hp hc.prime57 hPLs e hdvdP
  · obtain ⟨-, N, r, -, -, -, -, -, -, φ, -⟩ := h8
    exact false_of_quotient_perm_prod_C hp hc.prime57 hPLs φ hdvdP

end D1IbAltConfig

end CFSG.AGLEmbedding
