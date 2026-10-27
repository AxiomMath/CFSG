module

import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem mem_of_mul_inv_mem_of_coprime {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal]
    {p : ℕ} (hp : p.Prime) {t n : Γ} {k : ℕ} (ht : t ^ p ^ k = 1) (hn : p.Coprime (orderOf n))
    (htn : t * n⁻¹ ∈ N) : t ∈ N := by
  set q := QuotientGroup.mk' N
  have hq : q t = q n := by
    have h1 : q (t * n⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr htn
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have h1 : orderOf (q t) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, ht, map_one])
  have h2 : orderOf (q t) ∣ orderOf n := hq ▸ orderOf_map_dvd q n
  have h3 : orderOf (q t) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
    rcases j with _ | j
    · simpa using hj
    · exfalso
      have hpd : p ∣ orderOf (q t) := by rw [hj, pow_succ]; exact Dvd.intro_left _ rfl
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hn (hpd.trans h2)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff t).mp h3

theorem ReducedNongeneration.exists_sylow_facts_of_not_mem {p : ℕ} {X : Type} [Group X]
    [Finite X] {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) (hβ : KFactBeta) :
    Subgroup.center K = ⊥ ∧ IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∧
      ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) ∧
      ∃ T : Sylow p K, (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K ∧
        ¬ IsCyclic (T : Subgroup K) ∧ GLBCore p 1 (T : Subgroup K) ≠ ⊤ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZ, -, hfacts⟩ := h.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
  obtain ⟨hsimple, hnonab, hcat, hAut, -⟩ :=
    h.exists_sylow_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hTc => by
    have := pRank_mulAut_le_two_of_kOutRankLeOne hp hZ
      (fun B hB => card_le_of_isElemAbelian_of_isCyclic_sylow T hTc hB) hfacts.1
    omega
  have hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) := fun hc => hTnc (by
    rw [← hT] at hc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm (MulEquiv.surjective _))
  obtain ⟨hN, hKX₀⟩ := (h.center_eq_bot_and_rankOne_of_not_mem hz hzp hK hzK).2 hnc
  exact ⟨hZ, hsimple, hnonab, hcat, by omega, hnc, T, hT, hTnc,
    h.glbCore_ne_top_of_rankOne hN hKX₀ hT⟩

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.mk_mem_comp_of_mem_d1LiftX (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)}
    {KC : Subgroup (D1CzQuot p z)} (hRC : D1ReducedCentralizer p P' M z Pbar KC)
    (hSch : KFactCatalogSchreier) {x : G} (hx : x ∈ d1LiftX p H R K)
    (hxC : x ∈ Subgroup.centralizer ({z} : Set G)) :
    QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
      ⟨x, hxC⟩ ∈ KC := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := primeComplementCore_coprime (G := H) p
  obtain ⟨-, hzp, hzH, hzC⟩ := hz
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set W : Subgroup G := C ⊓ (K.comap π).map H.subtype with hW
  have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ C := inf_le_left
  have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ K := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set φ : W →* K := (π.comp (Subgroup.inclusion hWH)).codRestrict K hφ₀ with hφdef
  have hzH' : orderOf (⟨z, hzH⟩ : H) = p := (Subgroup.orderOf_coe _).symm.trans hzp
  have hφs : Function.Surjective φ := by
    intro k
    obtain ⟨g, hg, hgk⟩ := exists_mem_centralizer_mk_eq hp _ hO
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzH', pow_one]))
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzC k k.2))
    have hgC : (g : G) ∈ C :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have hgK : g ∈ K.comap π := by
      rw [Subgroup.mem_comap, hgk]
      exact k.2
    exact ⟨⟨g, hgC, g, hgK, rfl⟩, Subtype.ext hgk⟩
  obtain ⟨x', ⟨hx'R, hx'K⟩, rfl⟩ := hx
  have hxW : (x' : G) ∈ W := ⟨hxC, x', hx'K, rfl⟩
  set D : Subgroup W := perfectCore (⊤ : Subgroup W) with hD
  have hDperf : ⁅D, D⁆ = D := perfectCore_perfect _
  have hKperf : Group.IsPerfect K := ⟨hd.comp.2.2.1⟩
  have hDφ : D.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφs]
    exact perfectCore_eq_self_of_perfect
      (by rw [← commutator_def]; exact hKperf.commutator_eq_top)
  have hDn : D.Normal := by
    have h1 := perfectCore_normal (⊤ : Subgroup W)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le _)] at h1
    exact (Subgroup.normalizer_eq_top_iff).mp (top_le_iff.mp h1)
  obtain ⟨d, hdD, hdφ⟩ : φ ⟨x', hxW⟩ ∈ D.map φ := hDφ ▸ Subgroup.mem_top _
  have hxD : (⟨x', hxW⟩ : W) ∈ D := by
    have hRp : IsPGroup p R := hd.cfg.ext.isPGroup
    obtain ⟨k, hk⟩ := hRp ⟨x', hx'R⟩
    have hk' : (⟨(x' : G), hxW⟩ : W) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hn : φ (d⁻¹ * ⟨x', hxW⟩) = 1 := by rw [map_mul, map_inv, hdφ, inv_mul_cancel]
    have hn' : π (Subgroup.inclusion hWH (d⁻¹ * ⟨x', hxW⟩)) = 1 := congrArg Subtype.val hn
    have hcop : p.Coprime (orderOf (d⁻¹ * ⟨(x' : G), hxW⟩)) := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hn'
      have h2 := Subgroup.orderOf_dvd_natCard _ hn'
      rw [orderOf_injective _ (Subgroup.inclusion_injective hWH)] at h2
      exact hO.coprime_dvd_right h2
    refine mem_of_mul_inv_mem_of_coprime hp hk' hcop ?_
    simpa [mul_assoc] using hdD
  set ρ : W →* D1CzQuot p z := (QuotientGroup.mk' _).comp (Subgroup.inclusion hWC) with hρ
  have hDK : D.map ρ ≤ KC := hRC.le_of_isPerfect hSch
    (Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDperf]))
  exact hDK ⟨_, hxD, rfl⟩

theorem D1OneSmallData.mem_of_mem_inf (hd : D1OneSmallData p P M H R Rbar K) {P' : Subgroup G}
    (hP' : IsPGroup p P') (hRP' : R ≤ P') {t : G} (htP : t ∈ P') (htH : t ∈ H) : t ∈ R := by
  obtain ⟨T₀, hT₀⟩ := hd.cfg.ext.isSylow
  have hle : (T₀ : Subgroup H) ≤ (P' ⊓ H).subgroupOf H := by
    intro x hx
    have hxR : (x : G) ∈ R := hT₀ ▸ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨hRP' hxR, x.2⟩
  have heq := T₀.is_maximal' ((hP'.to_le inf_le_left).comap_subtype) hle
  have hmem : (⟨t, htH⟩ : H) ∈ Subgroup.comap H.subtype (P' ⊓ H) := ⟨htP, htH⟩
  rw [heq] at hmem
  exact hT₀ ▸ ⟨_, hmem, rfl⟩

end Config

end CFSG.AGLEmbedding
