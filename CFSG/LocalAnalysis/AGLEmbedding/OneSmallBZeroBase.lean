module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem twoCore_inf_centralizer_le_of_conj {p : ℕ} (hp : p.Prime) {M R : Subgroup G} {z n w : G}
    (hzp : orderOf z = p) (hnM : n ∈ M) (hnR : n ∈ Subgroup.normalizer (R : Set G))
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G))
    (hw : w ∈ Subgroup.zpowers (n * z * n⁻¹)) (hw1 : w ≠ 1) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({w} : Set G) ≤ Subgroup.centralizer (R : Set G) := by
  intro u hu
  have hnzo : orderOf (n * z * n⁻¹) = p := by
    have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
    rw [← hzp, ← this]
    rfl
  have hnz := mem_zpowers_of_mem_zpowers_of_prime hp hnzo hw hw1
  have huw : u * w = w * u := Subgroup.mem_centralizer_singleton_iff.mp hu.2
  have hunz : Commute u (n * z * n⁻¹) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hnz
    rw [← hj]
    exact Commute.zpow_right (show Commute u w from huw) j
  have hv : n⁻¹ * u * n ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M
        (M.inv_mem hnM)) u).mp hu.1
      simpa using this
    · show n⁻¹ * u * n ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hunz.eq
      calc n⁻¹ * u * n * z = n⁻¹ * (u * (n * z * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * z * n⁻¹) * u) * n := by rw [h1]
        _ = z * (n⁻¹ * u * n) := by group
  have hvR := hQz hv
  rw [Subgroup.mem_centralizer_iff] at hvR ⊢
  intro r hr
  have hr' : n⁻¹ * r * n ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnR) r).mp hr
    simpa using this
  have h1 := hvR _ hr'
  calc r * u = n * ((n⁻¹ * r * n) * (n⁻¹ * u * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * u * n) * (n⁻¹ * r * n)) * n⁻¹ := by rw [h1]
    _ = u * r := by group

section Config

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.inf_centralizer_le_of_b0 (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hB0 : D1CzB0 p R z) :
    (P : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G) ≤ R := by
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  obtain ⟨Q, hQ⟩ := hB0
  have hQle : (Q : Subgroup (Subgroup.centralizer ({z} : Set G))) ≤
      ((P : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf
        (Subgroup.centralizer ({z} : Set G)) := by
    intro q hq
    have hqR : (q : G) ∈ R := hQ ▸ ⟨q, hq, rfl⟩
    exact ⟨hd.cfg.ext.le_P hqR, q.2⟩
  have heq := Q.is_maximal' ((P.isPGroup'.to_le inf_le_left).comap_subtype) hQle
  intro x hx
  have hx' : (⟨x, hx.2⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      (Q : Subgroup (Subgroup.centralizer ({z} : Set G))) := by
    rw [← heq]
    exact hx
  exact hQ ▸ ⟨_, hx', rfl⟩

theorem D1OneSmallData.exists_moving_elt (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) :
    ∃ x ∈ (P : Subgroup G), x ∈ Subgroup.normalizer (R : Set G) ∧ x ∉ R ∧
      x * z * x⁻¹ ∉ Subgroup.zpowers z := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPR : (P : Subgroup G) ≠ R := by
    intro h
    have h4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
    rw [h, hd.pRank_R] at h4
    omega
  obtain ⟨x, hxP, hxN, hxR⟩ : ∃ x ∈ (P : Subgroup G), x ∈ Subgroup.normalizer (R : Set G) ∧
      x ∉ R := by
    by_contra h
    push Not at h
    exact hPR (eq_of_isPGroup_of_le_of_normalizer P.isPGroup' hd.cfg.ext.le_P h)
  refine ⟨x, hxP, hxN, hxR, fun hxz => hxR ?_⟩
  have hxzN : x ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hxz n
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hc := commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hz.2.1 hxzN hxk
  exact hd.inf_centralizer_le_of_b0 hB0
    ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hc.eq⟩

theorem D1OneSmallData.mem_of_mem_normalizer_of_commute (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hB0 : D1CzB0 p R z) {y : G}
    (hyN : y ∈ Subgroup.normalizer (R : Set G)) (hyz : y * z = z * y) {k : ℕ}
    (hyk : y ^ p ^ k = 1) : y ∈ R := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := hB0
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hyk)
    exact ⟨j, hj⟩
  have hS : IsPGroup p (R ⊔ Subgroup.zpowers y : Subgroup G) :=
    hd.cfg.ext.isPGroup.to_sup_of_normal_left' hyp (Subgroup.zpowers_le.mpr hyN)
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have hQle : (Q : Subgroup (Subgroup.centralizer ({z} : Set G))) ≤
      (R ⊔ Subgroup.zpowers y).subgroupOf (Subgroup.centralizer ({z} : Set G)) := by
    intro q hq
    have hqR : (q : G) ∈ R := hQ ▸ ⟨q, hq, rfl⟩
    exact Subgroup.mem_sup_left hqR
  have heq := Q.is_maximal' (hS.comap_subtype) hQle
  have hy : (⟨y, hyC⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      (Q : Subgroup (Subgroup.centralizer ({z} : Set G))) := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  exact hQ ▸ ⟨_, hy, rfl⟩

end Config

end CFSG.AGLEmbedding
