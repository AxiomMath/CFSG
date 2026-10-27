module

public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree glbPrimeCore_le glbPrimeCore_normal
  glbPrimeCore_coprime le_normalizer_glbPrimeCore
  exists_mem_inv_mul_mem_normalizer_of_not_dvd_index)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem _root_.CFSG.AGLEmbedding.D1Extremal.toPhaseThree3 (hS : Setting G)
    (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    D1PhaseThree p P M H R :=
  { h.toD1Escape with
    glob := hS.toU.toAGLGlobal
    twoCore_inf := h.toD1Escape.twoCore_inf_eq_of_hasPrimeConstraint hcon }

theorem _root_.CFSG.AGLEmbedding.D1Escape.not_dvd_index_R (h : D1Escape p P M H R) :
    ¬ p ∣ (R.subgroupOf H).index := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := h.isSylow
  have hsub : R.subgroupOf H = (T : Subgroup H) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [hsub]
  exact T.not_dvd_index

theorem _root_.CFSG.AGLEmbedding.D1Extremal.exists_invariantSylowTwo (hS : Setting G)
    (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ T : Subgroup G, T ≤ GLBPrimeCore p H ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index ∧
      R ≤ Subgroup.normalizer (T : Set G) ∧ pCoreOf 2 H ≤ T :=
  (h.toPhaseThree3 hS hcon).exists_sylowTwo_primeCore

theorem mem_primeCore_mul_normalizer {T : Subgroup G} (hTN : T ≤ GLBPrimeCore p H)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf (GLBPrimeCore p H)).index) {x : G}
    (hx : x ∈ H) :
    ∃ n ∈ GLBPrimeCore p H, ∃ m ∈ H, m ∈ Subgroup.normalizer (T : Set G) ∧ x = n * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, hlx⟩ := exists_mem_inv_mul_mem_normalizer_of_not_dvd_index (p := 2) hTN hT2 hTidx
    (le_normalizer_glbPrimeCore p H hx)
  exact ⟨l, hl, l⁻¹ * x, H.mul_mem (H.inv_mem (glbPrimeCore_le p H hl)) hx, hlx, by group⟩

theorem _root_.CFSG.AGLEmbedding.D1Escape.exists_mul_normalizer_zpowers
    (h : D1Escape p P M H R) (hcon : HasPrimeConstraint (G := H) p) {z : G} (hzR : z ∈ R)
    (hzc : z ∈ Subgroup.centralizer (R : Set G)) (hzp : orderOf z = p) :
    ∀ g ∈ H, ∃ n ∈ GLBPrimeCore p H, ∃ v ∈ H,
      v ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) ∧ g = n * v := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Rbar, hRbar, hred⟩ := h.reducedNongeneration
  obtain ⟨Q, hQn, hQp, hQc⟩ := hcon
  have : Q.Normal := hQn
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) :=
    primeComplementCore_coprime p
  let zH : H := ⟨z, h.le_H hzR⟩
  have hzHp : orderOf zH = p := (Subgroup.orderOf_coe zH).symm.trans hzp
  have hzbar : QuotientGroup.mk' (primeComplementCore p) zH ∈
      Subgroup.centralizer (Q : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' := hQp.le_sylow_of_normal Rbar hq
    rw [hRbar] at hq'
    obtain ⟨r, hr, rfl⟩ := hq'
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc r hr))
  have hRp : IsPGroup p (R.subgroupOf H) := h.isPGroup.comap_subtype
  have hzbarp : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) zH) = p := by
    refine orderOf_eq_prime (by rw [← map_pow, ← hzHp, pow_orderOf_eq_one, map_one]) ?_
    intro h1
    have hzO : zH ∈ R.subgroupOf H ⊓ primeComplementCore p :=
      ⟨hzR, by rwa [← QuotientGroup.ker_mk' (primeComplementCore (G := H) p)]⟩
    rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hRp hO, Subgroup.mem_bot] at hzO
    rw [hzO, orderOf_one] at hzHp
    exact hp.one_lt.ne hzHp
  have hnormal := CFSG.AGLEmbedding.zpowers_normal_of_mem_centralizer hQc
    (fun A hA hAe => by
      have := hA
      exact hred.card_le_of_normal_isElemAbelian hAe) hzbar hzbarp
  have hZp : IsPGroup p (Subgroup.zpowers zH) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzHp, pow_one])
  have hfr := CFSG.AGLEmbedding.comap_normalizer_map_le_sup hp _ hO hZp
  rw [MonoidHom.map_zpowers, Subgroup.normalizer_eq_top_iff.mpr hnormal,
    Subgroup.comap_top] at hfr
  intro g hg
  have hy : (⟨g, hg⟩ : H) ∈ ((primeComplementCore (G := H) p ⊔
      Subgroup.normalizer (Subgroup.zpowers zH : Set H) : Subgroup H) : Set H) :=
    hfr (Subgroup.mem_top _)
  rw [Subgroup.normal_mul, Set.mem_mul] at hy
  obtain ⟨n, hn, v, hv, hnv⟩ := hy
  refine ⟨(n : G), ?_, (v : G), v.2, ?_, ?_⟩
  · have hn' : n ∈ (GLBPrimeCore p H).subgroupOf H := by
      rw [CFSG.AGLEmbedding.glbPrimeCore_subgroupOf]
      exact hn
    exact hn'
  · have hmem := Subgroup.le_normalizer_map H.subtype ⟨v, hv, rfl⟩
    rwa [MonoidHom.map_zpowers] at hmem
  · exact (congrArg Subtype.val hnv).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
