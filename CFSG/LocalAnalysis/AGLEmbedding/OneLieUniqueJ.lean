module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Conj

variable {G : Type} [Group G] [Finite G]

theorem glbWeakCore_map_conj {p : ℕ} (hp : p.Prime) (P : Subgroup G) (g : G) :
    GLBWeakCore p (P.map (MulAut.conj g).toMonoidHom) =
      (GLBWeakCore p P).map (MulAut.conj g).toMonoidHom := by
  set σ := MulAut.conj g
  refine le_antisymm ?_ (map_glbWeakCore_le hp σ.toMonoidHom σ.injective P)
  have h := map_glbWeakCore_le hp σ.symm.toMonoidHom σ.symm.injective (P.map σ.toMonoidHom)
  rw [map_automorphism_symm_map] at h
  have hback : ((GLBWeakCore p (P.map σ.toMonoidHom)).map σ.symm.toMonoidHom).map
      σ.toMonoidHom = GLBWeakCore p (P.map σ.toMonoidHom) := by
    simpa only [MulEquiv.symm_symm] using map_automorphism_symm_map _ σ.symm
  rw [← hback]
  exact Subgroup.map_mono h

omit [Finite G] in
theorem coe_smul_sylow_eq_map_conj {p : ℕ} (P : Sylow p G) (m : G) :
    ((m • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem glbWeakCore_smul_le {p : ℕ} (hp : p.Prime) {P : Sylow p G} {M : Subgroup G}
    (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) {m : G} (hm : m ∈ M) :
    GLBWeakCore p ((m • P : Sylow p G) : Subgroup G) ≤ M := by
  rw [coe_smul_sylow_eq_map_conj, glbWeakCore_map_conj hp]
  rintro _ ⟨x, hx, rfl⟩
  exact M.mul_mem (M.mul_mem hm (hcore hx)) (M.inv_mem hm)

theorem D1LocalU.conj {p : ℕ} {P : Sylow p G} {M : Subgroup G} (h : D1LocalU p P M) {m : G}
    (hm : m ∈ M) : D1LocalU p (m • P) M where
  sigma := h.sigma
  maxLocal := h.maxLocal
  core := glbWeakCore_smul_le h.prime h.core hm

end Conj

section Rank

theorem OneLieTorusFacts.three_le_pRank {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {T : Sylow p K} {n e : ℕ} (hTF : OneLieTorusFacts p K T n e) :
    3 ≤ Open.pRank p (T : Subgroup K) := by
  have hp : p.Prime := Fact.out
  obtain ⟨ψ, hψinj, hψrange, -⟩ := hTF.torus
  have hn2 := hTF.two_le
  set Z : Subgroup K := (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)
    with hZdef
  have hZT : Z ≤ T := inf_le_left
  have hZel : IsElemAbelian p Z := by
    rw [← hψrange]
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha', ← hb', ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨a, rfl⟩ := hx
      have hap : a ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rw [← map_pow, hap, map_one]
  have hZcard : Nat.card Z = p ^ n := by
    rw [← hψrange, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, GaloisField.card p n (by omega)]
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · obtain ⟨hTcard, -, hexp, -⟩ := hTF.pair rfl
    have hZlt : Z < T := by
      refine lt_of_le_of_ne hZT fun heq => ?_
      have hc : Nat.card Z = Nat.card (T : Subgroup K) := by rw [heq]
      rw [hZcard, hTcard] at hc
      exact absurd (Nat.pow_right_injective hp.two_le hc) (by norm_num)
    obtain ⟨t, htT, htZ⟩ := IsConcreteLE.exists_of_lt hZlt
    have ht1 : t ≠ 1 := fun h => htZ (h ▸ Z.one_mem)
    have htC : t ∈ Subgroup.centralizer (Z : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Subgroup.mem_centralizer_iff.mp hz.2) t htT).symm
    exact three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hZel hZcard
      (orderOf_eq_prime (hexp t htT) ht1) htZ htC hZT htT
  · exact hn3.trans ((le_csSup (pRank_bddAbove p hp Z) ⟨Z, le_rfl, hZel, hZcard⟩).trans
      (PreuniquenessRankFour.Helpers.pRank_mono p hp hZT))

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.exists_torusFacts [Fact p.Prime] (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧
      ∃ n e : ℕ, OneLieTorusFacts p K T₁ n e := by
  obtain ⟨hsimple, hnonab⟩ := hd.isSimpleGroup
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hd.cfg.catalog.isCatalogGroup_center_quotient hd.comp)
  obtain ⟨T, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hd.noncyclic (by
    rw [← hT₁]
    exact isCyclic_of_surjective _ (K.subtype.subgroupMap_surjective (T : Subgroup K)))
  exact ⟨T, hT₁, hT K hsimple hnonab hcat p hd.cfg.red.ne_two T hTnc
    (hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT₁) hd.big⟩

theorem D1OneLieData.three_le_pRank_d1LiftX (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) : 3 ≤ Open.pRank p (d1LiftX p H R K) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, n, e, hTF⟩ := hd.exists_torusFacts hT
  have h3 := hTF.three_le_pRank
  rw [← pRank_map_of_injective p hp K.subtype K.subtype_injective (T₁ : Subgroup K), hT₁,
    ← hd.cfg.map_d1LiftX_eq_inf, pRank_map_mk_eq_pRank_map_subtype hp _
      (primeComplementCore_coprime p),
    Subgroup.map_subgroupOf_eq_of_le (d1LiftX_le_H p H R K)] at h3
  exact h3

end Rank

end CFSG.AGLEmbedding
