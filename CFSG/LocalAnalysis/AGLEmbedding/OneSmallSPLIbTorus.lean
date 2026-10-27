module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_torus_linTwo [Fact p.Prime] (h3 : D1PhaseThree p P M H R)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsSmallLinTwo p K) :
    ∃ φ : Multiplicative (GaloisField p 2) ≃* d1LiftX p H R K,
      ∀ μ : (GaloisField p 2)ˣ, ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p 2),
        t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a)) := by
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨T, hT, -⟩ := hd.exists_sylow
  obtain ⟨d, hdL, ⟨e₁⟩⟩ := hL
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdL
  set f : K ≃* PSL2GF p 2 := e₁.trans e₂
  have hfs : Function.Surjective (f : K →* PSL2GF p 2) := f.surjective
  set U : Sylow p (PSL2GF p 2) := T.mapSurjective hfs
  have hUT : (U : Subgroup (PSL2GF p 2)) = (T : Subgroup K).map (f : K →* PSL2GF p 2) :=
    Sylow.coe_mapSurjective hfs T
  have hTcard : Nat.card (T : Subgroup K) = p ^ 2 := by
    rw [← (psl2GF_sylow p 2 (by norm_num) U).2, hUT, Subgroup.card_map_of_injective
      (show Function.Injective (f : K →* PSL2GF p 2) from f.injective)]
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2 := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  obtain ⟨ψ, hψinj, hψrange, hc⟩ := exists_torus_param_of_mulEquiv_psl2GF hp2 (by norm_num) f
    ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) inf_le_right hcard
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hT1 : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ≠ ⊥ :=
    fun h => hd.noncyclic (by rw [h]; infer_instance)
  have hcY : ∀ μ : (GaloisField p 2)ˣ,
      ∃ c ∈ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
        ∀ a : Multiplicative (GaloisField p 2),
          c * ψ a * c⁻¹ =
            ψ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcK, hcψ⟩ := hc μ
    have hcN : c ∈ K ⊓ Subgroup.normalizer
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) :=
      ⟨hcK, by rw [← hψrange]; exact mem_normalizer_range_of_torus ψ μ.ne_zero hcψ⟩
    exact ⟨c, hN _ le_rfl hT1 hcN, hcψ⟩
  have hXH : d1LiftX p H R K ≤ H := d1LiftX_le_H p H R K
  have hXp : IsPGroup p (d1LiftX p H R K) := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hNB : GLBPrimeCore p H ≤ H ⊓ M := le_inf (glbPrimeCore_le p H) h3.primeCore_le
  have hψX : ψ.range = ((d1LiftX p H R K).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [hψrange, hd.cfg.map_d1LiftX_eq_inf]
  exact exists_torus_of_map_subgroupOf_eq hXH hXp hNB ψ hψinj hψX hcY

theorem half_succ_dvd_of_sq_sub_one_dvd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 - 1 ∣ 2 * k * (p - 1)) : (p + 1) / 2 ∣ k := by
  obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
  subst hm
  have h1 : (2 * m + 1) ^ 2 - 1 = (2 * m + 2) * (2 * m) := by
    have : (2 * m + 1) ^ 2 = (2 * m + 2) * (2 * m) + 1 := by ring
    omega
  have h2 : 2 * k * (2 * m + 1 - 1) = (2 * k) * (2 * m) := by
    congr 1
  rw [h1, h2] at h
  have hm0 : 0 < 2 * m := by
    have := hp.two_le
    omega
  have h3 : 2 * m + 2 ∣ 2 * k := Nat.dvd_of_mul_dvd_mul_right hm0 h
  have h4 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [h4]
  have h5 : 2 * (m + 1) ∣ 2 * k := by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    exact h3
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h5

theorem D1OneSmallData.exists_irr_linTwo_period [Fact p.Prime] (h3 : D1PhaseThree p P M H R)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsSmallLinTwo p K) :
    ∃ t : G, t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer ((d1LiftX p H R K : Subgroup G) : Set G) ∧
      ∀ k : ℕ, ¬ (p + 1) / 2 ∣ k → ∀ Y : Subgroup G, Y ≤ d1LiftX p H R K →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = d1LiftX p H R K := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨φ, htor⟩ := hd.exists_torus_linTwo h3 hL
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField p 2)ˣ)
  have hcardU : Nat.card (GaloisField p 2)ˣ = p ^ 2 - 1 := by
    rw [Nat.card_units, GaloisField.card p 2 (by norm_num)]
  obtain ⟨t, htK, ht⟩ := htor μ
  set c : GaloisField p 2 := (μ : GaloisField p 2) ^ 2 with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Units.ne_zero μ)
  refine ⟨t, htK, mem_normalizer_of_torus_conj φ hc0 ht, fun k hk Y hYX hY => ?_⟩
  have htk := conj_pow_of_torus_conj φ ht k
  refine eq_bot_or_eq_of_torus_conj' (by norm_num) φ (γ := c ^ k) (fun d hd0 hd2 h => ?_)
    (pow_ne_zero _ hc0) htk hYX hY
  have hd1 : d = 1 := by omega
  subst hd1
  apply hk
  have h1 : μ ^ (2 * k * (p - 1)) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have e : (c ^ k) ^ (p ^ 1 - 1) = (μ : GaloisField p 2) ^ (2 * k * (p - 1)) := by
      rw [hc, pow_one, ← pow_mul, ← pow_mul, mul_assoc]
    rw [← e]
    exact h
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hμ, hcardU] at h2
  exact half_succ_dvd_of_sq_sub_one_dvd hp hp2 h2

end CFSG.AGLEmbedding
