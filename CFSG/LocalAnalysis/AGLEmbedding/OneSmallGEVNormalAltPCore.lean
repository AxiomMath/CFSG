module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVAltLambdaCore
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem exists_conj_mem_rbar (hc : D1SmallAltConfig p P M H R Rbar K z)
    {x : H ⧸ primeComplementCore (G := H) p} {k : ℕ} (hx : x ^ p ^ k = 1) :
    ∃ g : H ⧸ primeComplementCore (G := H) p,
      g⁻¹ * x * g ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
  have : Fact p.Prime := ⟨hc.prime⟩
  exact exists_conj_mem_sylow_of_pow_eq_one Rbar hx

theorem pow_eq_one_of_pow (hc : D1SmallAltConfig p P M H R Rbar K z)
    {x : H ⧸ primeComplementCore (G := H) p} {k : ℕ} (hx : x ^ p ^ k = 1) : x ^ p = 1 := by
  obtain ⟨g, hg⟩ := hc.exists_conj_mem_rbar hx
  rw [hc.data.cfg.rbar] at hg
  obtain ⟨r, hr, hrg⟩ := hg
  have h1 : (g⁻¹ * x * g) ^ p = 1 := by
    rw [← hrg, ← map_pow]
    have : r ^ p = 1 := Subtype.ext (by simpa using hc.exp r (Subgroup.mem_subgroupOf.mp hr))
    rw [this, map_one]
  have h2 : (g⁻¹ * x * g) ^ p = g⁻¹ * x ^ p * g := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  rw [h2] at h1
  calc x ^ p = g * (g⁻¹ * x ^ p * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem mem_sup_of_pow (hc : D1SmallAltConfig p P M H R Rbar K z)
    {x : H ⧸ primeComplementCore (G := H) p} {k : ℕ} (hx : x ^ p ^ k = 1) :
    x ∈ K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have : Fact p.Prime := ⟨hc.prime⟩
  exact mem_sup_centralizer_of_pow_eq_one hc.normal_K hc.rbar_le hx

theorem orderOf_zH (hc : D1SmallAltConfig p P M H R Rbar K z) :
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

theorem le_zpowers_of_isPGroup (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hΓ : KFactAltTwoPGamma) {N : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hNp : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k = 1) (hNX : N ≤ d1X0 p M H)
    (hNn : K ⊓ d1X0 p M H ≤
      Subgroup.normalizer (N : Set (H ⧸ primeComplementCore (G := H) p))) :
    N ≤ Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p)
      ⟨z, hc.elt.2.2.1⟩) := by
  have : Fact p.Prime := ⟨hc.prime⟩
  have := hc.normal_K
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  set σ := QuotientGroup.mk' C
  set ψ := σ.comp K.subtype
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun k hk1 => ?_
    have hkC : (k : H ⧸ primeComplementCore (G := H) p) ∈ C := (QuotientGroup.eq_one_iff _).mp hk1
    have hmem : (k : H ⧸ primeComplementCore (G := H) p) ∈ K ⊓ C := ⟨k.2, hkC⟩
    rw [hc.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨T₁, hT₁, -⟩ := hc.data.exists_sylow
  set Γ := GLBCore p 1 (T₁ : Subgroup K)
  have hKX := hc.inf_d1X0_eq hT₁
  set NK := (N.map σ).comap ψ
  have hσ : ∀ a b : H ⧸ primeComplementCore (G := H) p, σ a = σ b → a⁻¹ * b ∈ C := fun a b h =>
    QuotientGroup.eq.mp h
  have hNKΓ : NK ≤ Γ := by
    intro k hk
    obtain ⟨n, hn, hnk⟩ := hk
    have hkX : (k : H ⧸ primeComplementCore (G := H) p) ∈ d1X0 p M H := by
      have h1 := hσ n k hnk
      have : (k : H ⧸ primeComplementCore (G := H) p) = n * (n⁻¹ * k) := by group
      rw [this]
      exact Subgroup.mul_mem _ (hNX hn) (hc.centralizer_le_d1X0 h1)
    obtain ⟨k', hk', hk'eq⟩ : (k : H ⧸ primeComplementCore (G := H) p) ∈ Γ.map K.subtype :=
      hKX ▸ ⟨k.2, hkX⟩
    rwa [show k' = k from Subtype.ext hk'eq] at hk'
  have hNKp : IsPGroup p NK := by
    rintro ⟨k, n, hn, hnk⟩
    obtain ⟨m, hm⟩ := hNp n hn
    refine ⟨m, Subtype.ext (hψ ?_)⟩
    change ψ (k ^ p ^ m) = ψ 1
    rw [map_pow, ← hnk, ← map_pow, hm, map_one, map_one]
  have hNKn : (NK.subgroupOf Γ).Normal := by
    refine ⟨fun k hk γ => ?_⟩
    obtain ⟨n, hn, hnk⟩ := Subgroup.mem_subgroupOf.mp hk
    have hγ : ((γ : K) : H ⧸ primeComplementCore (G := H) p) ∈ K ⊓ d1X0 p M H :=
      hKX ▸ ⟨γ, γ.2, rfl⟩
    have hγn := (Subgroup.mem_normalizer_iff.mp (hNn hγ) n).mp hn
    refine Subgroup.mem_subgroupOf.mpr ⟨_, hγn, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hnk]
    rfl
  have hNKbot : NK.subgroupOf Γ ≤ CFSG.pCore p Γ :=
    le_sSup ⟨hNKn, hNKp.comap_subtype⟩
  rw [(hΓ (↥K) p hc.prime hc.five_le hc.alt T₁).1] at hNKbot
  have hNC : N ≤ C := by
    intro n hn
    obtain ⟨m, hm⟩ := hNp n hn
    obtain ⟨k, hk, c, hcC, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hc.mem_sup_of_pow hm)
    have hkNK : (⟨k, hk⟩ : K) ∈ NK := by
      refine ⟨k * c, hn, ?_⟩
      change σ (k * c) = σ k
      have hc1 : σ c = 1 := (QuotientGroup.eq_one_iff c).mpr hcC
      rw [map_mul, hc1, mul_one]
    have h1 := hNKbot (Subgroup.mem_subgroupOf.mpr (show ((⟨⟨k, hk⟩, hNKΓ hkNK⟩ : Γ) : K) ∈ NK
      from hkNK))
    rw [Subgroup.mem_bot] at h1
    have hk1 : k = 1 := congrArg (fun g : Γ => ((g : K) : H ⧸ primeComplementCore (G := H) p)) h1
    rw [hk1, one_mul]
    exact hcC
  intro x hx
  set zH := QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hc.elt.2.2.1⟩
  have := hc.normal hc.elt.2.2.1
  obtain ⟨m, hm⟩ := hNp x hx
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hm)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hzp : IsPGroup p (Subgroup.zpowers zH) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc.orderOf_zH, pow_one])
  set D := Subgroup.zpowers x ⊔ Subgroup.zpowers zH
  have hDp : IsPGroup p D := hxp.to_sup_of_normal_right hzp
  have hDC : D ≤ C := sup_le (Subgroup.zpowers_le.mpr (hNC hx))
    (Subgroup.zpowers_le.mpr hc.elt.2.2.2)
  obtain ⟨zb, hzR, hzK, hzbp, hzc⟩ := hc.data.z
  have hKX₀ :=
    (hc.data.cfg.red.rankOne_principle hc.data.comp hc.data.noncyclic hzR hzK hzbp hzc).2
  have hDcyc : IsCyclic D := hc.data.cfg.red.isCyclic_of_le_centralizer hc.data.comp hKX₀ hDp hDC
  have hexp : Monoid.exponent D ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun d => by
    obtain ⟨j, hj⟩ := hDp d
    exact Subtype.ext (hc.pow_eq_one_of_pow (k := j) (by simpa using congrArg Subtype.val hj))
  rw [IsCyclic.exponent_eq_card] at hexp
  have hle : Subgroup.zpowers zH ≤ D := le_sup_right
  have heq : Subgroup.zpowers zH = D := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, hc.orderOf_zH]
    exact Nat.le_of_dvd hc.prime.pos hexp)
  exact heq ▸ (le_sup_left : Subgroup.zpowers x ≤ D) (Subgroup.mem_zpowers x)

end D1SmallAltConfig

end CFSG.AGLEmbedding
