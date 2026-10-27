module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVAltLambdaCore
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem mem_sup_of_pow (hc : D1IbAltConfig p P M H R Rbar K z)
    {x : H ⧸ primeComplementCore (G := H) p} {k : ℕ} (hx : x ^ p ^ k = 1) :
    x ∈ K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have : Fact p.Prime := ⟨hc.prime⟩
  exact mem_sup_centralizer_of_pow_eq_one hc.normal_K hc.rbar_le hx

theorem le_zpowers_of_isPGroup (hc : D1IbAltConfig p P M H R Rbar K z)
    (hΓ : KFactAltTwoPGamma) {N : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hNp : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k = 1) (hNX : N ≤ d1X0 p M H)
    (hNn : K ⊓ d1X0 p M H ≤
      Subgroup.normalizer (N : Set (H ⧸ primeComplementCore (G := H) p)))
    (hNz : ∀ n ∈ N, n * QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hc.elt.2.2.1⟩ =
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hc.elt.2.2.1⟩ * n) :
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
  set zH := QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hc.elt.2.2.1⟩
  have hNpg : IsPGroup p N := fun x => by
    obtain ⟨k, hk⟩ := hNp x x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hzp : IsPGroup p (Subgroup.zpowers zH) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc.orderOf_zH, pow_one])
  have hzN : Subgroup.zpowers zH ≤ Subgroup.normalizer (N : Set _) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun n hn => ?_)
    have : zH * n * zH⁻¹ = n := by
      rw [← hNz n hn, mul_inv_cancel_right]
    rw [this]
    exact hn
  set D := N ⊔ Subgroup.zpowers zH
  have hDp : IsPGroup p D := hNpg.to_sup_of_normal_left' hzp hzN
  have hDC : D ≤ C := sup_le hNC (Subgroup.zpowers_le.mpr hc.elt.2.2.2)
  have hD := D1OneSmallData.card_le_of_le_centralizer hc.data hc.card_R_le hDC hDp
  have heq : Subgroup.zpowers zH = D := Subgroup.eq_of_le_of_card_ge le_sup_right (by
    rw [Nat.card_zpowers, hc.orderOf_zH]
    exact hD)
  exact heq ▸ le_sup_left

theorem exists_lift_centralizer (hc : D1IbAltConfig p P M H R Rbar K z)
    {γ : H ⧸ primeComplementCore (G := H) p} (hγX : γ ∈ d1X0 p M H)
    (hγz : γ * QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hc.elt.2.2.1⟩ =
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hc.elt.2.2.1⟩ * γ) :
    ∃ g : G, g ∈ H ⊓ M ∧ g * z = z * g ∧ ∃ hgH : g ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨g, hgH⟩ = γ :=
  hc.data.exists_lift_centralizer_of_mem hc.elt hc.mem_M hγX hγz

theorem le_zpowers_zbar (hc : D1IbAltConfig p P M H R Rbar K z) (hΓ : KFactAltTwoPGamma)
    {Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hΛp : ∀ x ∈ Λ, ∃ k : ℕ, x ^ p ^ k = 1)
    (hΛC : Λ ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hΛn : ∀ g : ↥M, (g : G) * z = z * g → QuotientGroup.mk' (CFSG.pCore 2 ↥M) g ∈
      Subgroup.normalizer (Λ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    Λ ≤ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩) :=
  hc.data.le_zpowers_zbar_of hc.elt hc.phase hc.cz_le
    (fun hNp hNX hNn hNz => hc.le_zpowers_of_isPGroup hΓ hNp hNX hNn hNz) hΛp hΛC hΛn

end D1IbAltConfig

end CFSG.AGLEmbedding
