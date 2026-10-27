module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroLift
import CFSG.LocalAnalysis.AGLEmbedding.CommuteOfDecomp
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem card_rbar_inf (hc : D1SmallAltConfig p P M H R Rbar K z) :
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) =
      p ^ 2 := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, -, -, -, hT₁nc, -⟩ := hc.data.exists_sylow
  rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T₁.isPGroup'
  rw [hn]
  have hdvd : p ^ n ∣ Nat.card K := hn ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨e⟩ := hc.alt
  rw [Nat.card_congr e.toEquiv] at hdvd
  have := hp.two_le
  have h2 := two_mul_card_alternatingGroup_fin (n := 2 * p) (by omega)
  have hn3 : n < 3 := by
    by_contra h3
    have h4 : p ^ 3 ∣ (2 * p).factorial :=
      h2 ▸ ((pow_dvd_pow p (by omega : 3 ≤ n)).trans hdvd).trans (dvd_mul_left _ _)
    rcases hc.prime57 with rfl | rfl
    · exact absurd h4 (by decide)
    · exact absurd h4 (by norm_num [Nat.factorial])
  have hn2 : 2 ≤ n := by
    by_contra h2'
    apply hT₁nc
    interval_cases n
    · have : Subsingleton (T₁ : Subgroup K) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hn, pow_zero])).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (by rw [hn, pow_one])
  rw [show n = 2 by omega]

theorem card_d1LiftX (hc : D1SmallAltConfig p P M H R Rbar K z) :
    Nat.card (d1LiftX p H R K) = p ^ 2 ∧ z ∉ d1LiftX p H R K := by
  obtain ⟨hzT, hT⟩ := hc.data.d1LiftX_facts hc.elt
  exact ⟨hT.trans hc.card_rbar_inf, hzT⟩

theorem commute_of_mem_R (hc : D1SmallAltConfig p P M H R Rbar K z) {a b : G} (ha : a ∈ R)
    (hb : b ∈ R) : a * b = b * a := by
  have : Fact p.Prime := ⟨hc.prime⟩
  exact commute_of_mem_of_decomp
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hc.card_d1LiftX.1) (d1LiftX_le p H R K)
    (fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer hr)) hc.dec ha hb

theorem ne_one_and_ne_of_sizes {p n : ℕ} (hp5 : 5 ≤ p)
    (h : n = 0 ∨ n = p ^ 2 - 1 ∨ 2 * n = p ^ 2 - 1 ∨ n = 2 * (p - 1) ∨ n = (p - 1) ^ 2) :
    n ≠ 1 ∧ n ≠ p - 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 5 := ⟨p - 5, by omega⟩
  have e1 : (q + 5) ^ 2 = q * q + 10 * q + 25 := by ring
  have e2 : (q + 5 - 1) ^ 2 = q * q + 8 * q + 16 := by
    rw [show q + 5 - 1 = q + 4 by omega]
    ring
  rw [e1, e2] at h
  generalize q * q = s at h
  omega

theorem sizes_of_invSubset (hc : D1SmallAltConfig p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {S : Set G} (hS : D1InvSubset p H R K z S) :
    S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ 2 * S.ncard = p ^ 2 - 1 ∨ S.ncard = 2 * (p - 1) ∨
      S.ncard = (p - 1) ^ 2 := by
  rcases hc.data.orbit_sizes hOrb hc.elt hc.dec hc.not_fi22 hc.card_rbar_inf with h | ⟨-, -, h⟩ |
    ⟨-, h⟩
  · rcases h S hS with h | h <;> simp [h]
  · rcases h S hS with h | h | h <;> simp [h]
  · rcases h S hS with h | h | h | h <;> simp [h]

theorem invSubset_ncard_ne (hc : D1SmallAltConfig p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {S : Set G} (hS : D1InvSubset p H R K z S) : S.ncard ≠ 1 ∧ S.ncard ≠ p - 1 :=
  ne_one_and_ne_of_sizes hc.five_le (hc.sizes_of_invSubset hOrb hS)

theorem inv_subgroup (hc : D1SmallAltConfig p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {B : Subgroup G} (hBR : B ≤ R)
    (hBinv : ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) → ∀ b ∈ B, n * b * n⁻¹ ∈ B) :
    (d1LiftX p H R K ≤ B ∨ B ⊓ d1LiftX p H R K = ⊥) ∧
      (B ⊓ d1LiftX p H R K = ⊥ → B ≤ Subgroup.zpowers z ∧ (z ∉ B → B = ⊥)) := by
  have hp := hc.prime
  set T := d1LiftX p H R K
  have hTR : T ≤ R := d1LiftX_le p H R K
  obtain ⟨hTcard, hzT⟩ := hc.card_d1LiftX
  refine ⟨?_, fun hD => ?_⟩
  ·
    set D := B ⊓ T
    have hS : D1InvSubset p H R K z ((D : Set G) \ {1}) := by
      refine ⟨fun t ht => ⟨ht.1.2, ht.2⟩, fun n hn hnz hnT t ht => ⟨⟨hBinv n hn hnz hnT t ht.1.1,
        hnT t ht.1.2⟩, fun h1 => ht.2 ?_⟩⟩
      rw [Set.mem_singleton_iff] at h1 ⊢
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    have hcard := (hc.invSubset_ncard_ne hOrb hS).2
    rw [Set.ncard_sdiff_singleton_of_mem D.one_mem, ← Nat.card_coe_set_eq] at hcard
    change Nat.card D - 1 ≠ p - 1 at hcard
    have hDdvd : Nat.card D ∣ p ^ 2 := hTcard ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hDdvd
    interval_cases j
    · right
      exact Subgroup.eq_bot_of_card_eq D (by rw [hjeq, pow_zero])
    · exact absurd (by rw [hjeq, pow_one]) hcard
    · left
      have : D = T := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hjeq, hTcard])
      exact this ▸ inf_le_left
  ·
    have hBz : B ≤ Subgroup.zpowers z := by
      intro b hb
      obtain ⟨t, ht, i, rfl⟩ := hc.dec b (hBR hb)
      by_cases ht1 : t = 1
      · rw [ht1, one_mul]
        exact Subgroup.npow_mem_zpowers z i
      exfalso
      have hfix : ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
          (∀ s ∈ T, n * s * n⁻¹ ∈ T) → n * t * n⁻¹ = t := by
        intro n hn hnz hnT
        have h1 := hBinv n hn hnz hnT _ hb
        have h2 : n * (t * z ^ i) * n⁻¹ * (t * z ^ i)⁻¹ = n * t * n⁻¹ * t⁻¹ := by
          have : n * z ^ i * n⁻¹ = z ^ i := by rw [← conj_pow, hnz]
          calc n * (t * z ^ i) * n⁻¹ * (t * z ^ i)⁻¹
              = n * t * n⁻¹ * (n * z ^ i * n⁻¹) * (z ^ i)⁻¹ * t⁻¹ := by group
            _ = n * t * n⁻¹ * t⁻¹ := by rw [this]; group
        have h3 : n * t * n⁻¹ * t⁻¹ ∈ B ⊓ T := by
          rw [← h2]
          exact ⟨B.mul_mem h1 (B.inv_mem hb), by
            rw [h2]; exact T.mul_mem (hnT t ht) (T.inv_mem ht)⟩
        rw [hD, Subgroup.mem_bot] at h3
        exact mul_inv_eq_one.mp h3
      have hS : D1InvSubset p H R K z {t} := by
        refine ⟨fun s hs => ?_, fun n hn hnz hnT s hs => ?_⟩
        · rw [Set.mem_singleton_iff] at hs
          exact hs ▸ ⟨ht, ht1⟩
        · rw [Set.mem_singleton_iff] at hs ⊢
          rw [hs]
          exact hfix n hn hnz hnT
      exact (hc.invSubset_ncard_ne hOrb hS).1 (Set.ncard_singleton t)
    refine ⟨hBz, fun hzB => (Subgroup.eq_bot_iff_forall _).mpr fun b hb => ?_⟩
    by_contra hb1
    exact hzB ((Subgroup.zpowers_le.mpr hb) (mem_zpowers_of_mem_zpowers_of_prime hp hc.elt.2.1
      (hBz hb) hb1))

end D1SmallAltConfig

end CFSG.AGLEmbedding
