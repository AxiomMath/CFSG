module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_mk_eq_of_mem_normalizer_map {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (O : Subgroup Y) [O.Normal] (hO : p.Coprime (Nat.card O)) {S : Subgroup Y}
    (hS : IsPGroup p S) {yt : Y ⧸ O}
    (hyt : yt ∈ Subgroup.normalizer ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) :
      Set (Y ⧸ O))) :
    ∃ y ∈ Subgroup.normalizer (S : Set Y), QuotientGroup.mk' O y = yt := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective O yt
  have hy : y₀ ∈ ((O ⊔ Subgroup.normalizer (S : Set Y) : Subgroup Y) : Set Y) :=
    comap_normalizer_map_le_sup Fact.out O hO hS hyt
  rw [Subgroup.normal_mul, Set.mem_mul] at hy
  obtain ⟨o, ho, n, hn, rfl⟩ := hy
  refine ⟨n, hn, ?_⟩
  have ho1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  rw [map_mul, ho1, one_mul]

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_lift_of_mem_normalizer (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    {nb : K} (hnb : nb ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K)) :
    ∃ n : H, (n : G) ∈ Subgroup.normalizer (R : Set G) ∧ (n : G) * z * (n : G)⁻¹ = z ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) n =
        (nb : H ⧸ primeComplementCore (G := H) p) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hO := primeComplementCore_coprime (G := H) p
  have hRHp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRHp ha hb hab
  set zb := π ⟨z, hz.2.2.1⟩ with hzb
  have hzbc : (nb : H ⧸ primeComplementCore (G := H) p) * zb *
      (nb : H ⧸ primeComplementCore (G := H) p)⁻¹ = zb := by
    have h1 := Subgroup.mem_centralizer_iff.mp hz.2.2.2 (nb : H ⧸ _) nb.2
    rw [← hzb] at h1
    rw [h1]
    group
  have hnR : (nb : H ⧸ primeComplementCore (G := H) p) ∈
      Subgroup.normalizer (((R.subgroupOf H).map π : Subgroup (H ⧸ _)) : Set (H ⧸ _)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨r, hr, rfl⟩ := hy
    obtain ⟨t, ht, i, hti⟩ := hdec r hr
    obtain ⟨t', ⟨ht'R, ht'K⟩, rfl⟩ := ht
    have hr' : r = t' * (⟨z, hz.2.2.1⟩ : H) ^ i := Subtype.ext (by simpa using hti)
    rw [hr', map_mul, map_pow]
    have h1 : π t' ∈ (T₁ : Subgroup K).map K.subtype := by
      rw [hT₁]
      exact ⟨by rw [hd.cfg.rbar]; exact ⟨t', ht'R, rfl⟩, ht'K⟩
    obtain ⟨s, hs, hseq⟩ := h1
    have h2 : (nb : H ⧸ primeComplementCore (G := H) p) * π t' * (nb : H ⧸ _)⁻¹ ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
      have h3 : nb * s * nb⁻¹ ∈ (T₁ : Subgroup K) := (Subgroup.mem_normalizer_iff.mp hnb s).mp hs
      have h4 : ((nb * s * nb⁻¹ : K) : H ⧸ primeComplementCore (G := H) p) ∈
          (T₁ : Subgroup K).map K.subtype := ⟨_, h3, rfl⟩
      rw [hT₁] at h4
      rw [← hseq]
      have h7 : ((nb * s * nb⁻¹ : K) : H ⧸ primeComplementCore (G := H) p) =
          (nb : H ⧸ primeComplementCore (G := H) p) * K.subtype s * (nb : H ⧸ _)⁻¹ := by
        simp
      rw [← h7]
      exact h4.1
    rw [hd.cfg.rbar] at h2
    have h5 : (nb : H ⧸ primeComplementCore (G := H) p) * (π t' * zb ^ i) * (nb : H ⧸ _)⁻¹ =
        ((nb : H ⧸ _) * π t' * (nb : H ⧸ _)⁻¹) * zb ^ i := by
      have h6 : (nb : H ⧸ primeComplementCore (G := H) p) * zb ^ i * (nb : H ⧸ _)⁻¹ = zb ^ i := by
        rw [← conj_pow, hzbc]
      calc (nb : H ⧸ primeComplementCore (G := H) p) * (π t' * zb ^ i) * (nb : H ⧸ _)⁻¹
          = ((nb : H ⧸ _) * π t' * (nb : H ⧸ _)⁻¹) *
            ((nb : H ⧸ _) * zb ^ i * (nb : H ⧸ _)⁻¹) := by group
        _ = _ := by rw [h6]
    rw [h5]
    exact Subgroup.mul_mem _ h2 (Subgroup.pow_mem _
      (show zb ∈ (R.subgroupOf H).map π from ⟨⟨z, hz.2.2.1⟩, hz.1, rfl⟩) i)
  obtain ⟨n, hnN, hnπ⟩ := exists_mk_eq_of_mem_normalizer_map _ hO hRHp hnR
  refine ⟨n, ?_, ?_, hnπ⟩
  · refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hnN ⟨r, hd.cfg.ext.le_H hr⟩).mp hr
    exact h1
  · have hzR : (⟨z, hz.2.2.1⟩ : H) ∈ R.subgroupOf H := hz.1
    have h1 : n * ⟨z, hz.2.2.1⟩ * n⁻¹ ∈ R.subgroupOf H :=
      (Subgroup.mem_normalizer_iff.mp hnN _).mp hzR
    have h2 : π (n * ⟨z, hz.2.2.1⟩ * n⁻¹) = π ⟨z, hz.2.2.1⟩ := by
      rw [map_mul, map_mul, map_inv, hnπ, ← hzb, hzbc]
    have h3 := hinj _ h1 _ hzR h2
    simpa using congrArg Subtype.val h3

theorem D1OneSmallData.exists_transport (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    {S : Set G} (hS : S ⊆ (d1LiftX p H R K : Set G) \ {1})
    (hinv : ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) → ∀ t ∈ S, n * t * n⁻¹ ∈ S) :
    ∃ O : Set K, O ⊆ ((T₁ : Subgroup K) : Set K) \ {1} ∧
      (∀ n ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) ∧
      O.ncard = S.ncard := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hO := primeComplementCore_coprime (G := H) p
  have hRHp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRHp ha hb hab
  have hTH : ∀ t ∈ d1LiftX p H R K, ∃ htH : t ∈ H, ∃ s : K, s ∈ (T₁ : Subgroup K) ∧
      (s : H ⧸ primeComplementCore (G := H) p) = π ⟨t, htH⟩ := by
    rintro _ ⟨t', ⟨ht'R, ht'K⟩, rfl⟩
    refine ⟨t'.2, ?_⟩
    have h1 : π t' ∈ (T₁ : Subgroup K).map K.subtype := by
      rw [hT₁]
      exact ⟨by rw [hd.cfg.rbar]; exact ⟨t', ht'R, rfl⟩, ht'K⟩
    obtain ⟨s, hs, hseq⟩ := h1
    exact ⟨s, hs, hseq⟩
  have hex : ∀ t ∈ S, ∃ s : K, s ∈ (T₁ : Subgroup K) ∧ ∃ htH : t ∈ H,
      (s : H ⧸ primeComplementCore (G := H) p) = π ⟨t, htH⟩ := by
    intro t ht
    obtain ⟨htH, s, hs, hseq⟩ := hTH t (hS ht).1
    exact ⟨s, hs, htH, hseq⟩
  choose f hfT hfH hf using hex
  have hfeq : ∀ t (ht : t ∈ S) (s : K) (htH : t ∈ H),
      (s : H ⧸ primeComplementCore (G := H) p) = π ⟨t, htH⟩ → f t ht = s := by
    intro t ht s htH hs
    apply Subtype.ext
    rw [hf t ht, hs]
  refine ⟨{s | ∃ t, ∃ ht : t ∈ S, f t ht = s}, ?_, ?_, ?_⟩
  · rintro s ⟨t, ht, rfl⟩
    refine ⟨hfT t ht, fun h1 => ?_⟩
    have h2 : π ⟨t, hfH t ht⟩ = π 1 := by
      rw [← hf t ht, map_one]
      rw [Set.mem_singleton_iff] at h1
      rw [h1]
      rfl
    have htR : (⟨t, hfH t ht⟩ : H) ∈ R.subgroupOf H := d1LiftX_le p H R K (hS ht).1
    have h3 := hinj _ htR _ (R.subgroupOf H).one_mem h2
    exact (hS ht).2 (congrArg Subtype.val h3)
  · rintro nb hnb _ ⟨t, ht, rfl⟩
    obtain ⟨n, hnR, hnz, hnπ⟩ := hd.exists_lift_of_mem_normalizer hz hdec hT₁ hnb
    have hnT : ∀ t ∈ d1LiftX p H R K, (n : G) * t * (n : G)⁻¹ ∈ d1LiftX p H R K := by
      rintro _ ⟨t', ⟨ht'R, ht'K⟩, rfl⟩
      refine ⟨n * t' * n⁻¹, ⟨?_, ?_⟩, rfl⟩
      · exact (Subgroup.mem_normalizer_iff.mp hnR (t' : G)).mp ht'R
      · show π (n * t' * n⁻¹) ∈ K
        rw [map_mul, map_mul, map_inv, hnπ]
        exact K.mul_mem (K.mul_mem nb.2 ht'K) (K.inv_mem nb.2)
    have ht' := hinv _ hnR hnz hnT t ht
    refine ⟨_, ht', ?_⟩
    apply hfeq _ ht' _ (hfH _ ht')
    have h1 : (⟨(n : G) * t * (n : G)⁻¹, hfH _ ht'⟩ : H) = n * ⟨t, hfH t ht⟩ * n⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, hnπ, ← hf t ht]
    simp
  · symm
    refine Set.ncard_congr f (fun t ht => ⟨t, ht, rfl⟩) ?_ ?_
    · intro a b ha hb hab
      have h1 : π ⟨a, hfH a ha⟩ = π ⟨b, hfH b hb⟩ := by
        rw [← hf a ha, ← hf b hb, hab]
      have haR : (⟨a, hfH a ha⟩ : H) ∈ R.subgroupOf H := d1LiftX_le p H R K (hS ha).1
      have hbR : (⟨b, hfH b hb⟩ : H) ∈ R.subgroupOf H := d1LiftX_le p H R K (hS hb).1
      exact congrArg Subtype.val (hinj _ haR _ hbR h1)
    · rintro s ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩

@[expose] def D1InvSubset (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) (S : Set G) : Prop :=
  S ⊆ (d1LiftX p H R K : Set G) \ {1} ∧ ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
    (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) → ∀ t ∈ S, n * t * n⁻¹ ∈ S

theorem D1OneSmallData.orbit_sizes (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hFi : ¬ (p = 5 ∧ IsFi22 K))
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) :
    (∀ S, D1InvSubset p H R K z S → S.ncard = 0 ∨ S.ncard = p ^ 2 - 1) ∨
    (IsSmallLinTwo p K ∧ 5 ≤ p ∧ ∀ S, D1InvSubset p H R K z S →
      S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ 2 * S.ncard = p ^ 2 - 1) ∨
    (IsAltTwoP p K ∧ ∀ S, D1InvSubset p H R K z S →
      S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ S.ncard = 2 * (p - 1) ∨ S.ncard = (p - 1) ^ 2) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  obtain ⟨T₁, hT₁, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  have hT₁card : Nat.card T₁ = p ^ 2 := by
    rw [← hcard, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  have htr : ∀ S, D1InvSubset p H R K z S → ∃ O : Set K,
      O ⊆ ((T₁ : Subgroup K) : Set K) \ {1} ∧
      (∀ n ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) ∧
      O.ncard = S.ncard := fun S hS => hd.exists_transport hz hdec hT₁ hS.1 hS.2
  rcases hOrb K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small hFi hT₁card with h | ⟨hL, h5, h⟩ |
    ⟨hA, h⟩
  · left
    intro S hS
    obtain ⟨O, hO1, hO2, hO3⟩ := htr S hS
    rw [← hO3]
    exact h O hO1 hO2
  · right; left
    refine ⟨hL, h5, fun S hS => ?_⟩
    obtain ⟨O, hO1, hO2, hO3⟩ := htr S hS
    rw [← hO3]
    exact h O hO1 hO2
  · right; right
    refine ⟨hA, fun S hS => ?_⟩
    obtain ⟨O, hO1, hO2, hO3⟩ := htr S hS
    rw [← hO3]
    exact h O hO1 hO2

end Config

end CFSG.AGLEmbedding
