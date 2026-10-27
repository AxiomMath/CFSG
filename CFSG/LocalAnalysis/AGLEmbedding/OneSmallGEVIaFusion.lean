module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroLift
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNA
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_conj_eq_inv_u33 (hInvU : KFactU33SylowInvert)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) (hp3 : p = 3)
    (hU : IsSmallUnitary 3 K) :
    ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∃ n ∈ Subgroup.normalizer (R : Set G),
      n * z * n⁻¹ = z ∧ (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧
      n * t * n⁻¹ = t⁻¹ := by
  subst hp3
  have hp := hd.cfg.red.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hO := primeComplementCore_coprime (G := H) 3
  have hRHp : IsPGroup 3 (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  intro t ht ht1
  obtain ⟨t', ⟨ht'R, ht'K⟩, rfl⟩ := ht
  have h1 : π t' ∈ (T₁ : Subgroup K).map K.subtype := by
    rw [hT₁]
    exact ⟨by rw [hd.cfg.rbar]; exact ⟨t', ht'R, rfl⟩, ht'K⟩
  obtain ⟨s, hs, hseq⟩ := h1
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply ht1
    have h2 : π t' = π 1 := by rw [← hseq, map_one]; rfl
    have h3 := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp _ hO hRHp ht'R
      (R.subgroupOf H).one_mem h2
    simp [h3]
  obtain ⟨nb, hnb, hinvb⟩ := hInvU K hU T₁ s hs hs1
  obtain ⟨n, hnN, hnz, hnπ⟩ := hd.exists_lift_of_mem_normalizer hz hdec hT₁ hnb
  refine ⟨n, hnN, hnz, ?_, ?_⟩
  · rintro _ ⟨x, ⟨hxR, hxK⟩, rfl⟩
    have hnx : n * x * n⁻¹ ∈ R.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have h4 := (Subgroup.mem_normalizer_iff.mp hnN (x : G)).mp (Subgroup.mem_subgroupOf.mp hxR)
      simpa using h4
    have hxK' : π x ∈ K := hxK
    have hnxK : n * x * n⁻¹ ∈ K.comap π := by
      show π (n * x * n⁻¹) ∈ K
      rw [map_mul, map_mul, map_inv, hnπ]
      exact K.mul_mem (K.mul_mem (Subtype.mem nb) hxK') (K.inv_mem (Subtype.mem nb))
    exact ⟨n * x * n⁻¹, ⟨hnx, hnxK⟩, by simp⟩
  · have h2 : π (n * t' * n⁻¹) = π t'⁻¹ := by
      rw [map_mul, map_mul, map_inv, hnπ, map_inv, ← hseq]
      have h3 := congrArg (fun k : K => (k : H ⧸ primeComplementCore (G := H) 3)) hinvb
      simpa using h3
    have hmem1 : n * t' * n⁻¹ ∈ R.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have h4 := (Subgroup.mem_normalizer_iff.mp hnN (t' : G)).mp (Subgroup.mem_subgroupOf.mp ht'R)
      simpa using h4
    have h5 := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp _ hO hRHp hmem1
      ((R.subgroupOf H).inv_mem ht'R) h2
    have h6 := congrArg Subtype.val h5
    simpa using h6

omit [Finite G] in
theorem fusionSet_subset_centerOf {R : Subgroup G} {z : G} (hz : z ∈ centerOf R) :
    fusionSet R z ⊆ (centerOf R : Set G) := by
  rintro w ⟨-, n, hn, hw⟩
  obtain ⟨hzR, hzc⟩ := mem_centerOf_iff_commute.mp hz
  have h1 : n * z * n⁻¹ ∈ centerOf R := by
    refine mem_centerOf_iff_commute.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn z).mp hzR, ?_⟩
    intro r hr
    have hr' : n⁻¹ * r * n ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) r).mp hr
      simpa using this
    have h2 := hzc _ hr'
    calc r * (n * z * n⁻¹) = n * ((n⁻¹ * r * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * r * n)) * n⁻¹ := by rw [h2]
      _ = n * z * n⁻¹ * r := by group
  exact (Subgroup.zpowers_le.mpr h1) hw

theorem D1OneSmallData.fusZ_u33 (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hp3 : p = 3)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hZT : Nat.card (Subgroup.center (T₁ : Subgroup K)) = p)
    (hinv : ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∃ n ∈ Subgroup.normalizer (R : Set G),
      n * z * n⁻¹ = z ∧ (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧
      n * t * n⁻¹ = t⁻¹) :
    (∀ r ∈ R, r ∉ d1LiftX p H R K → (∀ s ∈ R, r * s = s * r) → r ∈ fusionSet R z) ∧
      (fusionSet R z).ncard < 9 := by
  subst hp3
  set T := d1LiftX 3 H R K with hT
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = 3 := hz.2.1
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzp; omega
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  have hzZ : z ∈ centerOf R := mem_centerOf_iff_commute.mpr ⟨hzR, hRz⟩
  have hZsub := fusionSet_subset_centerOf hzZ
  set W : Subgroup G := centerOf R ⊓ T with hW
  have hW3 : Nat.card W ≤ 3 := (hd.card_center_inf_le hT₁).trans hZT.le
  obtain ⟨hdvd, hinv₁, hinv₂⟩ := hd.fusion_count hz hB0 hdec hexpR
  set S₁ : Set G := fusionSet R z ∩ (T : Set G) with hS₁
  set S₂ : Set G := {t | t ∈ T ∧ z * t ∈ fusionSet R z} \ {1} with hS₂
  have hsub₁ : S₁ ⊆ (W : Set G) \ {1} := fun w hw =>
    ⟨⟨hZsub hw.1, hw.2⟩, hw.1.1⟩
  have hsub₂ : S₂ ⊆ (W : Set G) \ {1} := by
    rintro t ⟨⟨htT, hzt⟩, ht1⟩
    refine ⟨⟨?_, htT⟩, ht1⟩
    have h1 := hZsub hzt
    have : t = z⁻¹ * (z * t) := by group
    rw [this]
    exact (centerOf R).mul_mem ((centerOf R).inv_mem hzZ) h1
  have hWc : ((W : Set G) \ {1}).ncard ≤ 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem W.one_mem, ← Nat.card_coe_set_eq]
    change Nat.card W - 1 ≤ 2
    omega
  have hsizes : ∀ S : Set G, D1InvSubset 3 H R K z S → S ⊆ (W : Set G) \ {1} →
      S.ncard = 0 ∨ S.ncard = 2 := by
    intro S hS hSW
    rcases S.eq_empty_or_nonempty with he | ⟨w, hw⟩
    · left; rw [he, Set.ncard_empty]
    right
    have hwT : w ∈ T := (hS.1 hw).1
    have hw1 : w ≠ 1 := (hS.1 hw).2
    obtain ⟨n, hn, hnz, hnT, hnw⟩ := hinv w hwT hw1
    have hwinv : w⁻¹ ∈ S := hnw ▸ hS.2 n hn hnz hnT w hw
    have hw3 : w ^ 3 = 1 := hexpR w (hTR hwT)
    have hne : w ≠ w⁻¹ := by
      intro he
      apply hw1
      have h2 : w ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [he]; exact mul_inv_cancel w
      calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
        _ = 1 := by rw [hw3, h2]; group
    have h2 : 2 ≤ S.ncard := by
      have h3 := Set.ncard_le_ncard (Set.insert_subset hw (Set.singleton_subset_iff.mpr hwinv))
        (Set.toFinite S)
      rwa [Set.ncard_pair hne] at h3
    have h3 : S.ncard ≤ 2 := (Set.ncard_le_ncard hSW (Set.toFinite _)).trans hWc
    omega
  have hc₁ := hsizes _ hinv₁ hsub₁
  have hc₂ := hsizes _ hinv₂ hsub₂
  have hS₂card : S₂.ncard = 2 := by
    rcases hc₁ with h1 | h1 <;> rcases hc₂ with h2 | h2
    · rw [h1, h2] at hdvd; norm_num at hdvd
    · exact h2
    · rw [h1, h2] at hdvd; norm_num at hdvd
    · rw [h1, h2] at hdvd; norm_num at hdvd
  have hS₂eq : S₂ = (W : Set G) \ {1} := Set.eq_of_subset_of_ncard_le hsub₂ (by omega)
  have hzW : ∀ w ∈ W, z * w ∈ fusionSet R z := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, mul_one]; exact self_mem_fusionSet hz1
    · have : w ∈ S₂ := hS₂eq ▸ ⟨hw, hw1⟩
      exact this.1.2
  refine ⟨?_, ?_⟩
  · intro r hr hrT hrc
    obtain ⟨t, ht, i, rfl⟩ := hdec r hr
    have htR : t ∈ R := hTR ht
    have hz3 : z ^ 3 = 1 := hexpR z hzR
    have hzi : z ^ i = z ^ (i % 3) := by
      conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hz3, one_pow, mul_one]
    have htW : t ∈ W := by
      refine ⟨mem_centerOf_iff_commute.mpr ⟨htR, fun s hs => ?_⟩, ht⟩
      have h1 := hrc s hs
      have hzs : z ^ i * s = s * z ^ i := (Commute.pow_left (hRz s hs).symm i).eq
      have : t = (t * z ^ i) * (z ^ i)⁻¹ := by group
      rw [this]
      calc s * (t * z ^ i * (z ^ i)⁻¹) = (s * (t * z ^ i)) * (z ^ i)⁻¹ := by group
        _ = ((t * z ^ i) * s) * (z ^ i)⁻¹ := by rw [h1]
        _ = (t * z ^ i) * (s * (z ^ i)⁻¹) := by group
        _ = (t * z ^ i) * ((z ^ i)⁻¹ * s) := by
          rw [(Commute.inv_left (Commute.pow_left (hRz s hs).symm i)).symm.eq]
        _ = t * z ^ i * (z ^ i)⁻¹ * s := by group
    have hct : Commute t z := hRz t htR
    rw [hzi] at hrT ⊢
    have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : i % 3
    · exact absurd (by simpa using ht) hrT
    · rw [pow_one, hct.eq]; exact hzW t htW
    · have ht2W : t ^ 2 ∈ W := W.pow_mem htW 2
      have hmem := hzW _ ht2W
      have hsq : (z * t ^ 2) ^ 2 = t * z ^ 2 := by
        have hc2 : Commute z (t ^ 2) := (hct.pow_left 2).symm
        rw [hc2.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add,
          hexpR t htR, one_mul, pow_one]
        exact (hct.pow_right 2).eq.symm
      rw [← hsq]
      refine pow_mem_fusionSet hmem ?_
      rw [hsq]
      intro h1
      exact hrT (h1 ▸ T.one_mem)
  ·
    have hdecZ : ∀ r ∈ centerOf R, ∃ t ∈ centerOf R ⊓ T, ∃ c ∈ Subgroup.zpowers z, t * c = r := by
      intro r hr
      obtain ⟨t, ht, i, hti⟩ := hdec r (mem_centerOf_iff_commute.mp hr).1
      refine ⟨t, ⟨?_, ht⟩, z ^ i, Subgroup.npow_mem_zpowers z i, hti.symm⟩
      have : t = r * (z ^ i)⁻¹ := by rw [hti]; group
      rw [this]
      exact (centerOf R).mul_mem hr ((centerOf R).inv_mem ((centerOf R).pow_mem hzZ i))
    have h1 : Nat.card (centerOf R) ≤ Nat.card W * Nat.card (Subgroup.zpowers z) :=
      card_le_mul_of_decomp (Subgroup.zpowers_le.mpr hzZ) hdecZ
    rw [Nat.card_zpowers, hzp] at h1
    have h2 : Nat.card (centerOf R) ≤ 9 := by
      calc Nat.card (centerOf R) ≤ Nat.card W * 3 := h1
        _ ≤ 3 * 3 := Nat.mul_le_mul_right 3 hW3
        _ = 9 := by norm_num
    have h3 : fusionSet R z ⊆ (centerOf R : Set G) \ {1} := fun w hw => ⟨hZsub hw, hw.1⟩
    have h4 : (fusionSet R z).ncard ≤ ((centerOf R : Set G) \ {1}).ncard :=
      Set.ncard_le_ncard h3 (Set.toFinite _)
    have h5 : ((centerOf R : Set G) \ {1}).ncard = Nat.card (centerOf R) - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem (centerOf R).one_mem, ← Nat.card_coe_set_eq]
      rfl
    omega

end CFSG.AGLEmbedding
