module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroCount
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroArith
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroLift
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.d1LiftX_facts (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    z ∉ d1LiftX p H R K ∧ Nat.card (d1LiftX p H R K) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hO := primeComplementCore_coprime (G := H) p
  have hRHp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  refine ⟨?_, ?_⟩
  · rintro ⟨t, ⟨htR, htK⟩, hteq⟩
    have ht : t = ⟨z, hz.2.2.1⟩ := Subtype.ext hteq
    subst ht
    have hcen : (⟨π ⟨z, hz.2.2.1⟩, htK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun k =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2.2.2 k k.2)
    rw [hd.center, Subgroup.mem_bot] at hcen
    have h1 : π ⟨z, hz.2.2.1⟩ = 1 := congrArg Subtype.val hcen
    have h2 : (⟨z, hz.2.2.1⟩ : H) ∈ R.subgroupOf H ⊓ primeComplementCore (G := H) p :=
      ⟨hz.1, (QuotientGroup.eq_one_iff _).mp h1⟩
    rw [inf_eq_bot_of_isPGroup hp hRHp hO, Subgroup.mem_bot] at h2
    have h3 : z = 1 := congrArg Subtype.val h2
    have h4 := hz.2.1
    rw [h3, orderOf_one] at h4
    exact hp.one_lt.ne h4
  · have hXp : IsPGroup p ((d1LiftX p H R K).subgroupOf H) :=
      (hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)).comap_subtype
    rw [← hd.cfg.map_d1LiftX_eq_inf (K := K), card_map_mk_of_isPGroup hp _ hO hXp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (d1LiftX_le_H p H R K)).toEquiv]

theorem D1OneSmallData.false_of_ab_of_sizes_of_exotic
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G))
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1)
    (hsizes : (∀ S, D1InvSubset p H R K z S → S.ncard = 0 ∨ S.ncard = p ^ 2 - 1) ∨
      (IsSmallLinTwo p K ∧ 5 ≤ p ∧ ∀ S, D1InvSubset p H R K z S →
        S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ 2 * S.ncard = p ^ 2 - 1) ∨
      (IsAltTwoP p K ∧ ∀ S, D1InvSubset p H R K z S →
        S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ S.ncard = 2 * (p - 1) ∨ S.ncard = (p - 1) ^ 2))
    (hexo : p = 3 → IsAltTwoP p K →
      (∀ t ∈ d1LiftX p H R K, z * t ∈ fusionSet R z → t = 1) →
      (fusionSet R z ∩ (d1LiftX p H R K : Set G)).ncard = 4 → (fusionSet R z).ncard < 9 → False)
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set T := d1LiftX p H R K with hT
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = p := hz.2.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; exact hp.one_lt.ne hzp
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hzT, hTcard'⟩ := hd.d1LiftX_facts hz
  have hTcard : Nat.card T = p ^ 2 := hTcard'.trans hcard
  have hTab : IsElemAbelian p T :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hTcard, fun t ht => hexpR t (hTR ht)⟩
  have hZQ : ∀ w ∈ fusionSet R z, pCoreOf 2 M ⊓ Subgroup.centralizer ({w} : Set G) ≤
      Subgroup.centralizer (R : Set G) := by
    rintro w ⟨hw1, n, hn, hwn⟩
    exact twoCore_inf_centralizer_le_of_conj hp hzp (hd.cfg.ext.normalizer_le hn) hn hQz hwn hw1
  have hplane : ∀ A : Subgroup G, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∀ a ∈ A, (∀ b ∈ A, b ∉ Subgroup.zpowers a → b ∈ fusionSet R z) → a = 1 := by
    intro A hAR hA hAcard a haA hb
    refine eq_one_of_plane hp hp2 hd.cfg.glob.charTwo hd.cfg.loc.maxLocal.1
      (hAR.trans hd.cfg.ext.le_M) hA hAcard haA fun b hbA hba => ?_
    intro u hu
    have h1 := hZQ b (hb b hbA hba) hu
    rw [Subgroup.mem_centralizer_iff] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h1 a (hAR haA)).symm
  obtain ⟨t₀, ht₀T, ht₀1⟩ : ∃ t₀ ∈ T, t₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hTcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  obtain ⟨x, hxP, hxN, hxR, hxz⟩ := hd.exists_moving_elt hz hB0
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpdvd : p ∣ (fusionSet R z).ncard := p_dvd_ncard_fusionSet hzp hxN hxk hxR
    (fun y hy hyz hyk => hd.mem_of_mem_normalizer_of_commute hB0 hy hyz hyk)
  have hcount := ncard_fusionSet_eq hp hTR hzR hzT hzp hRz hexpR hdec
  set S₁ : Set G := fusionSet R z ∩ (T : Set G) with hS₁
  set O' : Set G := {t | t ∈ T ∧ z * t ∈ fusionSet R z} with hO'
  set S₂ : Set G := O' \ {1} with hS₂
  have h1O' : (1 : G) ∈ O' := ⟨T.one_mem, by rw [mul_one]; exact self_mem_fusionSet hz1⟩
  have hO'card : O'.ncard = 1 + S₂.ncard := by
    rw [add_comm]
    exact (Set.ncard_sdiff_singleton_add_one h1O').symm
  have hdvd : p ∣ S₁.ncard + (p - 1) * (1 + S₂.ncard) := by
    rw [← hO'card, ← hcount]
    exact hpdvd
  have hinv₁ : D1InvSubset p H R K z S₁ := by
    refine ⟨fun w hw => ⟨hw.2, hw.1.1⟩, fun n hn hnz hnT w hw =>
      ⟨conj_mem_fusionSet hn hw.1, hnT w hw.2⟩⟩
  have hinv₂ : D1InvSubset p H R K z S₂ := by
    refine ⟨fun t ht => ⟨ht.1.1, ht.2⟩, fun n hn hnz hnT t ht => ⟨⟨hnT t ht.1.1, ?_⟩, ?_⟩⟩
    · have h1 : z * (n * t * n⁻¹) = n * (z * t) * n⁻¹ := by
        calc z * (n * t * n⁻¹) = (n * z * n⁻¹) * (n * t * n⁻¹) := by rw [hnz]
          _ = n * (z * t) * n⁻¹ := by group
      rw [h1]
      exact conj_mem_fusionSet hn ht.1.2
    · intro h
      apply ht.2
      rw [Set.mem_singleton_iff] at h ⊢
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
  have hT1 : ((T : Set G) \ {1}).ncard = p ^ 2 - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hTcard
  have hcase1 : S₁.ncard ≠ p ^ 2 - 1 := by
    intro h
    have hsub : S₁ ⊆ (T : Set G) \ {1} := hinv₁.1
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h, hT1])
    apply ht₀1
    refine hplane T hTR hTab hTcard t₀ ht₀T fun b hbT hbt => ?_
    have hb1 : b ≠ 1 := fun h1 => hbt (h1 ▸ Subgroup.one_mem _)
    have : b ∈ S₁ := heq ▸ ⟨hbT, hb1⟩
    exact this.1
  have hcase2 : S₂.ncard ≠ p ^ 2 - 1 := by
    intro h
    have hsub : S₂ ⊆ (T : Set G) \ {1} := hinv₂.1
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h, hT1])
    have hzt : ∀ t ∈ T, z * t ∈ fusionSet R z := by
      intro t ht
      by_cases ht1 : t = 1
      · rw [ht1, mul_one]; exact self_mem_fusionSet hz1
      · have : t ∈ S₂ := heq ▸ ⟨ht, ht1⟩
        exact this.1.2
    have hc : Commute z t₀ := (hRz t₀ (hTR ht₀T)).symm
    set A := commPlane hp.pos hc (hexpR z hzR) (hexpR t₀ (hTR ht₀T)) with hA
    have hAR : A ≤ R := by
      rintro _ ⟨i, j, rfl⟩
      exact R.mul_mem (R.pow_mem hzR i) (R.pow_mem (hTR ht₀T) j)
    have ht₀p : orderOf t₀ = p := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hexpR t₀ (hTR ht₀T))) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) ht₀1
      · exact h1
    have hinf : Subgroup.zpowers z ⊓ Subgroup.zpowers t₀ = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
      by_contra hy1
      have := mem_zpowers_of_mem_zpowers_of_prime hp hzp hy.1 hy1
      exact hzT ((Subgroup.zpowers_le.mpr ht₀T) ((Subgroup.zpowers_le.mpr hy.2) this))
    have hAcard : Nat.card A = p ^ 2 := by
      refine le_antisymm (card_commPlane_le hp.pos hc _ _) ?_
      have h1 := mul_card_le_of_inf_eq_bot (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩ :
        Subgroup.zpowers z ≤ A) (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩ :
          Subgroup.zpowers t₀ ≤ A) hinf
      rw [Nat.card_zpowers, Nat.card_zpowers, hzp, ht₀p] at h1
      rw [sq]
      exact h1
    apply ht₀1
    refine hplane A hAR (isElemAbelian_commPlane hp.pos hc _ _) hAcard t₀ ⟨0, 1, by simp⟩
      fun b hbA hbt => ?_
    obtain ⟨i, j, rfl⟩ := hbA
    set m := i % p with hm
    have hzi : z ^ i = z ^ m := pow_congr_modEq (hexpR z hzR) (Nat.mod_modEq i p).symm
    have hm0 : m ≠ 0 := by
      intro h0
      apply hbt
      rw [hzi, h0, pow_zero, one_mul]
      exact Subgroup.npow_mem_zpowers t₀ j
    have hmp : m < p := Nat.mod_lt _ hp.pos
    obtain ⟨m', -, hmm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (Nat.coprime_of_lt_prime hm0 hmp hp).symm hp.one_lt
    have hmod : m * m' ≡ 1 [MOD p] := by
      unfold Nat.ModEq
      rw [hmm', Nat.mod_eq_of_lt hp.one_lt]
    have hmod' : m' * m ≡ 1 [MOD p] := by rw [mul_comm]; exact hmod
    have hb : (z * t₀ ^ (j * m')) ^ m = z ^ i * t₀ ^ j := by
      rw [(hc.pow_right _).mul_pow, ← pow_mul, hzi]
      congr 1
      rw [mul_assoc, pow_congr_modEq (hexpR t₀ (hTR ht₀T))
        (show j * (m' * m) ≡ j * 1 [MOD p] from Nat.ModEq.mul_left _ hmod'), mul_one]
    rw [← hb]
    refine pow_mem_fusionSet (hzt _ (T.pow_mem ht₀T _)) ?_
    rw [hb]
    intro h1
    apply hbt
    rw [h1]
    exact Subgroup.one_mem _
  rcases hsizes with h | ⟨-, h5, h⟩ | ⟨hA, h⟩
  · exact false_of_arith_trans hp (h S₁ hinv₁) (h S₂ hinv₂) hcase1 hcase2 hdvd
  · exact false_of_arith_lin h5 (h S₁ hinv₁) (h S₂ hinv₂) hcase1 hcase2 hdvd
  · rcases arith_alt hp hp2 (h S₁ hinv₁) (h S₂ hinv₂) hcase1 hcase2 hdvd with
      ⟨hc₂, hc₁⟩ | ⟨hp3, hc₂, hc₁⟩
    ·
      have hS₂e : S₂ = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hc₂
      have hO : ∀ t ∈ T, z * t ∈ fusionSet R z → t = 1 := by
        intro t ht hzt
        by_contra ht1
        have : t ∈ S₂ := ⟨⟨ht, hzt⟩, ht1⟩
        rw [hS₂e] at this
        exact this
      exact false_of_plane_lemma hp hTR hzR hzT hzp hTcard hRz hexpR hdec hxN hxz hO hc₁
    ·
      subst hp3
      have hS₂e : S₂ = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hc₂
      have hO : ∀ t ∈ T, z * t ∈ fusionSet R z → t = 1 := by
        intro t ht hzt
        by_contra ht1
        have : t ∈ S₂ := ⟨⟨ht, hzt⟩, ht1⟩
        rw [hS₂e] at this
        exact this
      have hS₁4 : S₁.ncard = 4 := by
        rcases h S₁ hinv₁ with h0 | h8 | h4 | h4
        · exact absurd h0 hc₁
        · exact absurd h8 hcase1
        · simpa using h4
        · simpa using h4
      have hZ : (fusionSet R z).ncard < 9 := by
        rw [hcount, hO'card, hc₂]
        have : (fusionSet R z ∩ (T : Set G)).ncard = 4 := hS₁4
        rw [this]
        norm_num
      exact hexo rfl hA hO hS₁4 hZ

theorem D1OneSmallData.false_of_ab_of_sizes
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G))
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1)
    (hsizes : (∀ S, D1InvSubset p H R K z S → S.ncard = 0 ∨ S.ncard = p ^ 2 - 1) ∨
      (IsSmallLinTwo p K ∧ 5 ≤ p ∧ ∀ S, D1InvSubset p H R K z S →
        S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ 2 * S.ncard = p ^ 2 - 1) ∨
      (IsAltTwoP p K ∧ ∀ S, D1InvSubset p H R K z S →
        S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ S.ncard = 2 * (p - 1) ∨ S.ncard = (p - 1) ^ 2))
    (hExo : ¬ (p = 3 ∧ IsAltTwoP 3 K ∧ D1SmallExotic p H R K z))
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) : False := by
  refine hd.false_of_ab_of_sizes_of_exotic hz hB0 hQz hdec hexpR hsizes ?_ hcard
  rintro rfl hA - hc₁ -
  have hp := hd.cfg.red.prime
  have hzp : orderOf z = 3 := hz.2.1
  obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (s := fusionSet R z ∩
    (d1LiftX 3 H R K : Set G)) (by omega)
  obtain ⟨⟨hw1, n, hn, hwn⟩, hwT⟩ := hw
  apply hExo
  refine ⟨rfl, hA, n, hn, ?_⟩
  have := mem_zpowers_of_mem_zpowers_of_prime hp (by
    have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
    rw [← hzp, ← this]
    rfl) hwn hw1
  exact (Subgroup.zpowers_le.mpr hwT) this

theorem D1OneSmallData.false_of_ab (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G))
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1) (hFi : ¬ (p = 5 ∧ IsFi22 K))
    (hExo : ¬ (p = 3 ∧ IsAltTwoP 3 K ∧ D1SmallExotic p H R K z))
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) : False :=
  hd.false_of_ab_of_sizes hz hB0 hQz hdec hexpR (hd.orbit_sizes hOrb hz hdec hFi hcard) hExo hcard

end Config

end CFSG.AGLEmbedding
