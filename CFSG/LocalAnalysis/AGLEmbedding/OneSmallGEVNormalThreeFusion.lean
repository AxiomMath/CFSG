module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem eq_eight_of_dvd {c₁ c₂ : ℕ} (h₁ : c₁ = 0 ∨ c₁ = 3 ^ 2 - 1) (h₂ : c₂ = 0 ∨ c₂ = 3 ^ 2 - 1)
    (h : 3 ∣ c₁ + (3 - 1) * (1 + c₂)) : c₂ = 3 ^ 2 - 1 := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> first | rfl | (norm_num at h)

theorem D1OneSmallData.decomp_exp_of_b0 (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hL : ¬ (p = 3 ∧ IsLinThreeFour K)) :
    (∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) ∧ ∀ r ∈ R, r ^ p = 1 := by
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  refine ⟨hdec, fun r hr => ?_⟩
  obtain ⟨t, ht, i, rfl⟩ := hdec r hr
  have hc : Commute t (z ^ i) := Commute.pow_right
    (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
      (hRC (d1LiftX_le p H R K ht))) i
  rw [hc.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
    one_pow, one_mul]

theorem D1OneSmallData.mul_mem_fusionSet (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hA6 : ¬ IsAltTwoP 3 K) (hL : ¬ IsLinThreeFour K)
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) :
    ∀ t ∈ d1LiftX p H R K, z * t ∈ fusionSet R z := by
  subst hp3
  have hp := hd.cfg.red.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hdec, hexpR⟩ := hd.decomp_exp_of_b0 hOut hExp hz hB0 (fun h => hL h.2)
  set T := d1LiftX 3 H R K with hT
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = 3 := hz.2.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; exact absurd hzp (by norm_num)
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hzT, hTcard'⟩ := hd.d1LiftX_facts hz
  have hTcard : Nat.card T = 3 ^ 2 := hTcard'.trans hcard
  obtain ⟨x, hxP, hxN, hxR, -⟩ := hd.exists_moving_elt hz hB0
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpdvd : 3 ∣ (fusionSet R z).ncard := p_dvd_ncard_fusionSet hzp hxN hxk hxR
    (fun y hy hyz hyk => hd.mem_of_mem_normalizer_of_commute hB0 hy hyz hyk)
  have hcount := ncard_fusionSet_eq hp hTR hzR hzT hzp hRz hexpR hdec
  set S₁ : Set G := fusionSet R z ∩ (T : Set G) with hS₁
  set O' : Set G := {t | t ∈ T ∧ z * t ∈ fusionSet R z} with hO'
  set S₂ : Set G := O' \ {1} with hS₂
  have h1O' : (1 : G) ∈ O' := ⟨T.one_mem, by rw [mul_one]; exact self_mem_fusionSet hz1⟩
  have hO'card : O'.ncard = 1 + S₂.ncard := by
    rw [add_comm]
    exact (Set.ncard_sdiff_singleton_add_one h1O').symm
  have hdvd : 3 ∣ S₁.ncard + (3 - 1) * (1 + S₂.ncard) := by
    rw [← hO'card, ← hcount]
    exact hpdvd
  have hinv₁ : D1InvSubset 3 H R K z S₁ :=
    ⟨fun w hw => ⟨hw.2, hw.1.1⟩, fun n hn hnz hnT w hw =>
      ⟨conj_mem_fusionSet hn hw.1, hnT w hw.2⟩⟩
  have hinv₂ : D1InvSubset 3 H R K z S₂ := by
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
  have hT1 : ((T : Set G) \ {1}).ncard = 3 ^ 2 - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hTcard
  rcases hd.orbit_sizes hOrb hz hdec (fun h => by omega) hcard with h | ⟨-, h5, -⟩ | ⟨hA, -⟩
  · have h8 := eq_eight_of_dvd (h S₁ hinv₁) (h S₂ hinv₂) hdvd
    have heq := Set.eq_of_subset_of_ncard_le hinv₂.1 (by rw [h8, hT1])
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1, mul_one]; exact self_mem_fusionSet hz1
    · have : t ∈ S₂ := heq ▸ ⟨ht, ht1⟩
      exact this.1.2
  · omega
  · exact absurd hA hA6

theorem D1OneSmallData.mem_fusionSet_of_not_mem (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hA6 : ¬ IsAltTwoP 3 K) (hL : ¬ IsLinThreeFour K)
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) :
    ∀ r ∈ R, r ∉ d1LiftX p H R K → r ∈ fusionSet R z := by
  have hzt := hd.mul_mem_fusionSet hOut hExp hOrb hz hB0 hp3 hA6 hL hcard
  subst hp3
  obtain ⟨hdec, hexpR⟩ := hd.decomp_exp_of_b0 hOut hExp hz hB0 (fun h => hL h.2)
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hz3 : z ^ 3 = 1 := hexpR z hz.1
  intro r hr hrT
  obtain ⟨t, ht, i, rfl⟩ := hdec r hr
  have hct : Commute t z := Subgroup.mem_centralizer_singleton_iff.mp
    (hRC (d1LiftX_le 3 H R K ht))
  have ht3 : t ^ 3 = 1 := hexpR t (d1LiftX_le 3 H R K ht)
  have hzi : z ^ i = z ^ (i % 3) := by
    conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hz3, one_pow, mul_one]
  have hi3 : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [hzi] at hrT ⊢
  interval_cases h : i % 3
  · exact absurd (by simpa using ht) hrT
  · rw [pow_one, hct.eq]
    exact hzt t ht
  ·
    have hsq : (t * z ^ 2) ^ 2 = z * t ^ 2 := by
      have hc2 : Commute t (z ^ 2) := hct.pow_right 2
      rw [hc2.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hz3, one_mul,
        pow_one, ← hct.pow_left 2 |>.eq]
    have hmem : z * t ^ 2 ∈ fusionSet R z := hzt _ (Subgroup.pow_mem _ ht 2)
    have hr4 : ((t * z ^ 2) ^ 2) ^ 2 = t * z ^ 2 := by
      have h3 : (t * z ^ 2) ^ 3 = 1 := hexpR _ (R.mul_mem (d1LiftX_le 3 H R K ht)
        (R.pow_mem hz.1 2))
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [← hr4, hsq]
    refine pow_mem_fusionSet hmem ?_
    rw [← hsq, hr4]
    intro h1
    exact hrT (h1 ▸ Subgroup.one_mem _)

end CFSG.AGLEmbedding
