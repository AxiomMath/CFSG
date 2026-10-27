module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_isCyclic_of_orderOf_eq_three {Y : Subgroup G} (hY : IsCyclic Y) {z y : G}
    (hzY : z ∈ Y) (hyY : y ∈ Y) (hzp : orderOf z = 3) (hyp : orderOf y = 3) :
    y ∈ Subgroup.zpowers z := by
  have h1 : Subgroup.zpowers (⟨y, hyY⟩ : Y) = Subgroup.zpowers (⟨z, hzY⟩ : Y) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzp, hyp]
  have h2 : (⟨y, hyY⟩ : Y) ∈ Subgroup.zpowers (⟨z, hzY⟩ : Y) := h1 ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem conj_mem_zpowers_of_cubes {S Y : Subgroup G} {z : G} (hYp : IsPGroup 3 Y)
    (hΩ : ∀ y ∈ Y, orderOf y = 3 → y ∈ Subgroup.zpowers z) (hzp : orderOf z = 3)
    (hcube : ∀ s ∈ S, s ^ 3 ∈ Y) {r : G} (hr : r ∈ S) (hr3 : r ^ 3 ≠ 1) {x : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) : x * z * x⁻¹ ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set w := r ^ 3 with hw
  have hwY : w ∈ Y := hcube r hr
  obtain ⟨n, hn⟩ := hYp ⟨w, hwY⟩
  have hwn : w ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨a, ha, hwa⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hwn)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hwa
    exact hr3 hwa
  have hw₀ : orderOf (w ^ 3 ^ (a - 1)) = 3 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (by
      rw [hwa]; exact pow_dvd_pow 3 (Nat.sub_le a 1)), hwa]
    rw [show a = (a - 1) + 1 by omega, pow_succ, Nat.add_sub_cancel]
    exact Nat.mul_div_cancel_left 3 (pow_pos (by norm_num) _)
  have hw₀Y : w ^ 3 ^ (a - 1) ∈ Y := Y.pow_mem hwY _
  have hw₀z := hΩ _ hw₀Y hw₀
  have hw₀1 : w ^ 3 ^ (a - 1) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw₀; norm_num at hw₀
  have hzw : z ∈ Subgroup.zpowers w :=
    (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers w _))
      (mem_zpowers_of_mem_zpowers_of_prime Nat.prime_three hzp hw₀z hw₀1)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzw
  have hxr : x * r * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hx r).mp hr
  have hxw : x * w * x⁻¹ ∈ Y := by
    have := hcube _ hxr
    rw [conj_pow] at this
    exact this
  have hxz : x * z * x⁻¹ ∈ Y := by
    rw [← hk, ← conj_zpow]
    exact Y.zpow_mem hxw k
  refine hΩ _ hxz ?_
  rw [← hzp]
  exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective z

theorem pow_three_mem_centralizer_of_isLinThreeFour (hAE : KFactL34AutExp) {X : Type}
    [Group X] [Finite X] {K : Subgroup X} (hL : IsLinThreeFour K) {s : X}
    (hsN : s ∈ Subgroup.normalizer (K : Set X)) {n : ℕ} (hsn : s ^ 3 ^ n = 1) :
    s ^ 3 ∈ Subgroup.centralizer (K : Set X) := by
  set f : MulAut K := K.normalizerMonoidHom ⟨s, hsN⟩ with hf
  have hfn : f ^ 3 ^ n = 1 := by
    have h1 : (⟨s, hsN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 ^ n = 1 :=
      Subtype.ext (by simpa using hsn)
    rw [hf, ← map_pow, h1, map_one]
  have hf3 := hAE K hL f ⟨n, hfn⟩
  refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
  have h3 : (((f ^ 3) ⟨k, hk⟩ : K) : X) = s ^ 3 * k * (s ^ 3)⁻¹ := by
    rw [hf, ← map_pow]
    rfl
  have h2 : s ^ 3 * k * (s ^ 3)⁻¹ = k := by
    rw [← h3, hf3]
    rfl
  calc k * s ^ 3 = s ^ 3 * k * (s ^ 3)⁻¹ * s ^ 3 := by rw [h2]
    _ = s ^ 3 * k := by group

section Config

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_b0_cube (hAE : KFactL34AutExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K) {r : G} (hr : r ∈ R)
    (hr3 : r ^ 3 ≠ 1) : False := by
  subst hp3
  have hp := hd.cfg.red.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hO := primeComplementCore_coprime (G := H) 3
  have hRHp : IsPGroup 3 (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRHp ha hb hab
  set Yb := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) with hYb
  obtain ⟨z₀, hz₀R, hz₀K, hz₀p, hz₀c⟩ := hd.z
  have hKX₀ := (hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hz₀R hz₀K hz₀p hz₀c).2
  have hYbp : IsPGroup 3 Yb := Rbar.isPGroup'.to_le inf_le_left
  have hYcyc : IsCyclic Yb := by
    by_contra hnc
    have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp hd.cfg.red.ne_two hYbp hnc
    have h1 : Open.pRank 3 Yb ≤ 1 :=
      hd.cfg.red.pRank_inf_centralizer_le_one_of_not_le hd.comp hKX₀
    omega
  set Y : Subgroup G := ((Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))).comap
    π).map H.subtype ⊓ R with hY
  have hYp : IsPGroup 3 Y := hd.cfg.ext.isPGroup.to_le inf_le_right
  have hmemRb : ∀ y : H, y ∈ R.subgroupOf H → π y ∈ (Rbar : Subgroup _) := fun y hy => by
    rw [hd.cfg.rbar]
    exact ⟨y, hy, rfl⟩
  set zH : H := ⟨z, hz.2.2.1⟩ with hzH
  have hzHp : orderOf zH = 3 := by rw [← Subgroup.orderOf_coe]; exact hz.2.1
  have hzbY : π zH ∈ Yb := ⟨hmemRb zH hz.1, hz.2.2.2⟩
  have hzbp : orderOf (π zH) = 3 := orderOf_mk_of_coprime hp _ hO hzHp
  have hΩ : ∀ y ∈ Y, orderOf y = 3 → y ∈ Subgroup.zpowers z := by
    rintro _ ⟨⟨y', hy'C, rfl⟩, hyR⟩ hyp
    have hy'p : orderOf y' = 3 := by rw [← Subgroup.orderOf_coe]; exact hyp
    have hy'R : y' ∈ R.subgroupOf H := hyR
    have hybY : π y' ∈ Yb := ⟨hmemRb y' hy'R, hy'C⟩
    have h1 := mem_zpowers_of_isCyclic_of_orderOf_eq_three hYcyc hzbY hybY hzbp
      (orderOf_mk_of_coprime hp _ hO hy'p)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : zH ^ k = y' := hinj _ ((R.subgroupOf H).zpow_mem hz.1 k) _ hy'R
      (by rw [map_zpow, hk])
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      rw [← h2]
      simp [hzH]⟩
  have hcube : ∀ s ∈ R, s ^ 3 ∈ Y := by
    intro s hs
    set sH : H := ⟨s, hd.cfg.ext.le_H hs⟩ with hsH
    have hsR : sH ∈ R.subgroupOf H := hs
    obtain ⟨n, hn⟩ := Rbar.isPGroup' ⟨π sH, hmemRb sH hsR⟩
    have hC := pow_three_mem_centralizer_of_isLinThreeFour hAE hL
      (hd.cfg.red.sylow_le_normalizer_component hd.comp (hmemRb sH hsR)) (n := n)
      (by simpa using congrArg Subtype.val hn)
    rw [← map_pow] at hC
    exact ⟨⟨sH ^ 3, hC, by simp [hsH]⟩, R.pow_mem hs 3⟩
  have hPR : (P : Subgroup G) = R := by
    refine eq_of_isPGroup_of_le_of_normalizer P.isPGroup' hd.cfg.ext.le_P fun x hxP hxN => ?_
    have hxz := conj_mem_zpowers_of_cubes hYp hΩ hz.2.1 hcube hr hr3 hxN
    have hxzN : x ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hxz n
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc := commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hz.2.1 hxzN hxk
    exact hd.inf_centralizer_le_of_b0 hB0
      ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hc.eq⟩
  have h4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
  rw [hPR, hd.pRank_R] at h4
  omega

end Config

end CFSG.AGLEmbedding
