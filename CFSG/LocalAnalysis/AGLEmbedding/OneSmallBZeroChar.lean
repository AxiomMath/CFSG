module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_mul_eq_of_le_normalizer_sup_centralizer {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (S : Sylow p X) {K : Subgroup X}
    (hSN : (S : Subgroup X) ≤ Subgroup.normalizer (K : Set X))
    (hS : (S : Subgroup X) ≤ K ⊔ Subgroup.centralizer (K : Set X)) :
    ∀ r ∈ (S : Subgroup X), ∃ t ∈ (S : Subgroup X) ⊓ K,
      ∃ c ∈ (S : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), t * c = r := by
  set N := Subgroup.normalizer (K : Set X) with hN
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hCN : Subgroup.centralizer (K : Set X) ≤ N := Subgroup.centralizer_le_normalizer _
  have : (K.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have : ((Subgroup.centralizer (K : Set X)).subgroupOf N).Normal := by
    refine ⟨fun c hc n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro k hk
    have hnk : (n : X)⁻¹ * k * n ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem n.2) k).mp hk
      simpa using this
    have h1 := hc _ hnk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc k * (n * c * (n : X)⁻¹) = n * (((n : X)⁻¹ * k * n) * c) * (n : X)⁻¹ := by group
      _ = n * (c * ((n : X)⁻¹ * k * n)) * (n : X)⁻¹ := by rw [h1]
      _ = n * c * (n : X)⁻¹ * k := by group
  set S' : Sylow p N := S.subtype hSN
  have hS' : (S' : Subgroup N) ≤
      K.subgroupOf N ⊔ (Subgroup.centralizer (K : Set X)).subgroupOf N := by
    rw [← Subgroup.subgroupOf_sup hKN hCN]
    intro x hx
    exact hS hx
  have hP := le_inf_sup_of_le_sup_of_normal S' hS'
  intro r hr
  obtain ⟨t, ht, c, hc, htc⟩ := exists_mul_eq_of_le_inf_sup hP (show (⟨r, hSN hr⟩ : N) ∈
    (S' : Subgroup N) from hr)
  exact ⟨t, ⟨ht.1, ht.2⟩, c, ⟨hc.1, hc.2⟩, congrArg Subtype.val htc⟩

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.rbar_le_sup_centralizer (hOut : KFactSmallOutPPrime)
    (hd : D1OneSmallData p P M H R Rbar K) (hLa : D1SmallLa p M H Rbar K) :
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
      K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  by_cases hL : p = 3 ∧ IsLinThreeFour K
  · by_contra hn
    exact (hLa hL.1 hL.2).1 hn
  obtain ⟨T₁, -, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  intro r hr
  have hrN : r ∈ Subgroup.normalizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
    hd.cfg.red.sylow_le_normalizer_component hd.comp hr
  set f : MulAut K := K.normalizerMonoidHom ⟨r, hrN⟩ with hf
  obtain ⟨n, hn⟩ := Rbar.isPGroup' ⟨r, hr⟩
  have hrn : r ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hfn : f ^ p ^ n = 1 := by
    have h1 : (⟨r, hrN⟩ : Subgroup.normalizer (K : Set _)) ^ p ^ n = 1 :=
      Subtype.ext (by simpa using hrn)
    rw [hf, ← map_pow, h1, map_one]
  obtain ⟨κ, hκ⟩ := hOut K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small hL f ⟨n, hfn⟩
  have hcen : (κ : H ⧸ primeComplementCore (G := H) p)⁻¹ * r ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have h1 := congrArg (fun g : MulAut K =>
      ((g ⟨k, hk⟩ : K) : H ⧸ primeComplementCore (G := H) p)) hκ
    simp only [MulAut.conj_apply, hf] at h1
    have h2 : (κ : H ⧸ primeComplementCore (G := H) p) * k * (κ : H ⧸ _)⁻¹ = r * k * r⁻¹ :=
      calc (κ : H ⧸ primeComplementCore (G := H) p) * k * (κ : H ⧸ _)⁻¹
          = ((κ * ⟨k, hk⟩ * κ⁻¹ : K) : H ⧸ primeComplementCore (G := H) p) := by simp
        _ = _ := h1
        _ = r * k * r⁻¹ := rfl
    calc k * ((κ : H ⧸ primeComplementCore (G := H) p)⁻¹ * r)
        = (κ : H ⧸ _)⁻¹ * ((κ : H ⧸ _) * k * (κ : H ⧸ _)⁻¹) * r := by group
      _ = (κ : H ⧸ _)⁻¹ * (r * k * r⁻¹) * r := by rw [h2]
      _ = (κ : H ⧸ _)⁻¹ * r * k := by group
  have : r = (κ : H ⧸ primeComplementCore (G := H) p) * ((κ : H ⧸ _)⁻¹ * r) := by group
  rw [this]
  exact Subgroup.mul_mem_sup κ.2 hcen

theorem D1OneSmallData.card_le_and_decomp_of_b0_of_le_sup (hExp : KFactSmallSylowExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z)
    (hRK : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
      K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) :
    Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) ∧
      ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hO := primeComplementCore_coprime (G := H) p
  have hRHp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRHp ha hb hab
  set zb := π ⟨z, hz.2.2.1⟩ with hzb
  have hzbR : zb ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact ⟨⟨z, hz.2.2.1⟩, hz.1, rfl⟩
  have hzbC : zb ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
    hz.2.2.2
  have hzbp : orderOf zb = p := orderOf_mk_of_coprime hp _ hO
    (by rw [← Subgroup.orderOf_coe]; exact hz.2.1)
  have hdec := exists_mul_eq_of_le_normalizer_sup_centralizer Rbar
    (fun r hr => hd.cfg.red.sylow_le_normalizer_component hd.comp hr) hRK
  set Y := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hY
  obtain ⟨z₀, hz₀R, hz₀K, hz₀p, hz₀c⟩ := hd.z
  have hKX₀ := (hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hz₀R hz₀K hz₀p hz₀c).2
  have hYp : IsPGroup p Y := Rbar.isPGroup'.to_le inf_le_left
  have hYcyc : IsCyclic Y := by
    by_contra hnc
    have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp hp2 hYp hnc
    have h1 : Open.pRank p Y ≤ 1 :=
      hd.cfg.red.pRank_inf_centralizer_le_one_of_not_le hd.comp hKX₀
    omega
  have hzY : zb ∈ Y := ⟨hzbR, hzbC⟩
  have hYle : Nat.card Y ≤ p := by
    by_contra hlt
    push Not at hlt
    obtain ⟨T₁, -, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
    have hexp : ∀ t ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K, t ^ p = 1 := by
      intro t ht
      obtain ⟨n, hn⟩ := Rbar.isPGroup' ⟨t, ht.1⟩
      have htn : t ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hk1 : (⟨t, ht.2⟩ : K) ^ p ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact htn)
      have h1 := hExp K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small ⟨t, ht.2⟩ ⟨n, hk1⟩
      simpa using congrArg Subtype.val h1
    have hcomm : ∀ a ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K,
        ∀ c ∈ Y, Commute a c :=
      fun a ha c hc => Subgroup.mem_centralizer_iff.mp hc.2 a ha.2
    obtain ⟨N, hN, ho⟩ := exists_pow_eq_of_decomp hp hzY hzbp hYp hlt inf_le_left hexp hcomm
      hdec
    rw [hd.cfg.rbar] at hN ho
    have hzRH : (⟨z, hz.2.2.1⟩ : H) ∈ R.subgroupOf H := hz.1
    obtain ⟨hN', o', ho', ho'z⟩ := exists_pow_eq_of_map hp _ hO hRHp hzRH hN ho
    have hNG : ∀ t ∈ R, t ^ N ∈ Subgroup.zpowers z := by
      intro t ht
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
        (hN' ⟨t, hd.cfg.ext.le_H ht⟩ (show (⟨t, hd.cfg.ext.le_H ht⟩ : H) ∈ R.subgroupOf H from ht))
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩
    have hoG : ∃ o ∈ R, o ^ N = z :=
      ⟨o', ho', by simpa using congrArg Subtype.val ho'z⟩
    have hPR := eq_of_pow_mem_zpowers P.isPGroup' hd.cfg.ext.le_P hz.2.1
      (hd.inf_centralizer_le_of_b0 hB0) hNG hoG
    have h4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
    rw [hPR, hd.pRank_R] at h4
    omega
  have hYz : Y = Subgroup.zpowers zb := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzY) ?_).symm
    rw [Nat.card_zpowers, hzbp]
    exact hYle
  have hcardR : Nat.card R = Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar, card_map_mk_of_isPGroup hp _ hO hRHp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd.cfg.ext.le_H).toEquiv]
  refine ⟨?_, ?_⟩
  · have h1 := card_le_mul_of_decomp (inf_le_left : Y ≤ _) hdec
    rw [hcardR]
    calc _ ≤ _ := h1
      _ ≤ _ * p := Nat.mul_le_mul_left _ hYle
      _ = _ := mul_comm _ _
  · intro r hr
    have hrH : r ∈ H := hd.cfg.ext.le_H hr
    have hrb : π ⟨r, hrH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
      rw [hd.cfg.rbar]
      exact ⟨⟨r, hrH⟩, hr, rfl⟩
    obtain ⟨tb, htb, cb, hcb, htc⟩ := hdec _ hrb
    rw [hYz] at hcb
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, zb ^ i = cb := by
      have hfin : IsOfFinOrder zb := isOfFinOrder_of_finite zb
      rw [← hfin.mem_powers_iff_mem_zpowers] at hcb
      exact hcb
    have htb' := htb.1
    rw [hd.cfg.rbar] at htb'
    obtain ⟨t, ht, rfl⟩ := htb'
    refine ⟨t, ⟨t, ⟨ht, htb.2⟩, rfl⟩, i, ?_⟩
    have hmem : t * ⟨z, hz.2.2.1⟩ ^ i ∈ R.subgroupOf H :=
      (R.subgroupOf H).mul_mem ht ((R.subgroupOf H).pow_mem hz.1 i)
    have h1 := hinj _ (show (⟨r, hrH⟩ : H) ∈ R.subgroupOf H from hr) _ hmem
      (by rw [map_mul, map_pow, ← htc])
    have h2 := congrArg Subtype.val h1
    simpa using h2

theorem D1OneSmallData.card_le_and_decomp_of_b0 (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hLa : D1SmallLa p M H Rbar K) :
    Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) ∧
      ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i :=
  hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0 (hd.rbar_le_sup_centralizer hOut hLa)

theorem D1OneSmallData.pow_eq_one_of_mem_d1LiftX (hExp : KFactSmallSylowExp)
    (hd : D1OneSmallData p P M H R Rbar K) {t : G} (ht : t ∈ d1LiftX p H R K) : t ^ p = 1 := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, -, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  obtain ⟨t', ⟨htR, htK⟩, rfl⟩ := ht
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hO := primeComplementCore_coprime (G := H) p
  have hRHp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  obtain ⟨n, hn⟩ := hRHp ⟨t', htR⟩
  have htn : t' ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hk1 : (⟨π t', htK⟩ : K) ^ p ^ n = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; simp [← map_pow, htn])
  have h1 := hExp K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small ⟨π t', htK⟩ ⟨n, hk1⟩
  have h2 : π (t' ^ p) = π 1 := by
    rw [map_pow, map_one]
    simpa using congrArg Subtype.val h1
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRHp ha hb hab
  have h3 := hinj _ ((R.subgroupOf H).pow_mem htR p) _ (R.subgroupOf H).one_mem h2
  simpa using congrArg Subtype.val h3

end Config

end CFSG.AGLEmbedding
