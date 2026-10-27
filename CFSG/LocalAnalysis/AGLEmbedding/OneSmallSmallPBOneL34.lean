module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPCube
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOne

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_b1_l34_of_comp (hGen : KFactL34OuterGen) (hAE : KFactL34AutExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnSP : ¬ D1CzSP p z) (hp3 : p = 3) (hOP : D1CzOuterP p z) {m : G}
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype)
    (hTP : (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom)
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hPbar : (Pbar : Subgroup (D1CzQuot p z)) =
      (T : Subgroup _).map (QuotientGroup.mk' (primeComplementCore p)))
    (hred : ReducedNongeneration p (D1CzQuot p z) Pbar
      (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p))))
    (hzZ : d1CzElt p z ∈ Subgroup.center (D1CzQuot p z)) (hzp : orderOf (d1CzElt p z) = p)
    (hKC : IsComponentOf KC ⊤) (hKCn : KC.Normal)
    (hKCu : ∀ L : Subgroup (D1CzQuot p z), IsComponentOf L ⊤ → L = KC)
    (hZKC : Subgroup.center KC = ⊥)
    (hzK : d1CzElt p z ∉ KC) (hLC : IsLinThreeFour KC)
    (hexp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, t ^ p = 1)
    (hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    False := by
  subst hp3
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨T₁, hT₁, hs, hnab, hcK, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  have := hKCn
  have hcard2 : Nat.card ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC : Subgroup _) = Nat.card T₁ := by
    rw [hcardKC, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  have hT₁9 : 9 ≤ Nat.card T₁ := by
    obtain ⟨n, hn⟩ := T₁.isPGroup'.exists_card_eq
    by_contra h9
    push Not at h9
    have hn1 : n ≤ 1 := by
      by_contra h2
      push Not at h2
      have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      omega
    apply hT₁nc
    interval_cases n
    · have : Subsingleton (T₁ : Subgroup K) := by
        rw [pow_zero] at hn
        exact (Nat.card_eq_one_iff_unique.mp hn).1
      infer_instance
    · rw [pow_one] at hn
      exact isCyclic_of_prime_card hn
  have hnc : ¬ IsCyclic ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC : Subgroup _) := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
      (α := ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC : Subgroup _))
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp g g.2)
    have h1 := orderOf_le_of_pow_eq_one (by norm_num) hg3
    omega
  obtain ⟨KC', hKC', x, ⟨k, hxk⟩, hxn⟩ := hOP
  rw [hKCu KC' hKC'] at hxn
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hxk)
    exact ⟨j, hj⟩
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨c, hcQ⟩ := MulAction.exists_smul_eq (D1CzQuot 3 z) Q Pbar
  set x' := c * x * c⁻¹ with hx'
  have hx'P : x' ∈ (Pbar : Subgroup (D1CzQuot 3 z)) := by
    rw [← hcQ, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨x, hQ (Subgroup.mem_zpowers x), rfl⟩
  have hNn : (KC ⊔ Subgroup.centralizer (KC : Set (D1CzQuot 3 z))).Normal := inferInstance
  have hx'n : x' ∉ KC ⊔ Subgroup.centralizer (KC : Set (D1CzQuot 3 z)) := by
    intro h
    apply hxn
    have : x = c⁻¹ * x' * c⁻¹⁻¹ := by rw [hx']; group
    rw [this]
    exact hNn.conj_mem _ h c⁻¹
  have hzP : d1CzElt 3 z ∈ (Pbar : Subgroup (D1CzQuot 3 z)) := mem_sylow_of_mem_center hzZ hzp Pbar
  have hzc : d1CzElt 3 z ∈ Subgroup.centralizer (KC : Set (D1CzQuot 3 z)) :=
    Subgroup.center_le_centralizer _ hzZ
  by_cases hx3 : x' ^ 3 = 1
  · exact hred.false_of_outer_three hGen hKC hLC hnc hzP hzK hzp hzc hx'P hx3
      (Subgroup.mem_center_iff.mp hzZ x') hx'n
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) 3
  have hx'T : x' ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)) :=
    hPbar ▸ hx'P
  obtain ⟨t₀, ht₀T, ht₀x⟩ := hx'T
  have ht₀3 : ((t₀ : Subgroup.centralizer ({z} : Set G)) : G) ^ 3 ≠ 1 := by
    intro h1
    apply hx3
    rw [← ht₀x, ← map_pow]
    have : t₀ ^ 3 = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
  set TG := (T : Subgroup (Subgroup.centralizer ({z} : Set G))).map
    (Subgroup.centralizer ({z} : Set G)).subtype with hTG
  set Y : Subgroup G := ((Subgroup.centralizer (KC : Set (D1CzQuot 3 z))).comap
    (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3))).map
      (Subgroup.centralizer ({z} : Set G)).subtype ⊓ TG with hY
  have hTp : IsPGroup 3 TG := T.isPGroup'.map (Subgroup.centralizer ({z} : Set G)).subtype
  have hYp : IsPGroup 3 Y := hTp.to_le inf_le_right
  have hmemP : ∀ s ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3) s ∈
        (Pbar : Subgroup (D1CzQuot 3 z)) :=
    fun s hs => hPbar ▸ ⟨s, hs, rfl⟩
  have hcube : ∀ s ∈ TG, s ^ 3 ∈ Y := by
    rintro _ ⟨sC, hsT, rfl⟩
    obtain ⟨n, hn⟩ := Pbar.isPGroup' ⟨_, hmemP sC hsT⟩
    have hCK := pow_three_mem_centralizer_of_isLinThreeFour hAE hLC
      (s := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3) sC)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hKCn]; exact Subgroup.mem_top _) (n := n)
      (by simpa using congrArg Subtype.val hn)
    rw [← map_pow] at hCK
    exact ⟨⟨sC ^ 3, hCK, by simp⟩, TG.pow_mem ⟨sC, hsT, rfl⟩ 3⟩
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzT : (⟨z, hzC⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      (T : Subgroup (Subgroup.centralizer ({z} : Set G))) := by
    obtain ⟨t, ht, hteq⟩ := hRT hz.1
    have : t = ⟨z, hzC⟩ := Subtype.ext hteq
    rw [← this]
    exact ht
  have hcyc := hred.isCyclic_inf_centralizer_of_not_mem_of_center hzZ hzp hKC hKCn hzK hZKC
  have hΩ : ∀ y ∈ Y, orderOf y = 3 → y ∈ Subgroup.zpowers z := by
    rintro _ ⟨⟨yC, hyC, rfl⟩, hyT⟩ hyp
    have hyCT : yC ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))) := by
      obtain ⟨y'', hy'', h''⟩ := hyT
      have : y'' = yC := Subtype.ext h''
      rw [← this]
      exact hy''
    have hyCp : orderOf yC = 3 := by rw [← Subgroup.orderOf_coe]; exact hyp
    have h1 := mem_zpowers_of_isCyclic_of_orderOf_eq_three hcyc ⟨hzP, hzc⟩ ⟨hmemP yC hyCT, hyC⟩
      hzp (orderOf_mk_of_coprime hp _ hO hyCp)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : (⟨z, hzC⟩ : Subgroup.centralizer ({z} : Set G)) ^ j = yC :=
      eq_of_mk_eq_of_isPGroup hp _ hO T.isPGroup'
        ((T : Subgroup (Subgroup.centralizer ({z} : Set G))).zpow_mem hzT j) hyCT
        (by rw [map_zpow]; exact hj)
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [← h2]; simp⟩
  have hrT : ((t₀ : Subgroup.centralizer ({z} : Set G)) : G) ∈ TG := ⟨t₀, ht₀T, rfl⟩
  have hQp : IsPGroup 3 ((P : Subgroup G).map (MulAut.conj m).toMonoidHom) := P.isPGroup'.map _
  have hQC : (P : Subgroup G).map (MulAut.conj m).toMonoidHom ⊓
      Subgroup.centralizer ({z} : Set G) ≤ TG := by
    rintro y ⟨hyQ, hyC⟩
    have hTeq : (T : Subgroup (Subgroup.centralizer ({z} : Set G))) =
        ((P : Subgroup G).map (MulAut.conj m).toMonoidHom).subgroupOf
          (Subgroup.centralizer ({z} : Set G)) :=
      (T.is_maximal' hQp.comap_subtype fun t ht => hTP ⟨t, ht, rfl⟩).symm
    have hy : (⟨y, hyC⟩ : Subgroup.centralizer ({z} : Set G)) ∈
        (T : Subgroup (Subgroup.centralizer ({z} : Set G))) := by
      rw [hTeq]
      exact hyQ
    exact ⟨_, hy, rfl⟩
  have hQT : (P : Subgroup G).map (MulAut.conj m).toMonoidHom = TG := by
    refine eq_of_isPGroup_of_le_of_normalizer hQp hTP fun g hgQ hgN => ?_
    have hgz := conj_mem_zpowers_of_cubes hYp hΩ hz.2.1 hcube hrT ht₀3 hgN
    have hgzN : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hgz n
    obtain ⟨j, hj⟩ := hQp ⟨g, hgQ⟩
    have hgj : g ^ 3 ^ j = 1 := by
      have h1 := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
    have hcomm := commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hz.2.1 hgzN hgj
    exact hQC ⟨hgQ, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq⟩
  apply hnSP
  have h4 : 4 ≤ Open.pRank 3 ((P : Subgroup G).map (MulAut.conj m).toMonoidHom) := by
    have := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta (m • P)
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
  rw [hQT] at h4
  exact h4.trans (pRank_mono 3 hp (Subgroup.map_subtype_le _))

theorem D1OneSmallData.false_of_b1_l34 (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hGen : KFactL34OuterGen) (hAE : KFactL34AutExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnSP : ¬ D1CzSP p z) (hnB0 : ¬ D1CzB0 p R z) (hIso : D1CzIso p z K) (hp3 : p = 3)
    (hL : IsLinThreeFour K) : False := by
  by_cases hOP : D1CzOuterP p z
  swap
  · exact hd.false_of_b1 hOut hExp hz hnSP hnB0 hIso (fun _ _ => hOP)
  subst hp3
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.exists_sylow_centralizer hz
  obtain ⟨Pbar, hPbar, hred⟩ := hd.exists_reducedNongeneration_three hz hm hRT hTP
  obtain ⟨KC, hKC, hKCn, hKCu, hzZ, hzp⟩ := hd.exists_component_czQuot hz hred
  obtain ⟨e⟩ := hIso KC hKC
  obtain ⟨T₁, hT₁, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  have := hKCn
  have hZKC : Subgroup.center KC = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => e.injective ?_
    have hey : e y ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k => by
      obtain ⟨k', rfl⟩ := e.surjective k
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy k']
    rw [hd.center, Subgroup.mem_bot] at hey
    rw [hey, map_one]
  have hzK : d1CzElt 3 z ∉ KC := by
    intro hzK
    have hmem : (⟨d1CzElt 3 z, hzK⟩ : KC) ∈ Subgroup.center KC :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hzZ k)
    rw [hZKC, Subgroup.mem_bot] at hmem
    have h1 : d1CzElt 3 z = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  have hLC : IsLinThreeFour KC := by
    obtain ⟨d, hdq, ⟨eK⟩⟩ := hL
    exact ⟨d, hdq, ⟨e.trans eK⟩⟩
  have hexp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := Pbar.isPGroup' ⟨t, ht.1⟩
    have htn : t ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hk1 : (⟨t, ht.2⟩ : KC) ^ 3 ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact htn)
    have h1 := hExp K hs hnab hc 3 hp hp2 T₁ hT₁nc hΓ hd.small (e ⟨t, ht.2⟩)
      ⟨n, by rw [← map_pow, hk1, map_one]⟩
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨TC, hTC⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKCn.isSubnormal
  have hcard2 : Nat.card ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC : Subgroup _) = Nat.card T₁ := by
    rw [← hTC, Subgroup.card_map_of_injective KC.subtype_injective, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]
  exact hd.false_of_b1_l34_of_comp hGen hAE hz hnSP rfl hOP hRT hTP hPbar hred hzZ hzp hKC hKCn
    hKCu hZKC hzK hLC hexp (by rw [hcard2, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective])

end Config

end CFSG.AGLEmbedding
