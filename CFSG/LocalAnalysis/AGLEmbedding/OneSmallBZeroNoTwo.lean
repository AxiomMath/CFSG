module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneSetup
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem noTwo_of_mulEquiv {p : ℕ} [Fact p.Prime] {K₁ K₂ : Type*} [Group K₁] [Group K₂] [Finite K₁]
    (e : K₁ ≃* K₂)
    (h : ∀ (S : Sylow p K₂) (W : Subgroup K₂), IsPGroup 2 W →
      (S : Subgroup K₂) ≤ Subgroup.normalizer (W : Set K₂) → W = ⊥) :
    ∀ (S : Sylow p K₁) (W : Subgroup K₁), IsPGroup 2 W →
      (S : Subgroup K₁) ≤ Subgroup.normalizer (W : Set K₁) → W = ⊥ := by
  intro S W hW hSW
  have h1 := h (S.mapSurjective (f := e.toMonoidHom) e.surjective) (W.map e.toMonoidHom)
    (hW.map _) (by
      show (S : Subgroup K₁).map e.toMonoidHom ≤ _
      exact (Subgroup.map_mono hSW).trans (Subgroup.le_normalizer_map _))
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem D1OneSmallData.twoCore_comm_mem_core_of_comp (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z)
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype)
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hPbar : (Pbar : Subgroup (D1CzQuot p z)) =
      (T : Subgroup _).map (QuotientGroup.mk' (primeComplementCore p)))
    (hKCn : KC.Normal) (hzZ : d1CzElt p z ∈ Subgroup.center (D1CzQuot p z))
    (hzp : orderOf (d1CzElt p z) = p) (hZKC : Subgroup.center KC = ⊥)
    (hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _))
    (hNoTwoKC : ∀ (S : Sylow p KC) (W : Subgroup KC), IsPGroup 2 W →
      (S : Subgroup KC) ≤ Subgroup.normalizer (W : Set KC) → W = ⊥)
    (hcard : Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    ∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) := by
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hTR : (T : Subgroup C).map C.subtype = R := by
    obtain ⟨T₀, hT₀⟩ := hB0
    refine (Subgroup.eq_of_le_of_card_ge hRT ?_).symm
    rw [← hT₀, Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective C.subtype_injective, T.card_eq_multiplicity,
      T₀.card_eq_multiplicity]
  obtain ⟨T₁, hT₁, -, -, -, -, -, -⟩ := hd.exists_sylow
  have := hKCn
  set π := QuotientGroup.mk' (primeComplementCore (G := C) p) with hπ
  set zt : D1CzQuot p z := d1CzElt p z with hzt
  obtain ⟨TC, hTC⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKCn.isSubnormal
  have hcard2 : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = Nat.card T₁ := by
    rw [hcardKC, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  have hcard3 : Nat.card (Pbar : Subgroup (D1CzQuot p z)) = Nat.card R := by
    rw [hPbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) T.isPGroup', ← hTR,
      Subgroup.card_map_of_injective C.subtype_injective]
  have hcard1 : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = Nat.card T₁ := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  have hztP : zt ∈ (Pbar : Subgroup (D1CzQuot p z)) := mem_sylow_of_mem_center hzZ hzp Pbar
  have hdisj : ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ⊓ Subgroup.zpowers zt = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy.2
    have hyZ : zt ^ j ∈ Subgroup.center (D1CzQuot p z) := Subgroup.zpow_mem _ hzZ j
    have hmem : (⟨zt ^ j, hy.1.2⟩ : KC) ∈ Subgroup.center KC :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hyZ k)
    rw [hZKC, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hsupeq : (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ⊔ Subgroup.zpowers zt = Pbar := by
    have hle : (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ⊔ Subgroup.zpowers zt ≤ Pbar :=
      sup_le inf_le_left (Subgroup.zpowers_le.mpr hztP)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := mul_card_le_of_inf_eq_bot (le_sup_left : (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ≤
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ⊔ Subgroup.zpowers zt) le_sup_right hdisj
    rw [Nat.card_zpowers, hzp, hcard2] at h1
    rw [hcard3]
    rw [hcard1] at hcard
    calc Nat.card R ≤ p * Nat.card T₁ := hcard
      _ = Nat.card T₁ * p := mul_comm _ _
      _ ≤ _ := h1
  set U : Subgroup G := pCoreOf 2 M ⊓ C with hU
  have hU2 : IsPGroup 2 U :=
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_left
  set Ut : Subgroup (D1CzQuot p z) := (U.subgroupOf C).map π with hUt
  have hUt2 : IsPGroup 2 Ut := (hU2.comap_subtype (K := C)).map _ |>.to_le (by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩)
  have hRU : ∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U := by
    intro r hr u hu
    refine ⟨(Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M
      (hd.cfg.ext.le_M hr)) u).mp hu.1, C.mul_mem (C.mul_mem (hd.le_centralizer_czElt hz hr) hu.2)
      (C.inv_mem (hd.le_centralizer_czElt hz hr))⟩
  have hPU : (Pbar : Subgroup (D1CzQuot p z)) ≤ Subgroup.normalizer (Ut : Set _) := by
    rw [hPbar]
    rintro _ ⟨t, ht, rfl⟩
    have htR : (t : G) ∈ R := hTR ▸ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨t * u * t⁻¹, hRU _ htR _ hu, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨u, hu, hueq⟩
      refine ⟨t⁻¹ * u * t, ?_, ?_⟩
      · show ((t⁻¹ * u * t : C) : G) ∈ U
        have := hRU _ (R.inv_mem htR) _ hu
        simpa using this
      · have h1 : π (t⁻¹ * u * t) = (π t)⁻¹ * π u * π t := by simp [map_mul, map_inv]
        rw [h1, hueq]
        group
  have hUK : Ut ⊓ KC = ⊥ := by
    set W : Subgroup KC := Ut.subgroupOf KC with hW
    have hW2 : IsPGroup 2 W := hUt2.comap_subtype
    have hSW : (TC : Subgroup KC) ≤ Subgroup.normalizer (W : Set KC) := by
      intro s hsT
      have hsP : ((s : KC) : D1CzQuot p z) ∈ (Pbar : Subgroup (D1CzQuot p z)) := by
        have : ((s : KC) : D1CzQuot p z) ∈ (TC : Subgroup KC).map KC.subtype := ⟨s, hsT, rfl⟩
        rw [hTC] at this
        exact this.1
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        show ((s * w * s⁻¹ : KC) : D1CzQuot p z) ∈ Ut
        have := (Subgroup.mem_normalizer_iff.mp (hPU hsP) (w : D1CzQuot p z)).mp hw
        simpa using this
      · intro hw
        show ((w : KC) : D1CzQuot p z) ∈ Ut
        have h1 := (Subgroup.mem_normalizer_iff.mp (hPU (Pbar.inv_mem hsP))
          ((s * w * s⁻¹ : KC) : D1CzQuot p z)).mp hw
        simpa [mul_assoc] using h1
    have hW1 := hNoTwoKC TC W hW2 hSW
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    have hy' : (⟨y, hy.2⟩ : KC) ∈ W := hy.1
    rw [hW1, Subgroup.mem_bot] at hy'
    exact congrArg Subtype.val hy'
  have hUcen : ∀ u ∈ Ut, ∀ r ∈ (Pbar : Subgroup (D1CzQuot p z)), u * r = r * u := by
    intro u hu r hr
    have hle : (Pbar : Subgroup (D1CzQuot p z)) ≤
        Subgroup.centralizer ({u} : Set (D1CzQuot p z)) := by
      rw [← hsupeq]
      refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.mpr ?_)
      ·
        have hcomm : u * t * u⁻¹ * t⁻¹ ∈ Ut ⊓ KC := by
          refine ⟨?_, ?_⟩
          · have h1 : t * u⁻¹ * t⁻¹ ∈ Ut :=
              (Subgroup.mem_normalizer_iff.mp (hPU ht.1) u⁻¹).mp (Ut.inv_mem hu)
            have h2 : u * t * u⁻¹ * t⁻¹ = u * (t * u⁻¹ * t⁻¹) := by group
            rw [h2]
            exact Ut.mul_mem hu h1
          · have h1 : u * t * u⁻¹ ∈ KC := hKCn.conj_mem t ht.2 u
            exact KC.mul_mem h1 (KC.inv_mem ht.2)
        rw [hUK, Subgroup.mem_bot] at hcomm
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : u * t * u⁻¹ = t := by
          calc u * t * u⁻¹ = u * t * u⁻¹ * t⁻¹ * t := by group
            _ = t := by rw [hcomm, one_mul]
        have h5 : u * t = t * u := by
          calc u * t = u * t * u⁻¹ * u := by group
            _ = t * u := by rw [this]
        exact h5.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp hzZ u).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hr)).symm
  have e1 : (primeComplementCore (G := C) p).map C.subtype = GLBPrimeCore p C := by
    rw [glbPrimeCore_eq_primeComplementCoreOf]
    rfl
  intro u hu r hr
  have huC : u ∈ C := hu.2
  have hrC : r ∈ C := hd.le_centralizer_czElt hz hr
  set c : C := ⟨u, huC⟩ * ⟨r, hrC⟩ * (⟨u, huC⟩ : C)⁻¹ * (⟨r, hrC⟩ : C)⁻¹ with hc
  have hcO : c ∈ primeComplementCore (G := C) p := by
    rw [← QuotientGroup.eq_one_iff (N := primeComplementCore (G := C) p)]
    have hut : π ⟨u, huC⟩ ∈ Ut := ⟨⟨u, huC⟩, hu, rfl⟩
    have hrt : π ⟨r, hrC⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) := by
      rw [hPbar]
      have : (⟨r, hrC⟩ : C) ∈ (T : Subgroup C) := by
        have hr' : r ∈ (T : Subgroup C).map C.subtype := hTR ▸ hr
        obtain ⟨t, ht, hteq⟩ := hr'
        have : t = ⟨r, hrC⟩ := Subtype.ext hteq
        rw [← this]
        exact ht
      exact ⟨_, this, rfl⟩
    have h1 := hUcen _ hut _ hrt
    show π c = 1
    simp only [hc, map_mul, map_inv, h1]
    group
  have h3 : (c : G) = u * r * u⁻¹ * r⁻¹ := by simp [hc]
  rw [← e1, ← h3]
  exact ⟨c, hcO, rfl⟩

theorem D1OneSmallData.twoCore_comm_mem_core (hNo2 : KFactSmallNoTwo)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hIso : D1CzIso p z K) (hFi : ¬ (p = 5 ∧ IsFi22 K))
    (hcard : Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    ∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.exists_sylow_centralizer hz
  have hTR : (T : Subgroup C).map C.subtype = R := by
    obtain ⟨T₀, hT₀⟩ := hB0
    refine (Subgroup.eq_of_le_of_card_ge hRT ?_).symm
    rw [← hT₀, Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective C.subtype_injective, T.card_eq_multiplicity,
      T₀.card_eq_multiplicity]
  obtain ⟨Pbar, hPbar, hred⟩ := hd.exists_reducedNongeneration_three hz hm hRT hTP
  obtain ⟨KC, hKC, hKCn, -, hzZ, hzp⟩ := hd.exists_component_czQuot hz hred
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
  obtain ⟨TC, hTC⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKCn.isSubnormal
  have hcard2 : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = Nat.card T₁ := by
    rw [← hTC, Subgroup.card_map_of_injective KC.subtype_injective, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]
  exact hd.twoCore_comm_mem_core_of_comp hz hB0 hRT hPbar hKCn hzZ hzp hZKC
    (by rw [hcard2, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective])
    (noTwo_of_mulEquiv e (hNo2 K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small hFi)) hcard

theorem D1OneSmallData.twoCore_inf_centralizer_le_of_comm (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hodd : ¬ D1CzEven p z)
    (hcomm : ∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) := by
  have hOodd : Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have huQ : r * u⁻¹ * r⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M
      (hd.cfg.ext.le_M hr)) _).mp ((pCoreOf 2 M).inv_mem hu.1)
  have hcQ : u * r * u⁻¹ * r⁻¹ ∈ pCoreOf 2 M := by
    have h := (pCoreOf 2 M).mul_mem hu.1 huQ
    simpa only [mul_assoc] using h
  obtain ⟨k, hk⟩ := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M ⟨_, hcQ⟩
  have hck : (u * r * u⁻¹ * r⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hco := Subgroup.orderOf_dvd_natCard _ (hcomm u hu r hr)
  have hcop : Nat.Coprime (2 ^ k)
      (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hOodd)
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hck) hco
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  calc r * u = (u * r * u⁻¹ * r⁻¹)⁻¹ * (u * r) := by group
    _ = u * r := by rw [h1, inv_one, one_mul]

theorem D1OneSmallData.twoCore_inf_centralizer_le (hNo2 : KFactSmallNoTwo)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hodd : ¬ D1CzEven p z) (hIso : D1CzIso p z K)
    (hFi : ¬ (p = 5 ∧ IsFi22 K))
    (hcard : Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) :=
  hd.twoCore_inf_centralizer_le_of_comm hodd (hd.twoCore_comm_mem_core hNo2 hz hB0 hIso hFi hcard)

end Config

end CFSG.AGLEmbedding
