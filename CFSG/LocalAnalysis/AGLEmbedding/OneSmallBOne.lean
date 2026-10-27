module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneSetup
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_b1_of_comp (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hnSP : ¬ D1CzSP p z) (hnB0 : ¬ D1CzB0 p R z) {m : G}
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
    (hKC : IsComponentOf KC ⊤) (hKCn : KC.Normal) (hZKC : Subgroup.center KC = ⊥)
    (hzK : d1CzElt p z ∉ KC)
    (hB : ∀ x : D1CzQuot p z, (∃ n : ℕ, x ^ p ^ n = 1) →
      x ∈ KC ⊔ Subgroup.centralizer (KC : Set (D1CzQuot p z)))
    (hexp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, t ^ p = 1)
    (hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    False := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, -, -, -, -, -, -⟩ := hd.exists_sylow
  have := hKCn
  have hPKC : (Pbar : Subgroup (D1CzQuot p z)) ≤
      KC ⊔ Subgroup.centralizer (KC : Set (D1CzQuot p z)) := fun x hx => hB x (by
    obtain ⟨n, hn⟩ := Pbar.isPGroup' ⟨x, hx⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩)
  have hdec : ∀ r ∈ (Pbar : Subgroup (D1CzQuot p z)), ∃ t ∈ (Pbar : Subgroup _) ⊓ KC,
      ∃ c ∈ (Pbar : Subgroup _) ⊓ Subgroup.centralizer (KC : Set (D1CzQuot p z)), t * c = r :=
    fun r hr => exists_mul_eq_of_le_inf_sup (le_inf_sup_of_le_sup_of_normal Pbar hPKC) hr
  set Y := (Pbar : Subgroup (D1CzQuot p z)) ⊓ Subgroup.centralizer (KC : Set (D1CzQuot p z))
    with hYdef
  have hYcyc : IsCyclic Y := hred.isCyclic_inf_centralizer_of_not_mem_of_center hzZ hzp hKC hKCn
    hzK hZKC
  have hzY : d1CzElt p z ∈ Y :=
    ⟨mem_sylow_of_mem_center hzZ hzp Pbar, Subgroup.center_le_centralizer _ hzZ⟩
  have hYp : IsPGroup p Y := Pbar.isPGroup'.to_le inf_le_left
  have hcomm : ∀ a ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, ∀ c ∈ Y, Commute a c :=
    fun a ha c hc => Subgroup.mem_centralizer_iff.mp hc.2 a ha.2
  have hcard1 : Nat.card (Pbar : Subgroup (D1CzQuot p z)) ≤
      Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) * Nat.card Y :=
    card_le_mul_of_decomp inf_le_left hdec
  have hcard2 : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = Nat.card T₁ := by
    rw [hcardKC, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  have hcard3 : Nat.card (Pbar : Subgroup (D1CzQuot p z)) =
      Nat.card ((T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype) := by
    rw [hPbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) T.isPGroup',
      Subgroup.card_map_of_injective (Subgroup.centralizer ({z} : Set G)).subtype_injective]
  have hRne : R ≠ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype :=
    fun h => hnB0 ⟨T, h.symm⟩
  have hcard4 := Subgroup.card_lt_of_lt (lt_of_le_of_ne hRT hRne)
  set zbar := QuotientGroup.mk' (primeComplementCore (G := H) p) (⟨z, hz.2.2.1⟩ : H)
    with hzbar
  have hzbR : zbar ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact ⟨⟨z, hz.2.2.1⟩, hz.1, rfl⟩
  have hzbC : zbar ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
    hz.2.2.2
  have hzbp : orderOf zbar = p := orderOf_mk_of_coprime hp _ (primeComplementCore_coprime p)
    (by rw [← Subgroup.orderOf_coe]; exact hz.2.1)
  have hdisj : ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊓
      Subgroup.zpowers zbar = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    have hyC : y ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
      Subgroup.zpowers_le.mpr hzbC hy.2
    have hmem : (⟨y, hy.1.2⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun k =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC k k.2)
    rw [hd.center, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hcard5 := mul_card_le_of_inf_eq_bot inf_le_left (Subgroup.zpowers_le.mpr hzbR) hdisj
  have hRHp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  rw [Nat.card_zpowers, hzbp, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
    hd.cfg.rbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hRHp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd.cfg.ext.le_H).toEquiv] at hcard5
  have hYcard : p < Nat.card Y := by
    rw [hcard2, hcard3] at hcard1
    have h1 : Nat.card T₁ * p < Nat.card T₁ * Nat.card Y := by omega
    exact Nat.lt_of_mul_lt_mul_left h1
  obtain ⟨N, hN, ho⟩ := exists_pow_eq_of_decomp hp hzY hzp hYp hYcard inf_le_left hexp hcomm hdec
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzT : (⟨z, hzC⟩ : Subgroup.centralizer ({z} : Set G)) ∈ (T : Subgroup _) := by
    obtain ⟨t, ht, hteq⟩ := hRT hz.1
    have : t = ⟨z, hzC⟩ := Subtype.ext hteq
    rw [← this]
    exact ht
  rw [hPbar] at hN ho
  obtain ⟨hN', o', ho', ho'z⟩ := exists_pow_eq_of_map hp _ (primeComplementCore_coprime p)
    T.isPGroup' hzT hN ho
  have hNG : ∀ t ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
      t ^ N ∈ Subgroup.zpowers z := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hN' t ht)
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by
      simpa using congrArg Subtype.val hj⟩
  have hoG : ∃ o ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
      o ^ N = z := ⟨o', ⟨o', ho', rfl⟩, by simpa using congrArg Subtype.val ho'z⟩
  have hQp : IsPGroup p ((P : Subgroup G).map (MulAut.conj m).toMonoidHom) := P.isPGroup'.map _
  have hQC : (P : Subgroup G).map (MulAut.conj m).toMonoidHom ⊓
      Subgroup.centralizer ({z} : Set G) ≤
        (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype := by
    rintro x ⟨hxQ, hxC⟩
    have hTeq : (T : Subgroup (Subgroup.centralizer ({z} : Set G))) =
        ((P : Subgroup G).map (MulAut.conj m).toMonoidHom).subgroupOf _ :=
      (T.is_maximal' hQp.comap_subtype fun t ht => hTP ⟨t, ht, rfl⟩).symm
    have hx : (⟨x, hxC⟩ : Subgroup.centralizer ({z} : Set G)) ∈ (T : Subgroup _) := by
      rw [hTeq]
      exact hxQ
    exact ⟨_, hx, rfl⟩
  have hQT := eq_of_pow_mem_zpowers hQp hTP hz.2.1 hQC hNG hoG
  apply hnSP
  have h4 : 4 ≤ Open.pRank p ((P : Subgroup G).map (MulAut.conj m).toMonoidHom) := by
    have := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta (m • P)
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
  rw [hQT] at h4
  exact h4.trans (pRank_mono p hp (Subgroup.map_subtype_le _))

theorem D1OneSmallData.false_of_b1 (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnSP : ¬ D1CzSP p z) (hnB0 : ¬ D1CzB0 p R z) (hIso : D1CzIso p z K)
    (hL34 : p = 3 → IsLinThreeFour K → ¬ D1CzOuterP p z) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.exists_sylow_centralizer hz
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
  have hzK : d1CzElt p z ∉ KC := by
    intro hzK
    have hmem : (⟨d1CzElt p z, hzK⟩ : KC) ∈ Subgroup.center KC :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hzZ k)
    rw [hZKC, Subgroup.mem_bot] at hmem
    have h1 : d1CzElt p z = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  have hB : ∀ x : D1CzQuot p z, (∃ n : ℕ, x ^ p ^ n = 1) →
      x ∈ KC ⊔ Subgroup.centralizer (KC : Set (D1CzQuot p z)) := by
    intro x hx
    by_cases hL : p = 3 ∧ IsLinThreeFour K
    · by_contra hxn
      exact hL34 hL.1 hL.2 ⟨KC, hKC, x, hx, hxn⟩
    · obtain ⟨n, hxn⟩ := hx
      refine mem_sup_centralizer_of_congr e
        (hOut K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small hL _ ⟨n, ?_⟩)
      rw [← map_pow, ← map_pow, hxn, map_one, map_one]
  have hexp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, t ^ p = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := Pbar.isPGroup' ⟨t, ht.1⟩
    have htn : t ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hk1 : (⟨t, ht.2⟩ : KC) ^ p ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact htn)
    have h1 := hExp K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small (e ⟨t, ht.2⟩)
      ⟨n, by rw [← map_pow, hk1, map_one]⟩
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨TC, hTC⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKCn.isSubnormal
  have hcard2 : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = Nat.card T₁ := by
    rw [← hTC, Subgroup.card_map_of_injective KC.subtype_injective, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]
  exact hd.false_of_b1_of_comp hz hnSP hnB0 hRT hTP hPbar hred hzZ hzp hKC hKCn hZKC hzK hB hexp
    (by rw [hcard2, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective])

end Config

theorem stmtSmallBOne_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) :
    StmtSmallBOne := by
  intro G _ _ p P M H R Rbar K hd _ z hz hnSP hnB0 hIso _ hL34
  exact hd.false_of_b1 hOut hExp hz hnSP hnB0 hIso hL34

end CFSG.AGLEmbedding
