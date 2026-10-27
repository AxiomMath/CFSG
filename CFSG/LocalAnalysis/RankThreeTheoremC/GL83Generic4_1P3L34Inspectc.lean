module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspectb
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34insp_hom_eq_one_iff {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsL34Normal M x J) (c : ↥(centralizer ({x} : Set G))) :
    l34Hom x J c = 1 ↔
      QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
        reducedCentralizerOfJ x J := by
  have hDn := l34_reducedCentralizer_normal hJ
  have h : l34Hom x J c = QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c) := rfl
  rw [h, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self]

theorem l34insp_eq_one_of_two (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    {c : ↥(centralizer ({x} : Set G))} {k : ℕ} (hc : (c : G) ^ 2 ^ k = 1)
    (h1 : l34Hom x J c = 1) : c = 1 := by
  have hDp := l34_reducedCentralizer_isPGroup hS hU0 hK1 hK2 hp hM hgen hJ
  have hπD := (l34insp_hom_eq_one_iff hJ c).mp h1
  obtain ⟨m, hm⟩ := hDp ⟨_, hπD⟩
  have hm' : (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c) ^
      3 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  have hk' : (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c) ^
      2 ^ k = 1 := by
    rw [← map_pow]
    have : c ^ 2 ^ k = 1 := Subtype.ext (by simpa using hc)
    rw [this, map_one]
  have hcop : Nat.Coprime (3 ^ m) (2 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  have hπ1 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk'))
  have hcO : (c : G) ∈ GLBPrimeCore 3 (centralizer ({x} : Set G)) :=
    (CFSG.AGLEmbedding.mk'_primeComplementCore_eq_one_iff 3 c).mp hπ1
  have hcP : (c : G) ∈ CFSG.ABGTheoremB.pPrimeCoreIn 3 (centralizer ({x} : Set G)) :=
    glbPrimeCore_le_pPrimeCoreIn 3 _ hcO
  have hodd := odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hgen.2.2.2.ge hgen.2.1.2.2.2.2
  have h2 : orderOf (c : G) ∣
      Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn 3 (centralizer ({x} : Set G))) := by
    have := orderOf_dvd_natCard
      (⟨c, hcP⟩ : CFSG.ABGTheoremB.pPrimeCoreIn 3 (centralizer ({x} : Set G)))
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf (c : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc
  have h4 : orderOf (c : G) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases j with _ | j
    · rwa [pow_zero] at hj
    · exfalso
      rw [hj, pow_succ] at h2
      exact hodd (dvd_of_mul_left_dvd h2)
  exact Subtype.ext (orderOf_eq_one_iff.mp h4)

theorem l34insp_eq_one_of_three {M : Subgroup G} {x : G} {J : Subgroup G}
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hJ : IsL34Normal M x J) {j : G}
    (hjJ : j ∈ J) (hj3 : j ^ 3 = 1) (h1 : l34Hom x J ⟨j, hJ.le_centralizer hjJ⟩ = 1) :
    j = 1 := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hπD := (l34insp_hom_eq_one_iff hJ _).mp h1
  have hπJ : QuotientGroup.mk' (primeComplementCore (G := C) 3) ⟨j, hJ.le_centralizer hjJ⟩ ∈
      r1sBar x J := ⟨_, Subgroup.mem_subgroupOf.mpr hjJ, rfl⟩
  have hπ1 : QuotientGroup.mk' (primeComplementCore (G := C) 3) ⟨j, hJ.le_centralizer hjJ⟩ = 1 := by
    have h : QuotientGroup.mk' (primeComplementCore (G := C) 3) ⟨j, hJ.le_centralizer hjJ⟩ ∈
        r1sBar x J ⊓ reducedCentralizerOfJ x J := ⟨hπJ, hπD⟩
    rw [l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ, Subgroup.mem_bot] at h
    exact h
  have hjO : (⟨j, hJ.le_centralizer hjJ⟩ : C) ∈ primeComplementCore (G := C) 3 :=
    (QuotientGroup.eq_one_iff _).mp hπ1
  have h2 : orderOf (⟨j, hJ.le_centralizer hjJ⟩ : C) ∣
      Nat.card (primeComplementCore (G := C) 3) := by
    have := orderOf_dvd_natCard (⟨_, hjO⟩ : primeComplementCore (G := C) 3)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf (⟨j, hJ.le_centralizer hjJ⟩ : C) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hj3))
  have h4 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (primeComplementCore_coprime 3) h3 h2)
  exact congrArg Subtype.val h4

theorem l34insp_hom_self {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
    l34Hom x J ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ = 1 := by
  rw [l34insp_hom_eq_one_iff hJ, r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
  intro h _
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective (primeComplementCore (G := centralizer ({x} : Set G)) 3) h
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp c.2)

theorem l34insp_hom_mem_normalizer (x : G) (J A : Subgroup G)
    {u : ↥(centralizer ({x} : Set G))} (hu : (u : G) ∈ normalizer (A : Set G)) :
    l34Hom x J u ∈ normalizer ((l34Img x J A : Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
  have hu' : u ∈ normalizer ((A.subgroupOf (centralizer ({x} : Set G)) :
      Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G))) := by
    rw [mem_normalizer_iff]
    intro c
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.mp hu c
  exact Subgroup.le_normalizer_map (l34Hom x J) ⟨u, hu', rfl⟩

theorem l34insp_sylow (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK4 : KFactL34Borel) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) {U : Subgroup G}
    (hU : IsPGroup 3 U) {u : G} (huU : u ∈ U) (huJ : u ∈ J) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    (hUxu : U ≤ zpowers x ⊔ zpowers u) {S₂ : Subgroup G}
    (hS₂ : invariantTwoMaximalWithin U J S₂) :
    IsSylowOf 2 (l34Img x J S₂) (l34Img x J J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hxJ : ∀ j ∈ J, x * j = j * x := fun j hj =>
    (mem_centralizer_singleton_iff.mp (hJC hj)).symm
  obtain ⟨-, -, hKt⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  set K : Subgroup (L34Quot x J) := l34Img x J J with hK
  set f : ↥J →* L34Quot x J := (l34Hom x J).comp (Subgroup.inclusion hJC) with hf
  have hfrange : f.range = K := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    by_contra hnc
    have hdvd : 3 ∣ Nat.card f.ker := by
      by_contra hnd
      exact hnc (Nat.prime_three.coprime_iff_not_dvd.mpr hnd)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 3 hdvd
    have hg3 : ((g : ↥J) : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      simpa using congrArg (fun y : f.ker => ((y : ↥J) : G)) this
    have h1 := l34insp_eq_one_of_three hK1 hK2 hJ (g : ↥J).2 hg3 g.2
    have : g = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hg
    omega
  have hũK : l34Hom x J ⟨u, hJC huJ⟩ ∈ K := ⟨⟨u, hJC huJ⟩, Subgroup.mem_subgroupOf.mpr huJ, rfl⟩
  have hũ1 : l34Hom x J ⟨u, hJC huJ⟩ ≠ 1 := fun h =>
    hu1 (l34insp_eq_one_of_three hK1 hK2 hJ huJ hu3 h)
  have hũ3 : l34Hom x J ⟨u, hJC huJ⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨u, hJC huJ⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [this, map_one]
  set uK : ↥K := ⟨l34Hom x J ⟨u, hJC huJ⟩, hũK⟩ with huK
  have huKo : orderOf uK = 3 := by
    rw [huK, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hũ3 hũ1
  have hfS : ∀ (s : G) (hs : s ∈ S₂), f ⟨s, hS₂.1 hs⟩ ∈ l34Img x J S₂ := fun s hs =>
    ⟨⟨s, hJC (hS₂.1 hs)⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hStK : l34Img x J S₂ ≤ K := Subgroup.map_mono fun c hc => hS₂.1 hc
  have hSt2 : IsPGroup 2 (l34Img x J S₂) := (hS₂.2.1.comap_subtype (K := C)).map _
  have hũN : l34Hom x J ⟨u, hJC huJ⟩ ∈
      normalizer ((l34Img x J S₂ : Subgroup (L34Quot x J)) : Set (L34Quot x J)) :=
    l34insp_hom_mem_normalizer x J S₂ (hS₂.2.2.1 huU)
  set V : Subgroup ↥K := (l34Img x J S₂).subgroupOf K with hV
  have huKV : uK ∈ normalizer (V : Set ↥K) := by
    rw [hV, ← Subgroup.subgroupOf_normalizer_eq hStK]
    exact hũN
  have hmax : rankTwoMaximalInvariantTwoSubgroup (zpowers uK) V := by
    refine ⟨hSt2.comap_subtype, zpowers_le.mpr huKV, fun L hL2 hLu hVL => ?_⟩
    have hLu' : uK ∈ normalizer (L : Set ↥K) := zpowers_le.mp hLu
    obtain ⟨W, hSW, hWJ, hW2, hUW, hWV⟩ := l34insp_lift f hU huJ hUxu hxJ hker
      (V := L.map K.subtype) (hL2.map _) (by rw [hfrange]; exact Subgroup.map_subtype_le _)
      (Subgroup.le_normalizer_map K.subtype ⟨uK, hLu', rfl⟩) hS₂.1 hS₂.2.1 hS₂.2.2.1
      (fun s hs => ⟨⟨f ⟨s, hS₂.1 hs⟩, hStK (hfS s hs)⟩,
        hVL (Subgroup.mem_subgroupOf.mpr (hfS s hs)), rfl⟩)
    have hWeq : W = S₂ := hS₂.2.2.2 W hWJ hW2 hUW hSW
    refine le_antisymm (fun l hl => ?_) hVL
    obtain ⟨s, hs, hsW, hsl⟩ := hWV (l : L34Quot x J) ⟨l, hl, rfl⟩
    rw [hWeq] at hsW
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [← hsl]
    exact hfS s hsW
  obtain ⟨hsyl, -, -⟩ := hK4 ↥K hKt uK huKo V hmax
  have h1 : V.map K.subtype = l34Img x J S₂ := by
    rw [hV, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hStK]
  have h2 : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h3 := (isSylowOf_map_subtype_iff K).mpr hsyl
  rwa [h1, h2] at h3

theorem l34insp_inf_eq_bot (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    (hKM : l34Img x J M ⊓ l34Img x J J =
      normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
        Set (L34Quot x J)) ⊓ l34Img x J J)
    {u : G} (huP : u ∈ (P : Subgroup G)) (huJ : u ∈ J) (huM : u ∈ M) (hu1 : u ≠ 1)
    (hu3 : u ^ 3 = 1) {S₂ : Subgroup G} (hS₂J : S₂ ≤ J) (hS₂2 : IsPGroup 2 S₂)
    (huS : u ∈ normalizer (S₂ : Set G)) :
    l34Img x J S₂ ⊓ l34Img x J M = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  obtain ⟨-, -, hKt⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨-, hTc, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  set K : Subgroup (L34Quot x J) := l34Img x J J with hK
  set T : Subgroup (L34Quot x J) := l34Img x J ((P : Subgroup G) ⊓ J) with hT
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  have hQ9 : Nat.card (Q : Subgroup ↥K) = 3 ^ 2 := (hK2 ↥K hKt Q).1
  have hTsyl : IsSylowOf 3 T K :=
    isSylowOf_of_card hTK (hTc.trans (hQ9.symm.trans Q.card_eq_multiplicity))
  obtain ⟨T', hT'⟩ := hTsyl.exists_sylow_eq_subgroupOf
  obtain ⟨-, -, -, hfrob⟩ := hK2 ↥K hKt T'
  have hũK : l34Hom x J ⟨u, hJC huJ⟩ ∈ K := ⟨⟨u, hJC huJ⟩, Subgroup.mem_subgroupOf.mpr huJ, rfl⟩
  have hũT : l34Hom x J ⟨u, hJC huJ⟩ ∈ T :=
    ⟨⟨u, hJC huJ⟩, Subgroup.mem_subgroupOf.mpr ⟨huP, huJ⟩, rfl⟩
  have hũM : l34Hom x J ⟨u, hJC huJ⟩ ∈ l34Img x J M :=
    ⟨⟨u, hJC huJ⟩, Subgroup.mem_subgroupOf.mpr huM, rfl⟩
  have hũ1 : l34Hom x J ⟨u, hJC huJ⟩ ≠ 1 := fun h =>
    hu1 (l34insp_eq_one_of_three hK1 hK2 hJ huJ hu3 h)
  have hStK : l34Img x J S₂ ≤ K := Subgroup.map_mono fun c hc => hS₂J hc
  have hSt2 : IsPGroup 2 (l34Img x J S₂) :=
    (hS₂2.comap_subtype (K := centralizer ({x} : Set G))).map _
  have hũN : l34Hom x J ⟨u, hJC huJ⟩ ∈
      normalizer ((l34Img x J S₂ : Subgroup (L34Quot x J)) : Set (L34Quot x J)) :=
    l34insp_hom_mem_normalizer x J S₂ huS
  have hVK : l34Img x J S₂ ⊓ l34Img x J M ≤ K := inf_le_left.trans hStK
  set V : Subgroup ↥K := (l34Img x J S₂ ⊓ l34Img x J M).subgroupOf K with hV
  have hV2 : IsPGroup 2 V := (hSt2.to_le inf_le_left).comap_subtype
  have hVN : V ≤ normalizer ((T' : Subgroup ↥K) : Set ↥K) := by
    intro v hv
    rw [hT', ← Subgroup.subgroupOf_normalizer_eq hTK]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have h2 : (v : L34Quot x J) ∈ l34Img x J M ⊓ K := ⟨(Subgroup.mem_subgroupOf.mp hv).2, v.2⟩
    rw [hKM] at h2
    exact h2.1
  have huV : (⟨_, hũK⟩ : ↥K) ∈ normalizer (V : Set ↥K) := by
    rw [hV, ← Subgroup.subgroupOf_normalizer_eq hVK]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hũN, Subgroup.le_normalizer hũM⟩
  have huT' : (⟨_, hũK⟩ : ↥K) ∈ (T' : Subgroup ↥K) := by
    rw [hT']
    exact Subgroup.mem_subgroupOf.mpr hũT
  have hu1' : (⟨_, hũK⟩ : ↥K) ≠ 1 := fun h => hũ1 (congrArg Subtype.val h)
  have hVbot := hfrob _ huT' hu1' V hV2 hVN huV
  refine eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr ?_
  have hyV : (⟨y, hVK hy⟩ : ↥K) ∈ V := Subgroup.mem_subgroupOf.mpr hy
  rw [hVbot, Subgroup.mem_bot] at hyV
  exact congrArg Subtype.val hyV

end CFSG.LocalAnalysis.RankThreeTheoremC
