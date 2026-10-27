module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Count
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Local
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

namespace R12

theorem isComponent_image {D A : Subgroup G} (hA : IsTwoComponentIn A D) :
    IsComponent ((A.subgroupOf D).map (QuotientGroup.mk' (pPrimeCore 2 ↥D))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥D) 2).2.1 hA.2

theorem eq_of_image_eq {D A B : Subgroup G} (hA : IsTwoComponentIn A D)
    (hB : IsTwoComponentIn B D)
    (h : (A.subgroupOf D).map (QuotientGroup.mk' (pPrimeCore 2 ↥D)) =
      (B.subgroupOf D).map (QuotientGroup.mk' (pPrimeCore 2 ↥D))) : A = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥D) 2).2.2.1 hA.2 hB.2 h
  have h2 := subgroupOf_inj.mp h1
  rwa [inf_of_le_left hA.1, inf_of_le_left hB.1] at h2

theorem mem_centralizer_image_of_mem_coreActionKernel {D A : Subgroup G}
    (hA : IsTwoComponentIn A D) {x : ↥D} (hx : (x : G) ∈ coreActionKernel A) :
    QuotientGroup.mk' (pPrimeCore 2 ↥D) x ∈
      centralizer (((A.subgroupOf D).map (QuotientGroup.mk' (pPrimeCore 2 ↥D)) :
        Subgroup (↥D ⧸ pPrimeCore 2 ↥D)) : Set (↥D ⧸ pPrimeCore 2 ↥D)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have haA : (a : G) ∈ A := mem_subgroupOf.mp ha
  have h1 : (a : G)⁻¹ * (x : G)⁻¹ * a * x ∈ oddCoreIn A := (mem_coreActionKernel.mp hx).2 _ haA
  exact (mk_mul_comm_iff (N := D) a x).mpr (oddCoreIn_le_of_isTwoComponentIn hA h1)

theorem mem_coreActionKernel_of_mem_centralizer_image {D A : Subgroup G}
    (hA : IsTwoComponentIn A D) {x : ↥D}
    (hx : QuotientGroup.mk' (pPrimeCore 2 ↥D) x ∈
      centralizer (((A.subgroupOf D).map (QuotientGroup.mk' (pPrimeCore 2 ↥D)) :
        Subgroup (↥D ⧸ pPrimeCore 2 ↥D)) : Set (↥D ⧸ pPrimeCore 2 ↥D))) :
    (x : G) ∈ coreActionKernel A := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥D) with hπ
  have hxD : (x : G) ∈ normalizer (D : Set G) := le_normalizer x.2
  have hAx := isTwoComponentIn_map_conj hA hxD
  have himage : ((A.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf D).map π =
      (A.subgroupOf D).map π := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, haA, hay⟩ := mem_subgroupOf.mp hy
      have haD : a ∈ D := hA.1 haA
      have hya : y = x * ⟨a, haD⟩ * x⁻¹ := by
        apply Subtype.ext
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hay
        simp [← hay]
      refine ⟨⟨a, haD⟩, mem_subgroupOf.mpr haA, ?_⟩
      rw [hya, map_mul, map_mul, map_inv]
      have hc := (mem_centralizer_iff.mp hx) (π ⟨a, haD⟩) ⟨⟨a, haD⟩, mem_subgroupOf.mpr haA, rfl⟩
      rw [← hc]
      group
    · rintro ⟨a, ha, rfl⟩
      have haA : (a : G) ∈ A := mem_subgroupOf.mp ha
      refine ⟨x * a * x⁻¹, mem_subgroupOf.mpr ⟨a, haA, by simp⟩, ?_⟩
      rw [map_mul, map_mul, map_inv]
      have hc := (mem_centralizer_iff.mp hx) (π a) ⟨a, ha, rfl⟩
      rw [← hc]
      group
  have hAeq : A.map (MulAut.conj (x : G)).toMonoidHom = A := eq_of_image_eq hAx hA himage
  have hxN : (x : G) ∈ normalizer (A : Set G) := mem_normalizer_iff_map_conj_eq.mpr hAeq
  refine mem_coreActionKernel.mpr ⟨hxN, fun a haA => ?_⟩
  have haD : a ∈ D := hA.1 haA
  have hcomm := (mem_centralizer_iff.mp hx) (π ⟨a, haD⟩) ⟨⟨a, haD⟩, mem_subgroupOf.mpr haA, rfl⟩
  have hO : a⁻¹ * (x : G)⁻¹ * a * x ∈ oddCoreIn D :=
    (mk_mul_comm_iff (N := D) ⟨a, haD⟩ x).mp hcomm
  have hmemA : a⁻¹ * (x : G)⁻¹ * a * x ∈ A := by
    have h3 : (x : G)⁻¹ * a * (x : G)⁻¹⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (inv_mem hxN) a).mp haA
    rw [inv_inv] at h3
    rw [mul_assoc, mul_assoc]
    refine mul_mem (inv_mem haA) ?_
    simpa [mul_assoc] using h3
  exact oddCoreIn_inf_le hA.1 (mem_inf.mpr ⟨hO, hmemA⟩)

theorem map_oddTwoCoreIn_sup_twoLayerIn (D : Subgroup G) :
    ((oddTwoCoreIn D ⊔ twoLayerIn D).subgroupOf D).map (QuotientGroup.mk' (pPrimeCore 2 ↥D)) =
      pCore 2 (↥D ⧸ pPrimeCore 2 ↥D) ⊔ layer (↥D ⧸ pPrimeCore 2 ↥D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥D) with hπ
  have hsub : (oddTwoCoreIn D ⊔ twoLayerIn D).subgroupOf D =
      (pCore 2 (↥D ⧸ pPrimeCore 2 ↥D)).comap π ⊔ pLayer ↥D 2 := by
    rw [oddTwoCoreIn, twoLayerIn, ← Subgroup.map_sup, ← comap_subtype,
      comap_map_eq_self_of_injective D.subtype_injective]
  rw [hsub, Subgroup.map_sup, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    LBalance.Quot.map_pLayer_eq_layer_quotient]

end R12

theorem lemma32RankTwoKernelInput_of_central (hP : R12.QuasisimpleRankTwoCentralInput) :
    Lemma32RankTwoKernelInput := by
  classical
  intro G _ _ b A₁ A₂ hb2 hA₁ hA₂ hne hbA₂ hr2 hcat hY T hT2 hTC hT1 hT2'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({b} : Set G) with hHdef
  set O := pPrimeCore 2 ↥H with hOdef
  set π := QuotientGroup.mk' O with hπ
  set K₁ := (A₁.subgroupOf H).map π with hK₁def
  set K₂ := (A₂.subgroupOf H).map π with hK₂def
  have hK₁ : IsComponent K₁ := R12.isComponent_image hA₁
  have hK₂ : IsComponent K₂ := R12.isComponent_image hA₂
  have hK12 : K₁ ≠ K₂ := fun h => hne (R12.eq_of_image_eq hA₁ hA₂ h)
  have hOcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
  have hbH : b ∈ H := mem_centralizer_singleton_iff.mpr rfl
  set b' : ↥H := ⟨b, hbH⟩ with hb'
  set z := π b' with hzdef
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hzZ : z ∈ center (↥H ⧸ O) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O q
    rw [hzdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
  have hzK : z ∈ K₂ := ⟨b', mem_subgroupOf.mpr hbA₂, rfl⟩
  have hz2 : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, hzdef, ← map_mul]
      have : b' * b' = 1 := Subtype.ext hbb
      rw [this, map_one]
    · intro h
      have hbO : b' ∈ O := (QuotientGroup.eq_one_iff _).mp h
      have h1 := orderOf_dvd_natCard (⟨b', hbO⟩ : O)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hb2] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd hOcop h1) (by norm_num)
  set φ : ↥A₂ →* ↥H ⧸ O := π.comp (inclusion hA₂.1) with hφ
  have hrange : φ.range = K₂ := by
    rw [hφ, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ.ker = pPrimeCore 2 ↥A₂ := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hOdef]
    have h1 := inf_oddCoreIn_eq hA₂
    constructor
    · intro hx
      have hxO : (x : G) ∈ A₂ ⊓ oddCoreIn H := ⟨x.2, ⟨inclusion hA₂.1 x, hx, rfl⟩⟩
      rw [h1] at hxO
      obtain ⟨y, hy, hyx⟩ := hxO
      rwa [Subtype.ext hyx] at hy
    · intro hx
      have hxO : (x : G) ∈ oddCoreIn A₂ := ⟨x, hx, rfl⟩
      rw [← h1] at hxO
      obtain ⟨y, hy, hyx⟩ := hxO.2
      have : y = inclusion hA₂.1 x := Subtype.ext hyx
      rwa [this] at hy
  set e : ↥A₂ ⧸ pPrimeCore 2 ↥A₂ ≃* ↥K₂ :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange) with hedef
  have he : ∀ a : ↥A₂, ((e (a : ↥A₂ ⧸ pPrimeCore 2 ↥A₂) : ↥K₂) : ↥H ⧸ O) = φ a := fun a => rfl
  set zQ : ↥A₂ ⧸ pPrimeCore 2 ↥A₂ := ((⟨b, hbA₂⟩ : ↥A₂) : ↥A₂ ⧸ pPrimeCore 2 ↥A₂) with hzQ
  have hezQ : ((e zQ : ↥K₂) : ↥H ⧸ O) = z := he _
  have hzQZ : zQ ∈ center (↥A₂ ⧸ pPrimeCore 2 ↥A₂) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥A₂) q
    rw [hzQ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hA₂.1 a.2))
  have hzQ2 : orderOf zQ = 2 := by
    have h := MulEquiv.orderOf_eq e zQ
    rw [← h, ← Subgroup.orderOf_coe, hezQ, hz2]
  have hqQ : IsQuasisimple (↥A₂ ⧸ pPrimeCore 2 ↥A₂) :=
    isQuasisimple_quotient_of_isPComponent hA₂.1 hA₂.2
  have hrQ : CFSG.pRank 2 (↥A₂ ⧸ pPrimeCore 2 ↥A₂) = 2 := by
    rw [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card), hr2]
  obtain ⟨hP1Q, sQ, tQ, htQ2, htQZ, hsQ2, hstQ⟩ :=
    hP _ hqQ (pPrimeCore_quotient_eq_bot Nat.prime_two) hcat hrQ zQ hzQZ hzQ2
  set s : ↥H ⧸ O := ((e sQ : ↥K₂) : ↥H ⧸ O) with hsdef
  set t : ↥H ⧸ O := ((e tQ : ↥K₂) : ↥H ⧸ O) with htdef
  have hsK : s ∈ K₂ := (e sQ).2
  have htK : t ∈ K₂ := (e tQ).2
  have ht2 : t * t = 1 := by
    rw [htdef, ← Subgroup.coe_mul, ← map_mul, htQ2, map_one, Subgroup.coe_one]
  have hs2 : s * s = z := by
    rw [hsdef, ← Subgroup.coe_mul, ← map_mul, hsQ2, hezQ]
  have hst : s * t = t * s := by
    rw [hsdef, htdef, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hstQ]
  have htn : ∃ k ∈ K₂, t * k ≠ k * t := by
    rw [mem_center_iff] at htQZ
    push Not at htQZ
    obtain ⟨q, hq⟩ := htQZ
    refine ⟨((e q : ↥K₂) : ↥H ⧸ O), (e q).2, fun h => hq ?_⟩
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact h.symm
  have hP1 : ∀ w ∈ K₂, (∀ k ∈ K₂, w * k = k * w) → w ^ 4 = 1 → w = 1 ∨ w = z := by
    intro w hw hwc hw4
    set wQ := e.symm ⟨w, hw⟩ with hwQ
    have hewQ : ((e wQ : ↥K₂) : ↥H ⧸ O) = w := by rw [hwQ, MulEquiv.apply_symm_apply]
    have hwQZ : wQ ∈ center (↥A₂ ⧸ pPrimeCore 2 ↥A₂) := by
      rw [mem_center_iff]
      intro q
      apply e.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hewQ]
      exact (hwc _ (e q).2).symm
    have hwQ4 : wQ ^ 4 = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, hewQ, hw4, Subgroup.coe_one]
    rcases hP1Q wQ hwQZ hwQ4 with h | h
    · left
      rw [← hewQ, h, map_one, Subgroup.coe_one]
    · right
      rw [← hewQ, h, hezQ]
  have hYW : CFSG.Open.pRank 2 ((pCore 2 (↥H ⧸ O) ⊔ layer (↥H ⧸ O)) ⊓
      centralizer (K₁ : Set (↥H ⧸ O))) ≤ 2 := by
    set Y₁ := (oddTwoCoreIn H ⊔ twoLayerIn H) ⊓ coreActionKernel A₁ with hY₁
    have hY₁H : Y₁ ≤ H := inf_le_left.trans (sup_le (map_subtype_le _) (map_subtype_le _))
    have hle : (pCore 2 (↥H ⧸ O) ⊔ layer (↥H ⧸ O)) ⊓ centralizer (K₁ : Set (↥H ⧸ O)) ≤
        (Y₁.subgroupOf H).map π := by
      rintro q ⟨hqM, hqC⟩
      rw [← R12.map_oddTwoCoreIn_sup_twoLayerIn H] at hqM
      obtain ⟨x, hx, rfl⟩ := hqM
      exact ⟨x, mem_subgroupOf.mpr (mem_inf.mpr ⟨mem_subgroupOf.mp hx,
        R12.mem_coreActionKernel_of_mem_centralizer_image hA₁ hqC⟩), rfl⟩
    have hodd : ¬ 2 ∣ Nat.card (π.ker.subgroupOf (Y₁.subgroupOf H)) := by
      intro h
      have h1 : Nat.card (π.ker.subgroupOf (Y₁.subgroupOf H)) ∣ Nat.card O := by
        rw [QuotientGroup.ker_mk']
        rw [← card_map_of_injective (Y₁.subgroupOf H).subtype_injective,
          subgroupOf_map_subtype]
        exact card_dvd_of_le inf_le_left
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hOcop (h.trans h1)
    have h1 := SectionRank.pRank_mono (p := 2) (by norm_num) hle
    have h2 := pRank_map_le_of_odd π (Y₁.subgroupOf H) hodd
    have h3 := SectionRank.pRank_le_map (p := 2) (by norm_num) H.subtype H.subtype_injective
      (Y₁.subgroupOf H)
    rw [subgroupOf_map_subtype, inf_of_le_left hY₁H] at h3
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at hY
    omega
  set T' := T.subgroupOf H with hT'
  have hT'1 : T'.map π ≤ centralizer (K₁ : Set (↥H ⧸ O)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact R12.mem_centralizer_image_of_mem_coreActionKernel hA₁ (hT1 (mem_subgroupOf.mp hx))
  have hT'2 : T'.map π ≤ centralizer (K₂ : Set (↥H ⧸ O)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact R12.mem_centralizer_image_of_mem_coreActionKernel hA₂ (hT2' (mem_subgroupOf.mp hx))
  have hbound := R12.card_le_two_of_centralizer (pPrimeCore_quotient_eq_bot Nat.prime_two) hK₁ hK₂
    hK12 hzZ hzK hz2 hsK htK ht2 htn hs2 hst hP1 hYW hT'1 hT'2
  have hT'p : IsPGroup 2 T' := hT2.comap_subtype (K := H)
  have hker1 : Nat.card ↥(π.ker ⊓ T') = 1 := by
    rw [QuotientGroup.ker_mk', ← eq_bot_iff_card, eq_bot_iff]
    rintro y ⟨hyO, hyT⟩
    exact mem_bot.mpr (eq_one_of_mem_of_isPGroup hT'p hOcop hyT hyO)
  have hmapcard : Nat.card ↥(T'.map π) = Nat.card T' := by
    have h := relIndex_mul_card π.ker T'
    rw [hker1, mul_one, relIndex_ker] at h
    exact h
  have hTT' : Nat.card T' = Nat.card T := by
    rw [hT']
    exact Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv
  rw [hmapcard, hTT'] at hbound
  exact hbound

end CFSG.ComponentClassification.Sol76T13

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem map_subgroupOf_le_centralizer_image {C J E : Subgroup G}
    (hJC : J ≤ C) (hEC : E ≤ C) (hJE : ⁅J, E⁆ ≤ oddCoreIn C) :
    (E.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) ≤
      centralizer (((J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))) :
        Set (↥C ⧸ pPrimeCore 2 ↥C)) := by
  have hJmap : (J.subgroupOf C).map C.subtype = J := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJC]
  have hEmap : (E.subgroupOf C).map C.subtype = E := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hEC]
  have hcomm : ⁅J.subgroupOf C, E.subgroupOf C⁆ ≤ pPrimeCore 2 ↥C := by
    refine (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp ?_
    rw [Subgroup.map_commutator, hJmap, hEmap]
    simpa only [oddCoreIn] using hJE
  have hbot : ⁅(J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)),
      (E.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcomm
  rw [Subgroup.commutator_comm] at hbot
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot

theorem exists_image_component_simple_of_commutator_le_oddCoreIn
    [Finite G] {C J E F : Subgroup G}
    (hJ : IsTwoComponentIn J C)
    (hJsimple : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J))
    (hEC : E ≤ C) (hFJ : F ≤ J)
    (hJE : ⁅J, E⁆ ≤ oddCoreIn C) :
    let π := QuotientGroup.mk' (pPrimeCore 2 ↥C)
    ∃ S : Subgroup (↥C ⧸ pPrimeCore 2 ↥C),
      CFSG.IsComponent S ∧ IsSimpleGroup S ∧
      (F.subgroupOf C).map π ≤ S ∧
      (E.subgroupOf C).map π ≤ centralizer (S : Set _) := by
  classical
  dsimp only
  have hN : (CFSG.Open.lBalancePrimeCore 2 C).subgroupOf J = pPrimeCore 2 ↥J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, LBalance.primeCore_eq_map, inf_comm]
    simpa only [oddCoreIn] using Sol76.inf_oddCoreIn_eq hJ
  have hNnormal : ((CFSG.Open.lBalancePrimeCore 2 C).subgroupOf J).Normal := by
    rw [hN]
    infer_instance
  let S : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) :=
    (J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))
  have hS : IsSimpleGroup S := by
    let e : (↥J ⧸ pPrimeCore 2 ↥J) ≃* S :=
      (QuotientGroup.quotientMulEquivOfEq hN.symm).trans
        (LBalance.coreQuotientEquivImage 2 C J hJ.1)
    exact e.isSimpleGroup_congr.mp hJsimple
  refine ⟨S, R12.isComponent_image hJ, hS, ?_, ?_⟩
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono C hFJ)
  · exact map_subgroupOf_le_centralizer_image hJ.1 hEC hJE

end CFSG.ComponentClassification.Sol76.Sig

namespace CFSG.ComponentClassification.Sol76T13.R12

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem le_coreActionKernel_of_commutator_le_oddCoreIn [Finite G] {C J E : Subgroup G}
    (hJ : IsTwoComponentIn J C) (hEC : E ≤ C) (hJE : ⁅J, E⁆ ≤ oddCoreIn C) :
    E ≤ coreActionKernel J := by
  intro e he
  let x : ↥C := ⟨e, hEC he⟩
  have hx : QuotientGroup.mk' (pPrimeCore 2 ↥C) x ∈
      centralizer (((J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))) :
        Set (↥C ⧸ pPrimeCore 2 ↥C)) :=
    CFSG.ComponentClassification.Sol76.Sig.map_subgroupOf_le_centralizer_image hJ.1 hEC hJE
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr he))
  exact mem_coreActionKernel_of_mem_centralizer_image hJ hx

end CFSG.ComponentClassification.Sol76T13.R12
