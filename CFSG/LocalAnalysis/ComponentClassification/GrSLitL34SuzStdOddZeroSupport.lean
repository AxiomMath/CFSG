module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCyclic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdQuot
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem isComponent_map_centralizer_quotient_of_isComponent {X : Type} [Group X]
    [Finite X] {U : Subgroup X} [U.Normal] (hU : Odd (Nat.card U)) {t : X} (ht : t ^ 2 = 1)
    {K : Subgroup X} (hKt : K ≤ centralizer ({t} : Set X))
    (hKcomp : IsComponent (K.subgroupOf (centralizer ({t} : Set X))))
    (hK2 : ∃ k ∈ K, orderOf k = 2) :
    K.map (QuotientGroup.mk' U) ≤ centralizer ({QuotientGroup.mk' U t} : Set (X ⧸ U)) ∧
      IsComponent ((K.map (QuotientGroup.mk' U)).subgroupOf
        (centralizer ({QuotientGroup.mk' U t} : Set (X ⧸ U)))) := by
  classical
  let C : Subgroup X := centralizer ({t} : Set X)
  let π : X →* X ⧸ U := QuotientGroup.mk' U
  let Cq : Subgroup (X ⧸ U) := centralizer ({π t} : Set (X ⧸ U))
  have hCmap : C.map π = Cq := by
    have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq
      (H := X) (p := 2) Nat.prime_two (W := ⊤) (N := U) le_top
      (Nat.coprime_two_left.mpr hU) ht
    rw [top_inf_eq, Subgroup.map_top_of_surjective (QuotientGroup.mk' U)
      (QuotientGroup.mk'_surjective U), top_inf_eq] at h
    simpa [C, Cq, π] using h
  have hKC : K.map π ≤ Cq := by
    rintro _ ⟨k, hkK, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hkt : t * k = k * t := Subgroup.mem_centralizer_iff.mp (hKt hkK) t rfl
    rw [← map_mul, ← map_mul, hkt]
  have hnotU : ¬ K ≤ U := by
    rintro hKU
    obtain ⟨k, hkK, hk2⟩ := hK2
    have hdvd : orderOf k ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U (hKU hkK)
    rw [hk2] at hdvd
    exact hU.not_two_dvd_nat hdvd
  have hKq : IsQuasisimple ↥K :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKt)).mp hKcomp.1
  have hKmap : IsQuasisimple ↥(K.map π) :=
    CFSG.LocalCores.isQuasisimple_map hKq π (by simpa [π, QuotientGroup.ker_mk'] using hnotU)
  have hKq' : IsQuasisimple ↥((K.map π).subgroupOf Cq) :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKC)).mpr hKmap
  have hKsub : ((K.map π).subgroupOf Cq).IsSubnormal := by
    have hmap : CFSG.Open.IsSubnormal ((K.subgroupOf C).map (π.comp C.subtype)) Cq := by
      have h := (CFSG.Open.IsSubnormal.of_mathlib hKcomp.2).map (π.comp C.subtype)
      rwa [show (⊤ : Subgroup ↥C).map (π.comp C.subtype) = Cq from by
        rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype, hCmap]] at h
    have hlower : (K.subgroupOf C).map (π.comp C.subtype) = K.map π := by
      rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKt]
    have hmap' : CFSG.Open.IsSubnormal (K.map π) Cq := hlower ▸ hmap
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf hKC).mp hmap'
  exact ⟨hKC, hKq', hKsub⟩

private theorem l34Zero_involution_and_card {H : Type} [Group H] [Finite H] {Λ : Subgroup H}
    (hΛL : IsL34Type (↥Λ ⧸ center ↥Λ)) :
    (∃ k ∈ Λ, orderOf k = 2) ∧ 2 ∣ Nat.card ↥Λ := by
  have hcardQ : Nat.card (↥Λ ⧸ center ↥Λ) = 20160 := by
    have h := CFSG.GH74.card_of_lieModel_PSL (G := ↥Λ ⧸ center ↥Λ) (n := 3) (p := 2)
      (f := 2) (by norm_num) hΛL
    rwa [show CFSG.Open.ordA 2 (2 ^ 2) = 20160 by decide] at h
  have h2Q : 2 ∣ Nat.card (↥Λ ⧸ center ↥Λ) := by rw [hcardQ]; norm_num
  have hcardΛ : Nat.card ↥Λ =
      Nat.card (↥Λ ⧸ center ↥Λ) * Nat.card ↥(center ↥Λ) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥Λ)
  have h2Λ : 2 ∣ Nat.card ↥Λ := by
    rw [hcardΛ]
    exact dvd_mul_of_dvd_left h2Q _
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥Λ) 2 h2Λ
  exact ⟨⟨k, k.2, by simpa only [Subgroup.orderOf_coe] using hk⟩, h2Λ⟩

private theorem l34Zero_center_image {H : Type} [Group H] [Finite H]
    {U : Subgroup H} [U.Normal] (hUodd : Odd (Nat.card U))
    {Λ : Subgroup H} (hΛq : IsQuasisimple ↥Λ) (hΛ2 : ∃ k ∈ Λ, orderOf k = 2) :
    (MonoidHom.subgroupMap (QuotientGroup.mk' U) Λ).ker ≤ center ↥Λ ∧
      center ↥(Λ.map (QuotientGroup.mk' U)) =
        (center ↥Λ).map (MonoidHom.subgroupMap (QuotientGroup.mk' U) Λ) := by
  classical
  let f : ↥Λ →* ↥(Λ.map (QuotientGroup.mk' U)) :=
    MonoidHom.subgroupMap (QuotientGroup.mk' U) Λ
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  have hf_apply : ∀ x : ↥Λ, (f x : H ⧸ U) = QuotientGroup.mk' U (x : H) := fun _ => rfl
  have hΛO : Λ ⊓ U ≤ (center ↥Λ).map Λ.subtype :=
    inf_le_center_of_isQuasisimple_of_odd hUodd hΛq hΛ2
  have hker_le : f.ker ≤ center ↥Λ := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    intro x hx
    have hmem : (x : H) ∈ Λ ⊓ U :=
      Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp (hΛO hmem)
    rwa [show x = z from Subtype.ext hzval.symm]
  refine ⟨hker_le, ?_⟩
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := hf z
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    have hcomm : ∀ k ∈ Λ, (x : H) * k * (x : H)⁻¹ * k⁻¹ ∈ U := by
      intro k hk
      have h1 : f (x * ⟨k, hk⟩ * x⁻¹ * ⟨k, hk⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have hc := Subgroup.mem_center_iff.mp hz (f ⟨k, hk⟩)
        rw [← hc]
        group
      have h1' : QuotientGroup.mk' U ((x : H) * k * (x : H)⁻¹ * k⁻¹) = 1 := by
        have hval := congrArg (fun y : ↥(Λ.map (QuotientGroup.mk' U)) => (y : H ⧸ U)) h1
        simpa [hf_apply] using hval
      exact (QuotientGroup.eq_one_iff ((x : H) * k * (x : H)⁻¹ * k⁻¹)).mp h1'
    have hcent := commute_of_commutator_mem_of_odd hUodd hΛq hΛ2 x.2 hcomm k k.2
    exact (Subtype.ext hcent).symm
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := hf q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw k]

private theorem l34Zero_type_transfer {H : Type} [Group H] [Finite H]
    {U : Subgroup H} [U.Normal] (hUodd : Odd (Nat.card U))
    {Λ : Subgroup H} (hΛq : IsQuasisimple ↥Λ) (hΛ2 : ∃ k ∈ Λ, orderOf k = 2)
    (hΛodd : Odd (Nat.card (center ↥Λ))) (hΛL : IsL34Type (↥Λ ⧸ center ↥Λ))
    (hDq : IsQuasisimple ↥(Λ.map (QuotientGroup.mk' U))) :
    Odd (Nat.card (center ↥(Λ.map (QuotientGroup.mk' U)))) ∧
      Open.fusionZStar ↥(Λ.map (QuotientGroup.mk' U)) =
        center ↥(Λ.map (QuotientGroup.mk' U)) ∧
      IsL34Type (↥(Λ.map (QuotientGroup.mk' U)) ⧸
        center ↥(Λ.map (QuotientGroup.mk' U))) := by
  classical
  obtain ⟨-, h2Λ⟩ := l34Zero_involution_and_card hΛL
  let f : ↥Λ →* ↥(Λ.map (QuotientGroup.mk' U)) :=
    MonoidHom.subgroupMap (QuotientGroup.mk' U) Λ
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  obtain ⟨hker_le, hZ⟩ := l34Zero_center_image hUodd hΛq hΛ2
  have hZodd : Odd (Nat.card (center ↥(Λ.map (QuotientGroup.mk' U)))) := by
    rw [hZ]
    exact hΛodd.of_dvd_nat (Subgroup.card_map_dvd (center ↥Λ) f)
  have hker_odd : Odd (Nat.card f.ker) := hΛodd.of_dvd_nat (Subgroup.card_dvd_of_le hker_le)
  have hcardD : Nat.card ↥Λ =
      Nat.card f.ker * Nat.card ↥(Λ.map (QuotientGroup.mk' U)) := by
    have h := (Subgroup.card_ker_mul_card_range f).symm
    rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h
    exact h
  have h2D : 2 ∣ Nat.card ↥(Λ.map (QuotientGroup.mk' U)) := by
    have h2prod : 2 ∣ Nat.card ↥(Λ.map (QuotientGroup.mk' U)) * Nat.card f.ker := by
      rw [mul_comm, ← hcardD]
      exact h2Λ
    exact (Nat.prime_two.dvd_mul.mp h2prod).resolve_right hker_odd.not_two_dvd_nat
  have hOD : pPrimeCore 2 ↥(Λ.map (QuotientGroup.mk' U)) ≠ ⊤ := by
    intro htop
    have hc := pPrimeCore_coprime_card (p := 2) (G := ↥(Λ.map (QuotientGroup.mk' U)))
    rw [htop, Subgroup.card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2D hc
  have hZD : Open.fusionZStar ↥(Λ.map (QuotientGroup.mk' U)) =
      center ↥(Λ.map (QuotientGroup.mk' U)) :=
    CatLeaf.fusionZStar_eq_center_of_quasisimple hDq hOD
  have eZ : (↥Λ ⧸ center ↥Λ) ≃*
      (↥(Λ.map (QuotientGroup.mk' U)) ⧸ center ↥(Λ.map (QuotientGroup.mk' U))) :=
    LieType.CurtisTits.centerQuotientEquivOfSurjective f hf hker_le hZ
  exact ⟨hZodd, hZD, LieType.CurtisTits.lieModel_of_mulEquiv eZ hΛL⟩

private theorem l34Zero_fixed_aut {Q : Type} [Group Q] {s : Q} (hs : s ^ 2 = 1)
    {K : Subgroup Q} (hfix : K.map (MulAut.conj s).toMonoidHom = K) :
    ∃ c : MulAut ↥K, (∀ x, c (c x) = x) ∧
      fixedSubgroup c = (K ⊓ centralizer ({s} : Set Q)).subgroupOf K := by
  classical
  have hss : s * s = 1 := by rw [← pow_two, hs]
  have hmem : s ∈ normalizer (K : Set Q) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix
  let c : MulAut ↥K := K.normalizerMonoidHom ⟨s, hmem⟩
  have hcapp : ∀ x : ↥K, ((c x : ↥K) : Q) = s * (x : Q) * s⁻¹ := fun _ => rfl
  have hc : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc s * (s * (x : Q) * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
      _ = x := by rw [hss]; group
  have hfixC : fixedSubgroup c = (K ⊓ centralizer ({s} : Set Q)).subgroupOf K := by
    ext x
    rw [CFSG.LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : Q) * s = s * (x : Q) * s⁻¹ * s := by rw [h1]
        _ = s * (x : Q) := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc s * (x : Q) * s⁻¹ = (x : Q) * s * s⁻¹ := by rw [hx]
        _ = x := by group
  exact ⟨c, hc, hfixC⟩

private theorem l34Zero_fixed_pcomponent {Q : Type} [Group Q] [Finite Q] {s : Q}
    {D K : Subgroup Q} {c : MulAut ↥K}
    (hDmem : D ≤ centralizer ({s} : Set Q))
    (hfixC : fixedSubgroup c = (K ⊓ centralizer ({s} : Set Q)).subgroupOf K)
    (hDcompKC : IsComponent (D.subgroupOf (K ⊓ centralizer ({s} : Set Q))))
    (hDKle : D ≤ K) (hDeq : D ≠ K) :
    D.subgroupOf K ≤ fixedSubgroup c ∧
      IsPComponent 2 ((D.subgroupOf K).subgroupOf (fixedSubgroup c)) ∧
      D.subgroupOf K ≠ ⊤ := by
  classical
  have hPle : D.subgroupOf K ≤ fixedSubgroup c := by
    rw [hfixC]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hDKle hx, hDmem hx⟩
  have hPcomp : IsPComponent 2
      (D.subgroupOf (K ⊓ centralizer ({s} : Set Q))) :=
    CFSG.ComponentClassification.CatLeafProof.isPComponent_two_of_isComponent hDcompKC
  have hPp : IsPComponent 2 ((D.subgroupOf K).subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (X := K) (Y := K ⊓ centralizer ({s} : Set Q)) (L := D)
      inf_le_left 2 Nat.prime_two).mpr hPcomp
  have hPne : D.subgroupOf K ≠ ⊤ := by
    intro htop
    apply hDeq
    apply le_antisymm hDKle
    intro x hx
    have hxK : (⟨x, hx⟩ : ↥K) ∈ D.subgroupOf K := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hxK
  exact ⟨hPle, hPp, hPne⟩

private theorem l34Zero_fixed_type_rank {Q : Type} [Group Q] [Finite Q]
    {D K : Subgroup Q} (hDKle : D ≤ K)
    (hZD : Open.fusionZStar ↥D = center ↥D)
    (hZodd : Odd (Nat.card (center ↥D)))
    (htypeD : IsL34Type (↥D ⧸ center ↥D)) :
    IsL34Type (↥(D.subgroupOf K) ⧸ Open.fusionZStar ↥(D.subgroupOf K)) ∧
      pRank 2 ↥(Open.fusionZStar ↥(D.subgroupOf K)) ≤ 1 := by
  have htypeD' : IsL34Type (↥D ⧸ Open.fusionZStar ↥D) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hZD).symm htypeD
  have htypeP : IsL34Type
      (↥(D.subgroupOf K) ⧸ Open.fusionZStar ↥(D.subgroupOf K)) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (Sol78.fusionZStarQuotCongr (Subgroup.subgroupOfEquivOfLe hDKle)).symm htypeD'
  have hPrankEq : pRank 2 ↥(Open.fusionZStar ↥(D.subgroupOf K)) =
      pRank 2 ↥(Open.fusionZStar ↥D) :=
    pRank_fusionZStar_congr (Sol78.coreQuotCongr (Subgroup.subgroupOfEquivOfLe hDKle))
  have hrankP : pRank 2 ↥(Open.fusionZStar ↥(D.subgroupOf K)) ≤ 1 := by
    rw [hPrankEq, CFSG.pRank_congr_of_mulEquiv (MulEquiv.subgroupCongr hZD) 2]
    have h0 : pRank 2 ↥(center ↥D) = 0 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.pRank_eq_zero_of_not_dvd_card Nat.prime_two hZodd.not_two_dvd_nat
    rw [h0]
    norm_num
  exact ⟨htypeP, hrankP⟩

private theorem l34Zero_catalog {K : Type} [Group K] [Finite K]
    (hcat : L34CyclicProperFixedCatalog) (hKq : IsQuasisimple K)
    (hOK : pPrimeCore 2 K = ⊥) (hKL : SectionRank.IsKGroupCat K)
    {c : MulAut K} (hc : ∀ x, c (c x) = x)
    {P : Subgroup K} (hPle : P ≤ fixedSubgroup c)
    (hPp : IsPComponent 2 (P.subgroupOf (fixedSubgroup c)))
    (hPne : P ≠ ⊤)
    (htypeP : IsL34Type (↥P ⧸ Open.fusionZStar ↥P))
    (hrankP : pRank 2 ↥(Open.fusionZStar ↥P) ≤ 1) :
    Blueprint.NativeSporadic.IsSporadic (K ⧸ center K) .Suz ∨
      Blueprint.NativeSporadic.IsSporadic (K ⧸ center K) .ONan ∨
      Blueprint.LieModel (K ⧸ center K) .PSL 3 2 4 := by
  classical
  have : IsSimpleGroup (K ⧸ center K) := hKq.2.1
  have hZK2 : IsPGroup 2 ↥(center K) := Sol78.center_isPGroup_two hOK
  have hcatK : Blueprint.Catalog (K ⧸ center K) := by
    refine SectionRank.catalog_of_isKGroupCat_of_surjective hKL ⊤
      ((QuotientGroup.mk' (center K)).comp (⊤ : Subgroup K).subtype) ?_
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) y
    exact ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩
  exact hcat K hKq hZK2 hcatK c hc P hPle hPp hPne htypeP hrankP

private theorem l34Zero_fixed_proper {Q : Type} [Group Q] [Finite Q]
    (hcat : L34CyclicProperFixedCatalog) {s : Q} (hs : s ^ 2 = 1) {D K : Subgroup Q}
    (hDmem : D ≤ centralizer ({s} : Set Q))
    (hDcompKC : IsComponent (D.subgroupOf (K ⊓ centralizer ({s} : Set Q))))
    (hZD : Open.fusionZStar ↥D = center ↥D)
    (hZodd : Odd (Nat.card (center ↥D)))
    (htypeD : IsL34Type (↥D ⧸ center ↥D))
    (hKcomp : IsComponent K) (hDKle : D ≤ K)
    (hfix : K.map (MulAut.conj s).toMonoidHom = K) (hDeq : D ≠ K)
    (hOK : pPrimeCore 2 ↥K = ⊥) (hKL : SectionRank.IsKGroupCat ↥K) :
    ∃ L : Subgroup Q, IsComponent L ∧ D ≤ L ∧
      L.map (MulAut.conj s).toMonoidHom = L ∧
      (Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Suz ∨
        Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan ∨
        Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 4) := by
  classical
  obtain ⟨c, hc, hfixC⟩ := l34Zero_fixed_aut hs hfix
  obtain ⟨hPle, hPp, hPne⟩ :=
    l34Zero_fixed_pcomponent hDmem hfixC hDcompKC hDKle hDeq
  obtain ⟨htypeP, hrankP⟩ := l34Zero_fixed_type_rank hDKle hZD hZodd htypeD
  exact ⟨K, hKcomp, hDKle, hfix,
    l34Zero_catalog hcat hKcomp.1 hOK hKL hc hPle hPp hPne htypeP hrankP⟩

private theorem l34Zero_support_cases {Q : Type} [Group Q] [Finite Q]
    (hcat : L34CyclicProperFixedCatalog) (hKQ : SectionRank.IsKGroupCat Q)
    (hO : pPrimeCore 2 Q = ⊥) {s : Q} (hs : s ^ 2 = 1) {D : Subgroup Q}
    (hDmem : D ≤ centralizer ({s} : Set Q))
    (hDcomp : IsComponent (D.subgroupOf (centralizer ({s} : Set Q))))
    (hZD : Open.fusionZStar ↥D = center ↥D)
    (hZodd : Odd (Nat.card (center ↥D)))
    (htypeD : IsL34Type (↥D ⧸ center ↥D)) :
    IsComponent D ∨
      (∃ L : Subgroup Q, IsComponent L ∧ D ≤ L ∧
        L.map (MulAut.conj s).toMonoidHom = L ∧
        (Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Suz ∨
          Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan ∨
          Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 4)) ∨
      (∃ L : Subgroup Q, IsComponent L ∧
        L.map (MulAut.conj s).toMonoidHom ≠ L ∧
        IsL34Type (↥L ⧸ center ↥L) ∧
        (D : Set Q) = {g | ∃ k ∈ L, k * (s * k * s⁻¹) = g} ∧
        ∀ L' : Subgroup Q, IsComponent L' →
          (⁅D, L'⁆ ≠ ⊥ ↔
            L' = L ∨ L' = L.map (MulAut.conj s).toMonoidHom)) := by
  obtain ⟨-, K, hKcomp, -, -, -, hsupport, hfixed, hswap⟩ :=
    CFSG.SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer
      hO hs hDmem hDcomp
  by_cases hfix : K.map (MulAut.conj s).toMonoidHom = K
  · obtain ⟨hDKle, hDcompKC⟩ := hfixed hfix
    by_cases hDeq : D = K
    · exact Or.inl (hDeq ▸ hKcomp)
    · refine Or.inr (Or.inl ?_)
      have hOK : pPrimeCore 2 ↥K = ⊥ :=
        CFSG.ComponentClassification.HarrisLit.pPrimeCore_eq_bot_of_isSubnormal hO hKcomp.2
      have hKL : SectionRank.IsKGroupCat ↥K := (hKQ).subgroup K
      exact l34Zero_fixed_proper hcat hs hDmem hDcompKC hZD hZodd htypeD hKcomp
        hDKle hfix hDeq hOK hKL
  · obtain ⟨-, -, hdiag, hequiv⟩ := hswap hfix
    obtain ⟨eK⟩ := hequiv
    exact Or.inr (Or.inr ⟨K, hKcomp, hfix,
      LieType.CurtisTits.lieModel_of_mulEquiv eK htypeD, hdiag, hsupport⟩)

theorem l34Zero_support (hcat : L34CyclicProperFixedCatalog) {H : Type} [Group H] [Finite H]
    (hK : SectionRank.IsKGroupCat H) {s : H} (hs : orderOf s = 2) {Λ : Subgroup H}
    (hΛs : Λ ≤ centralizer ({s} : Set H))
    (hΛ : IsComponent (Λ.subgroupOf (centralizer ({s} : Set H))))
    (hΛodd : Odd (Nat.card (center ↥Λ))) (hΛL : IsL34Type (↥Λ ⧸ center ↥Λ)) :
    IsComponent (Λ.map (QuotientGroup.mk' (pPrimeCore 2 H))) ∨
      (∃ L : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent L ∧
        Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ L ∧
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom = L ∧
        (Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Suz ∨
          Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan ∨
          Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 4)) ∨
      (∃ L : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent L ∧
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom ≠ L ∧
        IsL34Type (↥L ⧸ center ↥L) ∧
        ((Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) : Subgroup (H ⧸ pPrimeCore 2 H)) :
            Set (H ⧸ pPrimeCore 2 H)) =
          {g | ∃ k ∈ L, k * (QuotientGroup.mk' (pPrimeCore 2 H) s * k *
            (QuotientGroup.mk' (pPrimeCore 2 H) s)⁻¹) = g} ∧
        ∀ L' : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent L' →
          (⁅Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)), L'⁆ ≠ ⊥ ↔
            L' = L ∨
              L' = L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup H := pPrimeCore 2 H with hO
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  set sbar : H ⧸ O := π s with hsbar
  set D : Subgroup (H ⧸ O) := Λ.map π with hD
  have hs2 : s ^ 2 = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs] at h
  have hsbar2 : sbar ^ 2 = 1 := by
    rw [hsbar, hπ, ← map_pow, hs2, map_one]
  have hOquot : pPrimeCore 2 (H ⧸ O) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) 2
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))
  obtain ⟨hΛ2, -⟩ := l34Zero_involution_and_card hΛL
  have hmap := isComponent_map_centralizer_quotient_of_isComponent
    (U := O) (t := s) hOodd hs2 hΛs hΛ hΛ2
  have hDmem : D ≤ centralizer ({sbar} : Set (H ⧸ O)) := by
    simpa only [hD, hπ, hsbar] using hmap.1
  have hDcomp : IsComponent (D.subgroupOf (centralizer ({sbar} : Set (H ⧸ O)))) := by
    simpa only [hD, hπ, hsbar] using hmap.2
  have hDq : IsQuasisimple ↥D :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hDmem)).mp hDcomp.1
  have hΛq : IsQuasisimple ↥Λ :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hΛs)).mp hΛ.1
  obtain ⟨hZodd, hZD, htypeD⟩ :=
    l34Zero_type_transfer (U := O) hOodd hΛq hΛ2 hΛodd hΛL hDq
  have hmain := l34Zero_support_cases hcat (hK.quotient O) hOquot hsbar2
    hDmem hDcomp hZD hZodd htypeD
  simpa only [hD, hπ, hO, hsbar] using hmain

end CFSG.ComponentClassification.GrSLit.L34Sec5S
