module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step31
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Coords
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Step
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Centr
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Lemma815
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.Sporadic.Co1Patterson.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Layer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIG2
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.Transport
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3NotWeaklyClosed
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Co1TwoB
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalHoltFree
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Basic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Blueprint

namespace Sec3

variable {G : Type} [Group G]

theorem exists_sylow_eq_of_center_le [Finite G] {z : G} {T' : Subgroup G}
    (hT' : IsSylowOf 2 T' (centralizer ({z} : Set G))) (hzT : z ∈ T')
    (hZ : centerIn T' ≤ zpowers z) (hz2 : orderOf z = 2) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hT'.isPGroup.exists_le_sylow
  refine ⟨S, ?_⟩
  have key : ∀ u ∈ (S : Subgroup G), (∀ t ∈ T', u * t * u⁻¹ ∈ T') → u ∈ T' := by
    intro u huS hu
    have huN : u ∈ normalizer (T' : Set G) := AS76b.mem_normalizer_of_map_conj_le (by
      rintro _ ⟨t, ht, rfl⟩
      exact hu t ht)
    have hzZ : z ∈ centerIn T' :=
      ⟨hzT, mem_centralizer_iff.mpr fun t ht => mem_centralizer_singleton_iff.mp (hT'.le ht)⟩
    have h1 := hZ ((mem_normalizer_iff.mp (mem_normalizer_centerIn huN) z).mp hzZ)
    have huz : u * z * u⁻¹ = z := eq_of_mem_zpowers hz2 h1 (by
      intro h
      have hz1 : z ≠ 1 := by
        intro h'
        rw [h', orderOf_one] at hz2
        omega
      apply hz1
      calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
        _ = 1 := by rw [h]; group)
    have huC : u ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc u * z = u * z * u⁻¹ * u := by group
        _ = z * u := by rw [huz]
    have hX2 : IsPGroup 2 ↥(T' ⊔ zpowers u) :=
      S.isPGroup'.to_le (sup_le hTS (zpowers_le.mpr huS))
    have heq := hT'.eq_of_le le_sup_left (sup_le hT'.le (zpowers_le.mpr huC)) hX2
    rw [← heq]
    exact mem_sup_right (mem_zpowers u)
  have : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hnc := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent) (T'.subgroupOf S) ?_
  · apply le_antisymm _ hTS
    intro s hs
    have h : (⟨s, hs⟩ : ↥(S : Subgroup G)) ∈ T'.subgroupOf S := by
      rw [hnc]
      exact mem_top _
    exact mem_subgroupOf.mp h
  · apply le_antisymm _ le_normalizer
    intro u hu
    rw [mem_subgroupOf]
    refine key u u.2 fun t ht => ?_
    have h := (mem_normalizer_iff.mp hu ⟨t, hTS ht⟩).mp (mem_subgroupOf.mpr ht)
    exact mem_subgroupOf.mp h

theorem map_eq_bot_of_isPGroup {H K : Type*} [Group H] [Group K] [Finite K] [IsSimpleGroup K]
    (hK : ∃ a b : K, a * b ≠ b * a) {φ : H →* K} (hφ : Function.Surjective φ) {P : Subgroup H}
    (hPn : P.Normal) (hP : IsPGroup 2 P) : P.map φ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn' : (P.map φ).Normal := hPn.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map φ) with h | h
  · exact h
  · exfalso
    have hK2 : IsPGroup 2 K := by
      have := hP.map φ
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    have hc := hK2.center_nontrivial
    have hcen : center K = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h' | h'
      · exact absurd h' ((Subgroup.nontrivial_iff_ne_bot _).mp hc)
      · exact h'
    obtain ⟨a, b, hab⟩ := hK
    exact hab (mem_center_iff.mp (hcen ▸ mem_top b) a)

theorem center_quotient_center_eq_bot {H : Type*} [Group H]
    (hp : commutator (H ⧸ center H) = ⊤) : center (H ⧸ center H) = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
  rw [mem_bot, QuotientGroup.eq_one_iff]
  have hc : ∀ h : H, x * h * x⁻¹ * h⁻¹ ∈ center H := fun h => by
    have h1 := mem_center_iff.mp hk (h : H ⧸ center H)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have : x * h * x⁻¹ * h⁻¹ = (h * x) * ((h * x)⁻¹ * (x * h)) * (h * x)⁻¹ := by group
    rw [this]
    exact (inferInstance : (center H).Normal).conj_mem _ h1 _
  let f : H →* center H :=
    { toFun := fun h => ⟨x * h * x⁻¹ * h⁻¹, hc h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h k => Subtype.ext (by
        show x * (h * k) * x⁻¹ * (h * k)⁻¹ = x * h * x⁻¹ * h⁻¹ * (x * k * x⁻¹ * k⁻¹)
        have hck := mem_center_iff.mp (hc k) h⁻¹
        calc x * (h * k) * x⁻¹ * (h * k)⁻¹ = x * h * x⁻¹ * ((x * k * x⁻¹ * k⁻¹) * h⁻¹) := by
              group
          _ = x * h * x⁻¹ * (h⁻¹ * (x * k * x⁻¹ * k⁻¹)) := by rw [hck]
          _ = x * h * x⁻¹ * h⁻¹ * (x * k * x⁻¹ * k⁻¹) := by group) }
  have hcomm : commutator H ≤ f.ker := Abelianization.commutator_subset_ker f
  have hcen : center H ≤ f.ker := fun c hc' => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show x * c * x⁻¹ * c⁻¹ = 1
    rw [mem_center_iff.mp hc' x]
    group
  have hsup : commutator H ⊔ center H = ⊤ := by
    rw [eq_top_iff]
    intro h _
    have hm : (h : H ⧸ center H) ∈ (commutator H).map (QuotientGroup.mk' (center H)) := by
      rw [_root_.commutator_def, map_commutator,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← _root_.commutator_def, hp]
      exact mem_top _
    obtain ⟨c, hcC, hch⟩ := hm
    have : c⁻¹ * h ∈ center H := by
      rw [← QuotientGroup.eq]
      exact hch
    have e : h = c * (c⁻¹ * h) := by group
    rw [e]
    exact mul_mem (mem_sup_left hcC) (mem_sup_right this)
  have hker : f.ker = ⊤ := eq_top_iff.mpr (hsup ▸ sup_le hcomm hcen)
  rw [mem_center_iff]
  intro g
  have hg : f g = 1 := MonoidHom.mem_ker.mp (hker ▸ mem_top g)
  have h2 : x * g * x⁻¹ * g⁻¹ = 1 := congrArg Subtype.val hg
  have : x * g = g * x := by
    calc x * g = (x * g * x⁻¹ * g⁻¹) * g * x := by group
      _ = g * x := by rw [h2, one_mul]
  exact this.symm

theorem sec3B_le {A A₁ : Subgroup G} (h : A₁ ≤ A) (x : G) :
    sec3B A₁ x ≤ normalClosure (A : Set G) := by
  unfold sec3B
  have hN : ((normalClosure (A : Set G)).subgroupOf (centralizer ({x} : Set G))).Normal :=
    normalClosure_normal.subgroupOf _
  have hle : normalClosure ((A₁.subgroupOf (centralizer ({x} : Set G)) :
      Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G))) ≤
      (normalClosure (A : Set G)).subgroupOf (centralizer ({x} : Set G)) :=
    normalClosure_le_normal fun c hc => subset_normalClosure (h hc)
  refine (map_mono hle).trans ?_
  rw [subgroupOf_map_subtype]
  exact inf_le_left

theorem isSylowOf_zpowers [Finite G] {Q Q₀ : Subgroup G} {z : G}
    (hQ₀ : IsSylowOf 2 Q₀ (centralizer (Q : Set G))) (hcen : centerIn Q₀ = zpowers z)
    (hz : orderOf z = 2) (hzc : z ∈ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) :
    IsSylowOf 2 (zpowers z) (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G))
  have hPC : P ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := hP.le
  have hPQ₀ : P ≤ centralizer (Q₀ : Set G) :=
    hPC.trans (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hPQ : P ≤ centralizer (Q : Set G) :=
    hPC.trans (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
  have hPN : P ≤ normalizer (Q₀ : Set G) := fun p hp => by
    rw [mem_normalizer_iff]
    intro q
    have hpq : ∀ q ∈ Q₀, p * q * p⁻¹ = q := fun q hq => by
      rw [(mem_centralizer_iff.mp (hPQ₀ hp) q hq).symm, mul_inv_cancel_right]
    constructor
    · intro hq
      rw [hpq q hq]
      exact hq
    · intro hq
      have hc := mem_centralizer_iff.mp (hPQ₀ hp) _ hq
      have e : q = p * q * p⁻¹ := by
        calc q = p⁻¹ * ((p * q * p⁻¹) * p) := by group
          _ = p⁻¹ * (p * (p * q * p⁻¹)) := by rw [hc]
          _ = p * q * p⁻¹ := by group
      rw [e]
      exact hq
  have hW := hP.isPGroup.to_sup_of_normal_right' hQ₀.isPGroup hPN
  have hWeq := hQ₀.eq_of_le le_sup_right (sup_le hPQ hQ₀.le) hW
  have hPle : P ≤ zpowers z := by
    rw [← hcen]
    intro p hp
    exact ⟨hWeq ▸ (mem_sup_left hp : p ∈ P ⊔ Q₀), hPQ₀ hp⟩
  have h2 : IsPGroup 2 (zpowers z) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hz, pow_one]
  have hzC : zpowers z ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := zpowers_le.mpr hzc
  rw [hP.eq_of_le hPle hzC h2]
  exact hP

theorem centralizer_le_of_isSylowOf [Finite G] {Q₁ : Subgroup G} {z : G} (hzQ : z ∈ Q₁)
    (hsyl : IsSylowOf 2 (zpowers z) (centralizer (Q₁ : Set G)))
    (hN : centralizer ({z} : Set G) ≤ normalizer (Q₁ : Set G))
    (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥) :
    centralizer (Q₁ : Set G) ≤ Q₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC : centralizer (Q₁ : Set G) ≤ centralizer ({z} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc z hzQ).symm
  have hNc : zpowers z ≤ centralizer (centralizer (Q₁ : Set G) : Set G) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun c hc =>
      (mem_centralizer_singleton_iff.mp (hLC hc)))
  have hodd : Odd ((zpowers z).relIndex (centralizer (Q₁ : Set G))) := by
    have h := (isSylowOf_iff.mp hsyl).2.2
    rw [Nat.odd_iff]
    exact Nat.two_dvd_ne_zero.mp h
  have hL := eq_sup_oddCoreIn_of_central hsyl.isPGroup hsyl.le hNc hodd
  have hnorm := Asc75T4.normalIn_of_le_normalizer hLC
    (hN.trans fun n hn => mem_normalizer_centralizer hn)
  have hOL : AS76b.oddCoreIn (centralizer (Q₁ : Set G)) = ⊥ :=
    le_bot_iff.mp (hO ▸ Asc75T4.oddCoreIn_le_of_normalIn hnorm)
  rw [hL, hOL, sup_bot_eq]
  exact zpowers_le.mpr hzQ

theorem centralizer_le_of_simple_quotient {K : Type*} [Group K] [IsSimpleGroup K]
    {X Q₁ : Subgroup G} {z x : G} (hX : X.Normal) {φ : ↥(centralizer ({z} : Set G)) →* K}
    (hφ : Function.Surjective φ) (hker : φ.ker = Q₁.subgroupOf (centralizer ({z} : Set G)))
    (hQ₁X : Q₁ ≤ X) (hxC : x ∈ centralizer ({z} : Set G)) (hxX : x ∈ X) (hxQ₁ : x ∉ Q₁) :
    centralizer ({z} : Set G) ≤ X := by
  have hn : (X.subgroupOf (centralizer ({z} : Set G))).Normal := hX.subgroupOf _
  have hn' := hn.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((X.subgroupOf (centralizer ({z} : Set G))).map φ) with h | h
  · exfalso
    have hm : φ ⟨x, hxC⟩ ∈ (X.subgroupOf (centralizer ({z} : Set G))).map φ :=
      ⟨⟨x, hxC⟩, hxX, rfl⟩
    rw [h, mem_bot] at hm
    have hk : (⟨x, hxC⟩ : ↥(centralizer ({z} : Set G))) ∈ φ.ker := hm
    rw [hker] at hk
    exact hxQ₁ hk
  · intro g hg
    have hm : φ ⟨g, hg⟩ ∈ (X.subgroupOf (centralizer ({z} : Set G))).map φ := by
      rw [h]
      exact mem_top _
    obtain ⟨m, hmX, hmg⟩ := hm
    have hk : m⁻¹ * ⟨g, hg⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmg, inv_mul_cancel]
    rw [hker] at hk
    have e : g = (m : G) * ((m⁻¹ * ⟨g, hg⟩ : ↥(centralizer ({z} : Set G))) : G) := by simp
    rw [e]
    exact X.mul_mem hmX (hQ₁X hk)

theorem pattersonCo1Hyp_of [Finite G] {X Q₁ : Subgroup G} {z : G} (hΩ : OmegaPlus8Simple)
    (hXs : IsSimpleGroup X) (hXnc : ∃ a b : X, a * b ≠ b * a) (hz : orderOf z = 2) (hzX : z ∈ X)
    (hCX : centralizer ({z} : Set G) ≤ X)
    (hNC : normalizer (Q₁ : Set G) = centralizer ({z} : Set G))
    (hext : CFSG.IsExtraspecialPGroup 2 Q₁) (hcard : Nat.card Q₁ = 2 ^ 9)
    (hcen : centralizer (Q₁ : Set G) ≤ Q₁)
    {φ : ↥(centralizer ({z} : Set G)) →* ↥(timmesfeldOmegaPlus 4)} (hφ : Function.Surjective φ)
    (hker : φ.ker = Q₁.subgroupOf (centralizer ({z} : Set G))) :
    LargeExtraspecial.S14.PattersonCo1Hyp X ⟨z, hzX⟩ := by
  have : Finite ↥(timmesfeldOmegaPlus 4) := Finite.of_surjective φ hφ
  have : IsSimpleGroup ↥(timmesfeldOmegaPlus 4) := hΩ.1
  let ι : ↥(centralizer ({(⟨z, hzX⟩ : X)} : Set X)) →* G :=
    X.subtype.comp (centralizer ({(⟨z, hzX⟩ : X)} : Set X)).subtype
  have hι : Function.Injective ι := X.subtype_injective.comp (Subgroup.subtype_injective _)
  have hιC : ∀ c, ι c ∈ centralizer ({z} : Set G) := fun c =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2))
  have hιsurj : ∀ g ∈ centralizer ({z} : Set G), ∃ c, ι c = g := fun g hg =>
    ⟨⟨⟨g, hCX hg⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hg))⟩, rfl⟩
  let ι' := ι.codRestrict (centralizer ({z} : Set G)) hιC
  have hι'surj : Function.Surjective ι' := fun g => by
    obtain ⟨c, hc⟩ := hιsurj g g.2
    exact ⟨c, Subtype.ext hc⟩
  have hQC : Q₁ ≤ centralizer ({z} : Set G) := hNC ▸ le_normalizer
  have hQrange : Q₁ ≤ ι.range := fun q hq => hιsurj q (hQC hq)
  have hmap : (Q₁.comap ι).map ι = Q₁ := map_comap_eq_self hQrange
  have hnorm : (Q₁.comap ι).Normal := ⟨fun q hq c => by
    show ι (c * q * c⁻¹) ∈ Q₁
    rw [map_mul, map_mul, map_inv]
    have hcN : ι c ∈ normalizer (Q₁ : Set G) := hNC ▸ hιC c
    exact (mem_normalizer_iff.mp hcN _).mp hq⟩
  let e : (Q₁.comap ι) ≃* Q₁ :=
    (Subgroup.equivMapOfInjective _ ι hι).trans (MulEquiv.subgroupCongr hmap)
  have hext' := LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv e.symm hext
  have hcen' : centralizer ((Q₁.comap ι : Subgroup _) : Set _) ≤ Q₁.comap ι := by
    intro c hc
    show ι c ∈ Q₁
    apply hcen
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp (hQrange hq)
    have hd : d ∈ Q₁.comap ι := hq
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc d hd]
  have hle : ∀ P : Subgroup ↥(centralizer ({(⟨z, hzX⟩ : X)} : Set X)), P.Normal →
      IsPGroup 2 P → P ≤ Q₁.comap ι := by
    intro P hPn hP2
    have hbot := map_eq_bot_of_isPGroup hΩ.2 hφ (hPn.map ι' hι'surj) (hP2.map ι')
    intro c hc
    have h1 : φ (ι' c) = 1 := by
      have hm : φ (ι' c) ∈ (P.map ι').map φ := ⟨ι' c, ⟨c, hc, rfl⟩, rfl⟩
      rwa [hbot, mem_bot] at hm
    have hmem : ι' c ∈ φ.ker := h1
    rw [hker] at hmem
    exact hmem
  let S : LargeExtraspecial.Setting X :=
    { z := ⟨z, hzX⟩
      orderOf_z := (Subgroup.orderOf_mk z hzX).trans hz
      Q := Q₁.comap ι
      normal := hnorm
      extraspecial := hext'
      centralizer_le := hcen'
      le_of_normal := hle }
  have hQF : S.Q = timmesfeldFStar (centralizer ({(⟨z, hzX⟩ : X)} : Set X)) :=
    LargeExtraspecial.Bridge.Q_eq_timmesfeldFStar S
  refine ⟨hXs, hXnc, (Subgroup.orderOf_mk z hzX).trans hz,
    LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_fstar S, ?_, ?_⟩
  · rw [← hQF]
    show Nat.card (Q₁.comap ι) = 2 ^ 9
    rw [Nat.card_congr e.toEquiv, hcard]
  · rw [← hQF]
    refine ⟨φ.comp ι', hφ.comp hι'surj, ?_⟩
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
    rfl

theorem center_eq_bot_of_model {A : Type} [Group A] (hA : commutator A = ⊤)
    (h : ChevalleyExceptionalModel A .G2 2 2) : center A = ⊥ := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  have hc := center_quotient_center_eq_bot (commutator_eq_top_of_mulEquiv e hA)
  rw [← LargeExtraspecial.map_center_of_mulEquiv e] at hc
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hc

end Sec3

theorem stepAS81_of'
    (h75 : AS76b.Asc75Theorem4)
    (hL32 : AS76b.Lemma32) (hL33 : AS76b.Lemma33Three)
    (h187 : RankTwoExceptional.G2Levi187) (htc : RankTwoExceptional.G2TorusConj)
    (h18 : Step18G24) (h110 : Step110) (hQO : GoldschmidtQO)
    (hΩ : OmegaPlus8Simple) (h31 : Step31) (h3S : Step3Suz) (h32 : Step32) (h36 : Step36)
    (h37 : Step37) (h38 : Step38) (h39 : Step39) (h312 : Step312) (hzp : Sec3ZNotPoint) :
    RankTwoExceptional.StepAS81TwoB := by
  intro G _ _ A hH hO hG2 ih
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ1 : center ↥A = ⊥ := Sec3.center_eq_bot_of_model hH.standard.1.1 hG2
  let e : rankTwoQuot A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot
  have hT : TypeG24 (rankTwoQuot A) := SectionRank.chevalleyExceptionalModel_of_mulEquiv e hG2
  have hBase : Base G A :=
    ⟨hH, hO, RankTwoExcHypII.hypII_of_G2 hH.standard.1.1 le_rfl hT, Or.inr hT⟩
  have hZodd : Odd (Nat.card (center ↥A)) := by
    rw [hZ1, Subgroup.card_bot]
    exact odd_one
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := id hT
  obtain ⟨R, hR⟩ := ABGLocalTools.exists_isSylowOf 2 (centralizer (A : Set G))
  obtain ⟨ψ, hψ, g₀, T₀, hc, -, -, hQ⟩ := RankTwoExceptional.exists_config814_g2_coords h75
    hL32 hL33 RankTwoExceptional.g2Centr184 RankTwoExceptional.g2Centr184s h187 htc 2 le_rfl K hK
    eK hBase.hyp31 hZodd hR
  obtain ⟨hQ3, hψinj, hZL⟩ := hQ hZ1
  obtain ⟨hZL', hψx, hL1, hL2⟩ := hZL rfl
  clear hQ hZL
  have hQ3' : Nat.card (RankTwoExceptional.g2Q ψ T₀) = 3 := by
    rw [hQ3, hK]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥(RankTwoExceptional.g2Q ψ T₀) := isCyclic_of_prime_card hQ3'
  obtain ⟨⟨x, hxQ⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥(RankTwoExceptional.g2Q ψ T₀))
  have hx3 : orderOf x = 3 := by
    rw [← Subgroup.orderOf_mk x hxQ, orderOf_eq_card_of_forall_mem_zpowers hgen, hQ3']
  have hQx : RankTwoExceptional.g2Q ψ T₀ = zpowers x := (eq_of_le_of_card_ge
    (zpowers_le.mpr hxQ) (by rw [Nat.card_zpowers, hx3, hQ3'])).symm
  let _ : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hco : Sec3Coords A (AS76b.layerCentralizer A (RankTwoExceptional.g2Q ψ T₀)) x :=
    Sec3.sec3Coords_of (by rw [hK]; norm_num)
      (fun l hl => (mem_inf.1 (AS76b.layerCentralizer_le A _ hl)).1)
      (RankTwoExceptional.g2Q_le hxQ) hx3 hψ hψinj (hψx x hxQ) hL1 hL2
  clear hψx hL1 hL2
  rw [hQx] at hc hZL' hco
  have hxc : centerIn (AS76b.layerCentralizer A (zpowers x)) = zpowers x := by
    rw [← Sec3.map_center_eq_centerIn]
    exact hZL'
  have hne : AS76b.layerCentralizer A (zpowers x) ≠ A := by
    intro h
    have hxA : x ∈ A := hc.le (mem_zpowers x)
    have hxZ : (⟨x, hxA⟩ : ↥A) ∈ center ↥A := by
      rw [mem_center_iff]
      intro a
      have ha : (a : G) ∈ AS76b.layerCentralizer A (zpowers x) := by
        rw [h]
        exact a.2
      have hac := (AS76b.layerCentralizer_le A (zpowers x) ha).2
      exact Subtype.ext (mem_centralizer_iff.mp hac x (mem_zpowers x)).symm
    rw [hZ1, mem_bot] at hxZ
    have hx1 : x = 1 := congrArg Subtype.val hxZ
    rw [hx1, orderOf_one] at hx3
    omega
  have hS₁ : Sec3Pre G A (AS76b.layerCentralizer A (zpowers x)) R x :=
    ⟨hBase, (AS76b.layerCentralizer_le A _).trans inf_le_left, hc.quasisimple, hc.levi, hR,
      hL32 G A hBase.hyp31 R hR, Sec3.four_le_card_of_isSylowOf hR hBase.hyp.rank, hT, hZ1, hne,
      hx3, hxc, ih, rfl, ⟨_, g₀, T₀, hc⟩, hco⟩
  generalize AS76b.layerCentralizer A (zpowers x) = A₁ at hS₁ hne hxc
  obtain ⟨hBc, hBp, hBs⟩ := h31 G A A₁ R x hS₁
  obtain ⟨g, E, F, Zs, P, T, Q, B₀, z, y, hSz⟩ := h3S G A A₁ R x hS₁ hBc hBp hBs
  have hS := hSz.setting
  have hFr := hS.frame
  obtain ⟨D, J, U, hD⟩ := h32 G A A₁ R g E F x Zs P T Q B₀ z y hSz
  obtain ⟨V₀, V, Q₀, hQ0⟩ := h36 G A A₁ R g E F x Zs P T Q B₀ z y D J U hD
  obtain ⟨-, hext, hcard, hQ₀syl, -⟩ := h37 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ0
  have hQext := hSz.q8.1
  have hzcenQ : z ∈ centerIn Q := by
    rw [hSz.Q_center]
    exact mem_zpowers z
  have hz1 : z ≠ 1 := by
    intro h1
    have hc := Sec3.card_centerIn_of_extraspecial hQext
    rw [hSz.Q_center, h1, zpowers_one_eq_bot, Subgroup.card_bot] at hc
    omega
  have hz2 : orderOf z = 2 := orderOf_eq_prime (sq_eq_one_of_extraspecial hQext hSz.Q_center) hz1
  have hzQ : z ∈ Q := hzcenQ.1
  have hzcenQ₀ : z ∈ centerIn Q₀ := by
    rw [hQ0.center_Q₀]
    exact hzcenQ
  have hQ₁C : Q₀ ⊔ Q ≤ centralizer ({z} : Set G) := sup_le
    (fun w hw => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzcenQ₀.2 w hw))
    (fun w hw => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzcenQ.2 w hw))
  have hzc : z ∈ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun w hw => mem_centralizer_singleton_iff.mp (hQ₁C hw)
  have hzQ₁ : z ∈ Q₀ ⊔ Q := mem_sup_right hzQ
  have hcenQ₁ : centerIn (Q₀ ⊔ Q) = zpowers z := Sec3.centerIn_eq_zpowers hext ⟨hzQ₁, hzc⟩ hz1
  have hNC1 : normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
    intro n hn
    have h1 := (mem_normalizer_iff.mp (Sec3.mem_normalizer_centerIn hn) z).mp
      (by rw [hcenQ₁]; exact mem_zpowers z)
    rw [hcenQ₁] at h1
    have h2 : n * z * n⁻¹ = z := Sec3.eq_of_mem_zpowers hz2 h1 (by
      intro h
      apply hz1
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
    rw [mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h2]
  have hsylz := Sec3.isSylowOf_zpowers hQ₀syl (hQ0.center_Q₀.trans hSz.Q_center) hz2 hzc
  obtain ⟨h312i, T', hT'syl, hQ₁T', hT'weak⟩ :=
    h312 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ0
  have hzT' : z ∈ T' := hQ₁T' hzQ₁
  have hZT' : centerIn T' ≤ zpowers z := by
    have h2 : IsPGroup 2 ↥(centerIn T' ⊔ zpowers z) :=
      hT'syl.isPGroup.to_le (sup_le inf_le_left (zpowers_le.mpr hzT'))
    have hle : centerIn T' ⊔ zpowers z ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
      sup_le (fun w hw => Subgroup.centralizer_le hQ₁T' (mem_inf.mp hw).2) (zpowers_le.mpr hzc)
    rw [← hsylz.eq_of_le le_sup_right hle h2]
    exact le_sup_left
  obtain ⟨S', hS'⟩ := Sec3.exists_sylow_eq_of_center_le hT'syl hzT' hZT' hz2
  have h2c : ∃ S' : Sylow 2 G, z ∈ (S' : Subgroup G) ∧
      (S' : Subgroup G) ≤ centralizer ({z} : Set G) :=
    ⟨S', by rw [hS']; exact hzT', by rw [hS']; exact hT'syl.le⟩
  have hHyp : Hyp19 G z (Q₀ ⊔ Q) T' :=
    ⟨hz2, h2c, hQ₁C, hext, Or.inr hcard, hsylz, hT'syl, hQ₁T', hT'weak, h312i⟩
  have hstrong := h110 G z (Q₀ ⊔ Q) T' hHyp
  have hFN : sec3F (Q₀ ⊔ Q) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
    Quasithin.perfectCore_le _
  have hGold := hQO G z (Q₀ ⊔ Q) T' (sec3F (Q₀ ⊔ Q)) hz2 hT'syl hQ₁T' hzQ₁ (Or.inr hcard)
    (fun a ha b hb => commutator_mem_of_extraspecial hext hcenQ₁ ha hb) hstrong
    (hFN.trans hNC1) hFN (h38 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ0).2.2
  have hnp := hzp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ0 hGold
  have hzE : z ∈ E := by
    have h := hSz.z_mem
    rw [hSz.Zs_eq] at h
    have h2 : z ∈ centerIn (E ⊔ F) := h.2
    rw [← hFr.inf_eq_center] at h2
    exact h2.1
  have hOz := h18 G A A₁ R g E F x Zs P T Q B₀ z y hSz z hzE hz2 h2c hnp
  have hCN : centralizer ({z} : Set G) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := by
    rw [hOz, sup_bot_eq] at hGold
    exact hGold
  have hNC : normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) = centralizer ({z} : Set G) :=
    le_antisymm hNC1 hCN
  have hON : AS76b.oddCoreIn (normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) = ⊥ := by
    rw [hNC]
    exact hOz
  obtain ⟨φ₀, hφ₀, hker₀⟩ := h39 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ0 hON
  let φ := φ₀.comp (MulEquiv.subgroupCongr hNC.symm).toMonoidHom
  have hφ : Function.Surjective φ := hφ₀.comp (MulEquiv.subgroupCongr hNC.symm).surjective
  have hker : φ.ker = (Q₀ ⊔ Q).subgroupOf (centralizer ({z} : Set G)) := by
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker₀, hON, sup_bot_eq]
    rfl
  have hcen : centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) ≤ Q₀ ⊔ Q :=
    Sec3.centralizer_le_of_isSylowOf hzQ₁ hsylz hCN hOz
  obtain ⟨hXF, hXsimple⟩ := AS76b.asc08Lemma34 G A hBase.hyp31
  have hXs : IsSimpleGroup ↥(rankTwoX A) := by
    show IsSimpleGroup ↥(normalClosure (A : Set G))
    rw [hXF]
    exact hXsimple
  have hXnc : ∃ a b : ↥(rankTwoX A), a * b ≠ b * a := by
    have : IsSimpleGroup (↥A ⧸ center ↥A) := hH.standard.1.2
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥A ⧸ center ↥A)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have ha : a ∉ center ↥A := fun h => hq ((QuotientGroup.eq_one_iff a).mpr h)
    rw [mem_center_iff] at ha
    push Not at ha
    obtain ⟨b, hb⟩ := ha
    refine ⟨⟨b, le_normalClosure b.2⟩, ⟨a, le_normalClosure a.2⟩, fun h => hb ?_⟩
    have h' := congrArg (fun t : ↥(rankTwoX A) => (t : G)) h
    exact Subtype.ext h'
  have hxA₁ : x ∈ A₁ := (show x ∈ centerIn A₁ by rw [hxc]; exact mem_zpowers x).1
  have hxA : x ∈ A := hFr.le hxA₁
  have hDA : D ≤ A := by
    rw [hD.D_eq]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hV₀A : V₀ ≤ A := fun v hv => by
    have hv' : v ∈ (V₀ : Set G) := hv
    rw [hQ0.V₀_eq] at hv'
    exact hDA hv'.1
  have hVA : V ≤ A := by
    rw [hQ0.V_eq, commutator_le]
    intro a ha b hb
    have hbA : b ∈ A := zpowers_le.mpr hxA hb
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem (hV₀A ha) hbA) (A.inv_mem (hV₀A ha))) (A.inv_mem hbA)
  have hQ₁X : Q₀ ⊔ Q ≤ rankTwoX A :=
    sup_le ((hQ0.Q₀_le.trans hVA).trans le_normalClosure)
      (hSz.Q_le.trans (hSz.T_le.trans (Sec3.sec3B_le hFr.le x)))
  have hzX : z ∈ rankTwoX A := hQ₁X hzQ₁
  have hxC : x ∈ centralizer ({z} : Set G) := by
    have hzA₁ : z ∈ A₁ := by
      have h := hSz.z_mem
      rw [hSz.Zs_eq] at h
      exact h.1
    have hxc' : x ∈ centralizer (A₁ : Set G) :=
      (show x ∈ centerIn A₁ by rw [hxc]; exact mem_zpowers x).2
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxc' z hzA₁).symm
  have hxQ₁ : x ∉ Q₀ ⊔ Q := by
    intro hx
    obtain ⟨k, hk⟩ := hext.1 ⟨x, hx⟩
    have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hx3] at h2
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  have hCX : centralizer ({z} : Set G) ≤ rankTwoX A := by
    have : IsSimpleGroup ↥(timmesfeldOmegaPlus 4) := hΩ.1
    exact Sec3.centralizer_le_of_simple_quotient normalClosure_normal hφ hker hQ₁X hxC
      (le_normalClosure hxA) hxQ₁
  have hP := Sec3.pattersonCo1Hyp_of hΩ hXs hXnc hz2 hzX hCX hNC hext hcard hcen hφ hker
  obtain ⟨n, hnA₁, hnQ, hne⟩ := Sec3.exists_conj_mem_Q hSz hz1
  exact ⟨⟨z, hzX⟩, hP, Sec3.notWeaklyClosed_of hzX hNC hext.1 (le_normalClosure (hFr.le hnA₁))
    (mem_sup_right hnQ) hne hP, Sec3.co1TwoBData_of hSz hz1 hzX⟩

end CFSG.ComponentClassification.AS81

