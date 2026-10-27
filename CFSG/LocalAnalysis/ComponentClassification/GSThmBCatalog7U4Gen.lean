module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Pair
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Frame

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup
open CFSG.ComponentClassification.GSThmB.Catalog7L4 (commutator_comm_of_central
  conj_comm_of_central nontrivial_of_isPComponent')
open scoped commutatorElement

variable {S : Type*} [Group S] [Finite S] {Z : Subgroup S} [Z.Normal]

omit [Finite S] in
theorem comm_mem_center (hZ : Z ≤ center S) {g y : S}
    (hy : QuotientGroup.mk' Z y ∈ centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z))) :
    y * g * y⁻¹ * g⁻¹ ∈ center S := by
  apply hZ
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul, map_inv,
    map_inv, mem_centralizer_singleton_iff.mp hy]
  group

theorem isPComponent_factor (hZ : Z ≤ center S) {g : S} {T : Type*} [Group T]
    (ι : T →* S) (hι : Function.Injective ((QuotientGroup.mk' Z).comp ι))
    (hT : IsQuasisimple T) (hιg : ∀ u, ι u * g = g * ι u)
    (hιn : ∀ z : S, z * g = g * z → ∀ u, z * ι u * z⁻¹ ∈ ι.range) {e : T}
    (he : orderOf e = 2) :
    ((QuotientGroup.mk' Z).comp ι).range ≤
        centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z)) ∧
      IsPComponent 2 ((((QuotientGroup.mk' Z).comp ι).range).subgroupOf
        (centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z)))) ∧
      IsQuasisimple ↥((((QuotientGroup.mk' Z).comp ι).range).subgroupOf
        (centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z)))) := by
  classical
  set π := QuotientGroup.mk' Z with hπ
  set C := centralizer ({π g} : Set (S ⧸ Z)) with hC
  set A := (π.comp ι).range with hA
  set N₀ := centralizer ({g} : Set S) with hN₀
  set N := N₀.map π with hN
  have hAC : A ≤ C := by
    rintro _ ⟨U, rfl⟩
    rw [hC, mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul, hιg]
  have hNC : N ≤ C := by
    rintro _ ⟨W, hW, rfl⟩
    rw [hC, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (mem_centralizer_singleton_iff.mp hW)]
  have hAN : A ≤ N := by
    rintro _ ⟨U, rfl⟩
    exact ⟨ι U, mem_centralizer_singleton_iff.mpr (hιg U), rfl⟩
  have eA : T ≃* A := MonoidHom.ofInjective hι
  have hAq : IsQuasisimple ↥(A.subgroupOf C) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((subgroupOfEquivOfLe hAC).trans eA.symm)).2 hT
  have hNn : (N.subgroupOf C).Normal := by
    constructor
    rintro ⟨n, hnC⟩ hn ⟨c, hc⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨W, hW, rfl⟩ := hn
    obtain ⟨Z', rfl⟩ := QuotientGroup.mk'_surjective Z c
    have hZ' := comm_mem_center hZ hc
    refine ⟨Z' * W * Z'⁻¹, mem_centralizer_singleton_iff.mpr
      (conj_comm_of_central hZ' (mem_centralizer_singleton_iff.mp hW)), ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hAn : ((A.subgroupOf C).subgroupOf (N.subgroupOf C)).Normal := by
    constructor
    rintro ⟨⟨a, haC⟩, haN⟩ ha ⟨⟨n, hnC⟩, hnN⟩
    rw [mem_subgroupOf, mem_subgroupOf] at ha ⊢
    rw [mem_subgroupOf] at hnN
    obtain ⟨W, hW, rfl⟩ := hnN
    obtain ⟨U, rfl⟩ := ha
    obtain ⟨U', hU'⟩ := hιn W (mem_centralizer_singleton_iff.mp hW) U
    refine ⟨U', ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.comp_apply, hU', map_mul, map_inv]
  have hAN' : A.subgroupOf C ≤ N.subgroupOf C := fun y hy => hAN hy
  have hsn : (A.subgroupOf C).IsSubnormal :=
    IsSubnormal.step _ _ hAN' hNn.isSubnormal hAn
  have hnot : ¬ A.subgroupOf C ≤ pPrimeCore 2 ↥C := by
    intro hle
    set x := (π.comp ι) e with hx
    have hxA : x ∈ A := ⟨e, rfl⟩
    have hmem : (⟨x, hAC hxA⟩ : ↥C) ∈ pPrimeCore 2 ↥C := hle (by rw [mem_subgroupOf]; exact hxA)
    have hord : orderOf (⟨⟨x, hAC hxA⟩, hmem⟩ : ↥(pPrimeCore 2 ↥C)) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx, orderOf_injective _ hι, he]
    have hdvd := orderOf_dvd_natCard (⟨⟨x, hAC hxA⟩, hmem⟩ : ↥(pPrimeCore 2 ↥C))
    rw [hord] at hdvd
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥C)
    exact absurd (Nat.Coprime.coprime_dvd_right hdvd hcop) (by norm_num)
  exact ⟨hAC, LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
    ⟨hAq, hsn⟩ hnot, hAq⟩

variable {T : Type*} [Group T]

theorem le_sup_of_pComponent (hZ : Z ≤ center S) {g : S} (ι₁ ι₂ : T →* S)
    (hcomm : ∀ z z' : S, z * g = g * z → z' * g = g * z' → ⁅z, z'⁆ ∈ ι₁.range ⊔ ι₂.range)
    {K : Subgroup (S ⧸ Z)}
    (hKle : K ≤ centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z)))
    (hK : IsPComponent 2 (K.subgroupOf
      (centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z))))) :
    Group.IsPerfect K ∧ Nontrivial K ∧
      K ≤ ((QuotientGroup.mk' Z).comp ι₁).range ⊔ ((QuotientGroup.mk' Z).comp ι₂).range := by
  classical
  set π := QuotientGroup.mk' Z with hπ
  set N₀ := centralizer ({g} : Set S) with hN₀
  have hperf : Group.IsPerfect K := by
    have := CatalogueBAlternating.pComponent_perfect hK
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKle).toMonoidHom)
      (subgroupOfEquivOfLe hKle).surjective
  have hnt : Nontrivial K := by
    have := nontrivial_of_isPComponent' hK
    exact (subgroupOfEquivOfLe hKle).symm.toEquiv.nontrivial
  have hKN : K ≤ N₀.map π := by
    rw [← Subgroup.commutator_eq_self (H := K), Subgroup.commutator_le]
    intro y hy y' hy'
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Z y
    obtain ⟨z', rfl⟩ := QuotientGroup.mk'_surjective Z y'
    exact ⟨⁅z, z'⁆, mem_centralizer_singleton_iff.mpr (commutator_comm_of_central
      (comm_mem_center hZ (hKle hy)) (comm_mem_center hZ (hKle hy'))),
      map_commutatorElement _ _ _⟩
  refine ⟨hperf, hnt, ?_⟩
  rw [← Subgroup.commutator_eq_self (H := K), Subgroup.commutator_le]
  intro y hy y' hy'
  obtain ⟨z, hz, rfl⟩ := hKN hy
  obtain ⟨z', hz', rfl⟩ := hKN hy'
  have hmem := hcomm z z' (mem_centralizer_singleton_iff.mp hz)
    (mem_centralizer_singleton_iff.mp hz')
  have hmap : (ι₁.range ⊔ ι₂.range).map π = (π.comp ι₁).range ⊔ (π.comp ι₂).range := by
    rw [Subgroup.map_sup, MonoidHom.range_comp, MonoidHom.range_comp]
  rw [← map_commutatorElement, ← hmap]
  exact mem_map_of_mem _ hmem

theorem false_of_solvable (hZ : Z ≤ center S) {g : S} (ι₁ ι₂ : T →* S)
    (h12 : ∀ u w, ι₁ u * ι₂ w = ι₂ w * ι₁ u)
    (hcomm : ∀ z z' : S, z * g = g * z → z' * g = g * z' → ⁅z, z'⁆ ∈ ι₁.range ⊔ ι₂.range)
    [Group.IsSolvable T] {K : Subgroup (S ⧸ Z)}
    (hKle : K ≤ centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z)))
    (hK : IsPComponent 2 (K.subgroupOf
      (centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z))))) : False := by
  classical
  obtain ⟨hperf, hnt, hKF⟩ := le_sup_of_pComponent hZ ι₁ ι₂ hcomm hKle hK
  have := hperf
  have := hnt
  set μ : T × T →* S ⧸ Z :=
    (QuotientGroup.mk' Z).comp (MonoidHom.noncommCoprod ι₁ ι₂ fun u w => h12 u w) with hμ
  have hFμ : ((QuotientGroup.mk' Z).comp ι₁).range ⊔ ((QuotientGroup.mk' Z).comp ι₂).range ≤
      μ.range := by
    refine sup_le ?_ ?_
    · rintro _ ⟨U, rfl⟩
      refine ⟨(U, 1), ?_⟩
      change QuotientGroup.mk' Z (ι₁ U * ι₂ 1) = QuotientGroup.mk' Z (ι₁ U)
      rw [map_one, mul_one]
    · rintro _ ⟨W, rfl⟩
      refine ⟨(1, W), ?_⟩
      change QuotientGroup.mk' Z (ι₁ 1 * ι₂ W) = QuotientGroup.mk' Z (ι₂ W)
      rw [map_one, one_mul]
  have : Group.IsSolvable μ.range := Group.isSolvable_of_surjective μ.rangeRestrict_surjective
  have : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hKF.trans hFμ))
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem eq_factor_of_pComponent (hZ : Z ≤ center S) {g : S} (ι₁ ι₂ : T →* S)
    (hcomm : ∀ z z' : S, z * g = g * z → z' * g = g * z' → ⁅z, z'⁆ ∈ ι₁.range ⊔ ι₂.range)
    (hT : IsQuasisimple T) {e : T} (he : orderOf e = 2)
    (hι₁ : Function.Injective ((QuotientGroup.mk' Z).comp ι₁))
    (hι₂ : Function.Injective ((QuotientGroup.mk' Z).comp ι₂))
    (hι₁g : ∀ u, ι₁ u * g = g * ι₁ u) (hι₂g : ∀ u, ι₂ u * g = g * ι₂ u)
    (hι₁n : ∀ z : S, z * g = g * z → ∀ u, z * ι₁ u * z⁻¹ ∈ ι₁.range)
    (hι₂n : ∀ z : S, z * g = g * z → ∀ u, z * ι₂ u * z⁻¹ ∈ ι₂.range)
    {K : Subgroup (S ⧸ Z)}
    (hKle : K ≤ centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z)))
    (hK : IsPComponent 2 (K.subgroupOf
      (centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z))))) :
    K = ((QuotientGroup.mk' Z).comp ι₁).range ∨ K = ((QuotientGroup.mk' Z).comp ι₂).range := by
  classical
  set C := centralizer ({QuotientGroup.mk' Z g} : Set (S ⧸ Z)) with hC
  set A₁ := ((QuotientGroup.mk' Z).comp ι₁).range with hA₁
  set A₂ := ((QuotientGroup.mk' Z).comp ι₂).range with hA₂
  obtain ⟨hperf, hnt, hKF⟩ := le_sup_of_pComponent hZ ι₁ ι₂ hcomm hKle hK
  have := hperf
  obtain ⟨hLC, hL, hqL⟩ := isPComponent_factor hZ ι₁ hι₁ hT hι₁g hι₁n he
  obtain ⟨hRC, hR, hqR⟩ := isPComponent_factor hZ ι₂ hι₂ hT hι₂g hι₂n he
  by_contra hne
  push Not at hne
  obtain ⟨hneL, hneR⟩ := hne
  have hsub : ∀ {A : Subgroup (S ⧸ Z)}, A ≤ C → K ≠ A →
      K.subgroupOf C ≠ A.subgroupOf C := by
    intro A hA hKA h
    apply hKA
    have := subgroupOf_inj.mp h
    rwa [inf_of_le_left hKle, inf_of_le_left hA] at this
  have hcL := ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
    hK hL).2 (hsub hLC hneL)).2.2.2 (Or.inr hqL)
  have hcR := ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
    hK hR).2 (hsub hRC hneR)).2.2.2 (Or.inr hqR)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcL hcR
  have hbot : ⁅K, K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy y' hy'
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hyC : (⟨y, hKle hy⟩ : ↥C) ∈ K.subgroupOf C := by rw [mem_subgroupOf]; exact hy
    have hyA : ∀ {A : Subgroup (S ⧸ Z)} (hA : A ≤ C),
        K.subgroupOf C ≤ centralizer ((A.subgroupOf C : Subgroup ↥C) : Set ↥C) →
        ∀ a ∈ A, a * y = y * a := by
      intro A hA hKA a ha
      have h1 := mem_centralizer_iff.mp (hKA hyC) ⟨a, hA ha⟩
        (show (⟨a, hA ha⟩ : ↥C) ∈ A.subgroupOf C by rw [mem_subgroupOf]; exact ha)
      exact congrArg Subtype.val h1
    have hcent : A₁ ⊔ A₂ ≤ centralizer ({y} : Set (S ⧸ Z)) :=
      sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hyA hLC hcL a ha))
        (fun a ha => mem_centralizer_singleton_iff.mpr (hyA hRC hcR a ha))
    exact (mem_centralizer_singleton_iff.mp (hcent (hKF hy'))).symm
  rw [Subgroup.commutator_eq_self (H := K)] at hbot
  exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt hbot

end Catalog7U4

end CFSG.ComponentClassification.GSThmB
