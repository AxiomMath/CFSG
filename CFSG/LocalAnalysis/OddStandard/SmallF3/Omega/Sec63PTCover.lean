module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.LocalCores
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem sec63PT_comap_oddCore_eq {P P' : Type*} [Group P] [Group P'] [Finite P] [Finite P']
    (φ : P →* P') (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) :
    (oddCore P').comap φ = oddCore P := by
  apply le_antisymm
  · have hn : ((oddCore P').comap φ).Normal := (oddCore_normal (G := P')).comap φ
    let g := φ.domRestrict ((oddCore P').comap φ)
    have hcard := Subgroup.card_ker_mul_card_range g
    have hrange : Nat.card g.range ∣ Nat.card (oddCore P') := by
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨v, rfl⟩
      exact v.2
    have hkerdvd : Nat.card g.ker ∣ Nat.card φ.ker := by
      have hsub : g.ker.map ((oddCore P').comap φ).subtype ≤ φ.ker := by
        rintro _ ⟨v, hv, rfl⟩
        exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hv)
      rw [← Subgroup.card_map_of_injective (K := g.ker)
        ((oddCore P').comap φ).subtype_injective]
      exact Subgroup.card_dvd_of_le hsub
    have hodd : Odd (Nat.card ((oddCore P').comap φ)) := by
      rw [← hcard]
      exact (hker.of_dvd_nat hkerdvd).mul
        ((odd_card_oddCore (G := P')).of_dvd_nat hrange)
    exact le_sSup ⟨hn, hodd⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have hn : ((oddCore P).map φ).Normal := (oddCore_normal (G := P)).map φ hφ
    have hodd : Odd (Nat.card ((oddCore P).map φ)) :=
      (odd_card_oddCore (G := P)).of_dvd_nat (Subgroup.card_map_dvd _ φ)
    exact le_sSup ⟨hn, hodd⟩

noncomputable def sec63PT_oddCoreQuotientEquiv {P P' : Type*} [Group P] [Group P']
    [Finite P] [Finite P']
    (φ : P →* P') (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) :
    P ⧸ oddCore P ≃* P' ⧸ oddCore P' :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact (sec63PT_comap_oddCore_eq φ hφ hker).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (oddCore P')).comp φ)
      ((QuotientGroup.mk'_surjective _).comp hφ))

theorem sec63PT_lieModel_psl_iff {K K' : Type} [Group K] [Group K'] [Finite K] [Finite K']
    (φ : K →* K') (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) (n p f : ℕ) :
    LieModel (K ⧸ oddCore K) .PSL n p f ↔ LieModel (K' ⧸ oddCore K') .PSL n p f :=
  ⟨fun h => LieModel.of_mulEquiv (sec63PT_oddCoreQuotientEquiv φ hφ hker) h,
    fun h => LieModel.of_mulEquiv (sec63PT_oddCoreQuotientEquiv φ hφ hker).symm h⟩

theorem sec63PT_not_le_center_of_isQuasisimple {X : Type} [Group X] {J : Subgroup X}
    (hJ : IsQuasisimple J) : ¬ J ≤ center X := by
  intro hJZ
  obtain ⟨-, -, a, b, hab⟩ := hJ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h : a * b = b * a := Subtype.ext (mem_center_iff.mp (hJZ a.2) b).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem sec63PT_isComponent_map {X Y : Type} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center X) {J : Subgroup X}
    (hJ : IsComponent J) : IsComponent (J.map π) :=
  ⟨isQuasisimple_map hJ.1 π fun h => sec63PT_not_le_center_of_isQuasisimple hJ.1 (h.trans hker),
    hJ.2.map hπ⟩

theorem sec63PT_eq_of_map_eq {X Y : Type} [Group X] [Group Y] [Finite X] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center X) {J J' : Subgroup X}
    (hJ : IsComponent J) (hJ' : IsComponent J') (h : J.map π = J'.map π) : J = J' := by
  by_contra hne
  have hc : ⁅J, J'⁆ = ⊥ := (distinct_components_commute hJ hJ').resolve_left hne
  have hL := sec63PT_isComponent_map π hπ hker hJ
  have hc' : ⁅J.map π, J'.map π⁆ = ⊥ := by rw [← Subgroup.map_commutator, hc, Subgroup.map_bot]
  rw [← h, Subgroup.isPerfect_iff.mp hL.1.1] at hc'
  have := isQuasisimple_nontrivial hL.1
  exact ((nontrivial_iff_ne_bot _).mp this) hc'

private theorem sec63PT_subgroupMap_ker_le_center {A P : Type} [Group A] [Group P] (ρ : A →* P)
    (hker : ρ.ker ≤ center A) (H : Subgroup A) :
    (ρ.subgroupMap H).ker ≤ center ↥H := by
  intro v hv
  rw [Subgroup.mem_center_iff]
  intro g
  have hv1 : ρ (v : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hv)
  exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hv1)) (g : A))

private theorem sec63PT_map_subgroupMap_subgroupOf {A P : Type} [Group A] [Group P]
    (ρ : A →* P) {H K : Subgroup A} (hKH : K ≤ H) :
    (K.subgroupOf H).map (ρ.subgroupMap H) = (K.map ρ).subgroupOf (H.map ρ) := by
  ext ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxH⟩, hxK, hxy⟩
    exact ⟨x, hxK, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hxK, hxy⟩
    exact ⟨⟨x, hKH hxK⟩, hxK, Subtype.ext hxy⟩

theorem sec63PT_isComponentIn_map {A P : Type} [Group A] [Group P] (ρ : A →* P)
    (hker : ρ.ker ≤ center A) {H K : Subgroup A} (hK : IsComponentIn K H) :
    IsComponentIn (K.map ρ) (H.map ρ) := by
  have hψ : Function.Surjective (ρ.subgroupMap H) := MonoidHom.subgroupMap_surjective ρ H
  have hψker : (ρ.subgroupMap H).ker ≤ center ↥H :=
    sec63PT_subgroupMap_ker_le_center ρ hker H
  refine ⟨Subgroup.map_mono hK.1, ?_⟩
  rw [← sec63PT_map_subgroupMap_subgroupOf ρ hK.1]
  exact sec63PT_isComponent_map (ρ.subgroupMap H) hψ hψker hK.2

theorem sec63PT_eq_of_map_eq_in {A P : Type} [Group A] [Finite A] [Group P] (ρ : A →* P)
    (hker : ρ.ker ≤ center A) {H K K' : Subgroup A} (hK : IsComponentIn K H)
    (hK' : IsComponentIn K' H) (h : K.map ρ = K'.map ρ) : K = K' := by
  have hψ : Function.Surjective (ρ.subgroupMap H) := MonoidHom.subgroupMap_surjective ρ H
  have hψker : (ρ.subgroupMap H).ker ≤ center ↥H :=
    sec63PT_subgroupMap_ker_le_center ρ hker H
  have hEq : K.subgroupOf H = K'.subgroupOf H :=
    sec63PT_eq_of_map_eq (ρ.subgroupMap H) hψ hψker hK.2 hK'.2 (by
      rw [sec63PT_map_subgroupMap_subgroupOf ρ hK.1,
        sec63PT_map_subgroupMap_subgroupOf ρ hK'.1, h])
  have hinf : K ⊓ H = K' ⊓ H := Subgroup.subgroupOf_inj.mp hEq
  rw [inf_eq_left.mpr hK.1, inf_eq_left.mpr hK'.1] at hinf
  exact hinf

theorem sec63PT_map_coverDerived {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {X : Subgroup P} (hX : IsQuasisimple X) :
    (coverDerived ρ X).map ρ = X := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact coverDerived_le X
  · intro q hq
    obtain ⟨a, ha, haq⟩ := h.exists_mem_coverDerived (X := X) hX hq
    exact Subgroup.mem_map.mpr ⟨a, ha, haq⟩

theorem sec63PT_oddCentralCover_subgroupMap {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) (V : Subgroup A) : OddCentralCover (ρ.subgroupMap V) := by
  refine ⟨MonoidHom.subgroupMap_surjective ρ V,
    sec63PT_subgroupMap_ker_le_center ρ h.ker_le_center V, ?_⟩
  have hle : ((ρ.subgroupMap V).ker).map V.subtype ≤ ρ.ker := by
    rintro _ ⟨v, hv, rfl⟩
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hv))
  have hcard : Nat.card ((ρ.subgroupMap V).ker) =
      Nat.card (((ρ.subgroupMap V).ker).map V.subtype) :=
    Nat.card_congr (((ρ.subgroupMap V).ker).equivMapOfInjective _
      V.subtype_injective).toEquiv
  rw [hcard]
  exact h.odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hle)

end CFSG.OddStandard.SmallF3.Omega
