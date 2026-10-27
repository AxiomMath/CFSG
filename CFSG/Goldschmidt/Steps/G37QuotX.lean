module

public import CFSG.Goldschmidt.Steps.G37Quot
import CFSG.Goldschmidt.Steps.Completion
public import CFSG.Goldschmidt.Steps.G37Core

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

theorem isPGroup_zpowers_of_sq {P : Type*} [Group P] {x : P} (hx : x ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨g, hg⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rcases eq_one_or_eq_of_mem_zpowers hx hg with rfl | rfl
  · exact one_pow 2
  · exact hx

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

theorem not_le_oddCoreOf {K : Subgroup G} (hK : GorensteinWalter.IsQuasisimple K) :
    ¬ K ≤ oddCoreOf H := by
  intro h
  have h2 : 2 ∣ Nat.card K := CFSG.Walter.IsQuasisimple.two_dvd_card hK
  have h3 := Subgroup.card_dvd_of_le h
  exact (Nat.not_even_iff_odd.mpr (Completion.odd_card_oddCoreOf H))
    (even_iff_two_dvd.mpr (h2.trans h3))

omit [Finite G] in
theorem isComponentOf_subgroupOf {K X : Subgroup G} (hXH : X ≤ H) (hK : IsComponentOf K X) :
    IsComponentOf (K.subgroupOf H) (X.subgroupOf H) := by
  refine ⟨fun x hx => hK.1 hx, ?_, ?_⟩
  · let ψ : (X.subgroupOf H) →* X :=
      { toFun := fun x => ⟨((x : H) : G), x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    convert hK.2.1.comap ψ using 1
    ext x
    exact Iff.rfl
  · exact CFSG.Walter.isQuasisimple_of_mulEquiv'
      (Subgroup.subgroupOfEquivOfLe (hK.1.trans hXH)).symm hK.2.2

theorem isComponentOf_barOf' {K X : Subgroup G} (hXH : X ≤ H) (hK : IsComponentOf K X) :
    IsComponentOf (barOf H K) (barOf H X) := by
  refine isComponentOf_map' _ (isComponentOf_subgroupOf hXH hK) ?_
  rw [QuotientGroup.ker_mk']
  intro h
  apply not_le_oddCoreOf (H := H) hK.2.2
  have := Subgroup.map_mono (f := H.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le (hK.1.trans hXH)] at this

omit [Finite G] in
theorem barOf_self : barOf H H = ⊤ := by
  rw [barOf, Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem isComponentOf_barOf_top {L : Subgroup G} (hL : IsComponentOf L H) :
    IsComponentOf (barOf H L) ⊤ := by
  have h := isComponentOf_barOf' (le_refl H) hL
  rwa [barOf_self] at h

section X

variable {X : Subgroup G} (hXH : X ≤ H)
include hXH

theorem barOf_componentLayerOf_le :
    barOf H (componentLayerOf X) ≤ componentLayerOf (barOf H X) := by
  have hE : componentLayerOf X ≤ H := (sSup_le fun K hK => hK.1).trans hXH
  rw [← le_preOf_iff hE]
  refine sSup_le fun K hK => ?_
  rw [le_preOf_iff (hK.1.trans hXH)]
  exact le_sSup (isComponentOf_barOf' hXH hK)

theorem barOf_oddFit_le :
    barOf H (oddCoreOf (CFSG.fittingSubgroupOf X)) ≤
      oddCoreOf (CFSG.fittingSubgroupOf (barOf H X)) := by
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have hYX : Y ≤ X := oddFit_le X
  have hYH : Y ≤ H := hYX.trans hXH
  have hYXb : barOf H Y ≤ barOf H X := barOf_mono hYX
  have hXN : barOf H X ≤ Subgroup.normalizer (barOf H Y : Set (H ⧸ goldschmidtOddCore H)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_barOf hYH x.2
      (normalizer_le_normalizer_oddFit X (Subgroup.le_normalizer hx))
  have hnil : Group.IsNilpotent (barOf H Y) := by
    have : Group.IsNilpotent Y := isNilpotent_oddFit X
    have : Group.IsNilpotent (Y.subgroupOf H) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYH).symm
    exact Group.nilpotent_of_surjective _
      ((QuotientGroup.mk' (goldschmidtOddCore H)).subgroupMap_surjective (Y.subgroupOf H))
  have hodd : Odd (Nat.card (barOf H Y)) := by
    have h1 : Nat.card (barOf H Y) ∣ Nat.card (Y.subgroupOf H) := Subgroup.card_map_dvd _ _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv] at h1
    exact (odd_card_oddFit X).of_dvd_nat h1
  have hYF : barOf H Y ≤ CFSG.fittingSubgroupOf (barOf H X) :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent hYXb
      ⟨hYXb, fun h hh k hk => (Subgroup.mem_normalizer_iff.mp (hXN hh) k).mp hk⟩ hnil
  exact Completion.le_oddCoreOf hYF
    (fun f hf => hXN (CFSG.fittingSubgroupOf_le _ hf)) hodd

theorem barOf_eq_sup (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) :
    barOf H X = componentLayerOf (barOf H X) ⊔
      oddCoreOf (CFSG.fittingSubgroupOf (barOf H X)) := by
  apply le_antisymm
  · calc barOf H X = barOf H (componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) :=
          congrArg (barOf H) hXE
      _ = barOf H (componentLayerOf X) ⊔ barOf H (oddCoreOf (CFSG.fittingSubgroupOf X)) :=
          barOf_sup ((sSup_le fun K hK => hK.1).trans hXH) ((oddFit_le X).trans hXH)
      _ ≤ _ := sup_le_sup (barOf_componentLayerOf_le hXH) (barOf_oddFit_le hXH)
  · exact sup_le (sSup_le fun K hK => hK.1) (oddFit_le _)

end X

theorem centralizer_le_barOf {a : G} (haH : a ∈ H) (ha2 : a ^ 2 = 1) :
    Subgroup.centralizer
        ({QuotientGroup.mk' (goldschmidtOddCore H) ⟨a, haH⟩} : Set (H ⧸ goldschmidtOddCore H)) ≤
      barOf H (H ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := Subgroup.zpowers (⟨a, haH⟩ : H) with hT
  have : Fact (IsPGroup 2 T) :=
    ⟨isPGroup_zpowers_of_sq (Subtype.ext (by rw [Subgroup.coe_pow]; exact ha2))⟩
  have hcop : Nat.Coprime 2 (Nat.card (goldschmidtOddCore H)) :=
    Nat.coprime_two_left.mpr (CFSG.Goldschmidt.SStarTransport.odd_card_goldschmidtOddCore H)
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer 2 T (goldschmidtOddCore H)
    (CFSG.Open.goldschmidtOddCore_normal H) hcop
  simp only at h
  rw [hT, MonoidHom.map_zpowers, CFSG.Walter.centralizer_zpowers_eq',
    CFSG.Walter.centralizer_zpowers_eq'] at h
  rw [h]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, Subgroup.mem_inf.mpr ⟨x.2, ?_⟩, rfl⟩
  have hx' : x ∈ Subgroup.centralizer ({⟨a, haH⟩} : Set H) := hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx'
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hx')

theorem centralizer_le_normalizer_barOf {X : Subgroup G} (hXH : X ≤ H) {a : G} (haH : a ∈ H)
    (ha2 : a ^ 2 = 1)
    (hXa : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup.centralizer
        ({QuotientGroup.mk' (goldschmidtOddCore H) ⟨a, haH⟩} : Set (H ⧸ goldschmidtOddCore H)) ≤
      Subgroup.normalizer (barOf H X : Set (H ⧸ goldschmidtOddCore H)) :=
  (centralizer_le_barOf haH ha2).trans ((barOf_mono (le_inf inf_le_left hXa)).trans
    (barOf_normalizer_le hXH))

end CFSG.Goldschmidt.G37
