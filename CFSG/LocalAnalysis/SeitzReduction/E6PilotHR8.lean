module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Basic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (SLmOvergroup SLmSmall SLmCatalogueClausesAt
  FixedCentralizerTwoSmall)

@[expose] def NeighbourOvergroupSL {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (m f : ℕ) :
    Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          SLmOvergroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) m f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)))

theorem not_slmSmall {S : Type} [Group S] {m f : ℕ} (hmf : 5 ≤ m ∨ 2 ≤ f) :
    ¬ SLmSmall S m f := by
  rintro ⟨rfl, h⟩
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨h34, -⟩ <;> omega

theorem lieModel_quotient_center_of_slmOvergroup {K : Type} [Group K] {τ : MulAut K} {m f : ℕ}
    (h : SLmOvergroup K τ m f) (hmf : 5 ≤ m ∨ 2 ≤ f) :
    LieModel (K ⧸ center K) .PSL m 2 (2 * f) :=
  h.2.2.resolve_right (not_slmSmall hmf)

theorem center_eq_bot_of_isComponent_of_odd {Y : Type*} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {Kc : Subgroup Y} (hKc : IsComponent Kc)
    (hodd : Odd (Nat.card (center Kc))) : center Kc = ⊥ := by
  set Z : Subgroup Y := (center Kc).map Kc.subtype with hZ
  have hZsn : Z.IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hKc.2
  have hZodd : Odd (Nat.card Z) := by
    rw [hZ, card_map_of_injective Kc.subtype_injective]
    exact hodd
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hZsn
  have htop : pPrimeCore 2 Z = ⊤ :=
    le_antisymm le_top (le_sSup ⟨normal_top, by
      rw [card_top]
      exact Nat.coprime_two_left.mpr hZodd⟩)
  rw [htop, ← MonoidHom.range_eq_map, range_subtype, hO] at h1
  rw [eq_bot_iff]
  intro z hz
  have hzZ : (z : Y) ∈ Z := ⟨z, hz, rfl⟩
  exact (mem_bot).mpr (Subtype.ext ((mem_bot).mp (h1 hzZ)))

theorem lieModel_of_slmOvergroup_of_pPrimeCore_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {Kc : Subgroup Y} (hKc : IsComponent Kc) {τ : MulAut Kc}
    {m f : ℕ} (h : SLmOvergroup Kc τ m f) (hmf : 5 ≤ m ∨ 2 ≤ f) :
    center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f) := by
  have hZ := center_eq_bot_of_isComponent_of_odd hO hKc h.2.1
  exact ⟨hZ, LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
    (lieModel_quotient_center_of_slmOvergroup h hmf)⟩

theorem fixedCentralizerTwoSmall_of_card_le_two {Y : Type} [Group Y] {K D : Subgroup Y}
    (σ : MulAut K) (hDK : D ≤ K)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (D' : Subgroup (fixedSubgroup σ))
    (hD' : D'.map (fixedSubgroup σ).subtype = D.subgroupOf K) :
    FixedCentralizerTwoSmall σ D' := by
  intro U hU hUD _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hD'] at hUD
  have hU'D : U.map K.subtype ≤ centralizer (D : Set Y) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have h := mem_centralizer_iff.mp (hUD hu) ⟨d, hDK hd⟩ (mem_subgroupOf.mpr hd)
    exact congrArg Subtype.val h
  have h2 := hsyl _ (hU.map _) hU'D
  rwa [card_map_of_injective K.subtype_injective] at h2

theorem isComponent_fixedSubgroup_of_le {Y : Type} [Group Y] {s : Y} {Kc D : Subgroup Y}
    (hsN : s ∈ normalizer (Kc : Set Y)) (hDK : D ≤ Kc) (hDs : D ≤ centralizer ({s} : Set Y))
    (hDcomp : IsComponent (D.subgroupOf (Kc ⊓ centralizer ({s} : Set Y)))) {m f : ℕ}
    (hDm : LieModel D .PSL m 2 f) :
    IsComponent
        ((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) ∧
      LieModel
        (((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) ⧸
          center ((D.subgroupOf Kc).subgroupOf
            (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)))) .PSL m 2 f ∧
      ((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))).map
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)).subtype = D.subgroupOf Kc := by
  have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
    rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  have hD'c := F4Pilot.isComponent_subgroupOf_subgroupOf
    (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
  have hD'm := LieType.CurtisTits.lieModel_of_mulEquiv
    (F4Pilot.subgroupOfSubgroupOfEquiv hDK hDfix).symm hDm
  exact ⟨hD'c, LinearPilot.lieModel_quotient_center_of_center_eq_bot
    (F4Pilot.center_eq_bot_of_isQuasisimple hD'c.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSL hD'm)) hD'm,
    by rw [subgroupOf_map_subtype, inf_eq_left.mpr hDfix]⟩

theorem neighbour_overgroup_slm_of_pPrimeCore_eq_bot {m f : ℕ} (hm : 3 ≤ m)
    (hmf : 5 ≤ m ∨ 2 ≤ f) (hcat : SLmCatalogueClausesAt m) {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    (hDm : LieModel D .PSL m 2 f) : NeighbourOvergroupSL s D m f := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, -, hfix, hswap⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  have hDq : IsQuasisimple D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDs) hDc.1
  have hZ : center D = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hDq
    (LinearPilot.isSimpleGroup_of_lieModel_PSL hDm)
  refine ⟨Kc, hKc, hDKK, ?_⟩
  by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
  · left
    obtain ⟨hDK, hDcomp⟩ := hfix hKt
    have hDne : D ≠ Kc := by
      rintro rfl
      exact hnn (F4Pilot.normal_of_isComponent_of_standard hKc hstd)
    have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
    have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := by
      intro hKs
      rw [inf_eq_left.mpr hKs] at hDcomp
      exact hDne (F4Pilot.eq_of_isComponent_subgroupOf hKc.1 hDK hDcomp)
    have hτ2 := F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
    obtain ⟨hD'c, hD'm, hD'map⟩ := isComponent_fixedSubgroup_of_le hsN hDK hDs hDcomp hDm
    have hcatK := hsec Kc hKc
    have hsK : s ∉ Kc := fun hsK =>
      not_slmSmall hmf (LinearPilot.slm_inner_small_of_clauses hcat hKc.1 hcatK _ hτ2 hm _
        hD'c hD'm (F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK)
        (fixedCentralizerTwoSmall_of_card_le_two _ hDK hsyl _ hD'map))
    exact ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN, LinearPilot.slm_overgroup_catalogue hcat
      hKc.1 hcatK _ hτ2 hm _ hD'c hD'm
      (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl _ hD'map)⟩
  · right
    obtain ⟨hcomm, -, -, ⟨φ⟩⟩ := hswap hKt
    exact ⟨hKt, hcomm,
      ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

theorem neighbour_overgroup_E6_of_pPrimeCore_eq_bot (hcat : SLmCatalogueClausesAt 6) {Y : Type}
    [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    {f : ℕ} (hD6 : LieModel D .PSL 6 2 f) : NeighbourOvergroupSL s D 6 f :=
  neighbour_overgroup_slm_of_pPrimeCore_eq_bot (by norm_num) (Or.inl (by norm_num)) hcat hO hsec
    hs hD hsyl hstd hnn hD6

theorem lieModel_PSL_map_oddCore {G : Type} [Group G] {H D : Subgroup G} (hDH : D ≤ H)
    {m f : ℕ} (hDm : LieModel D .PSL m 2 f)
    (hne : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≠ ⊥) :
    LieModel ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) .PSL m 2 f := by
  have : IsSimpleGroup D := LinearPilot.isSimpleGroup_of_lieModel_PSL hDm
  have hsimple : IsSimpleGroup (D.subgroupOf H) := (subgroupOfEquivOfLe hDH).isSimpleGroup
  obtain ⟨φ⟩ := F4Pilot.nonempty_mulEquiv_map_of_isSimpleGroup (QuotientGroup.mk' (oddCore H))
    hsimple hne
  exact LieType.CurtisTits.lieModel_of_mulEquiv ((subgroupOfEquivOfLe hDH).symm.trans φ) hDm

theorem neighbour_overgroup_slm {m f : ℕ} (hm : 3 ≤ m) (hmf : 5 ≤ m ∨ 2 ≤ f)
    (hcat : SLmCatalogueClausesAt m) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G))
    (hDm : LieModel D .PSL m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => F4Pilot.catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact neighbour_overgroup_slm_of_pPrimeCore_eq_bot hm hmf hcat
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn (lieModel_PSL_map_oddCore hDX hDm (ne_bot_of_isQuasisimple hcomp.2.2))

theorem neighbour_overgroup_E6 (hcat : SLmCatalogueClausesAt 6) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G)) {f : ℕ}
    (hD6 : LieModel D .PSL 6 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f :=
  neighbour_overgroup_slm (by norm_num) (Or.inl (by norm_num)) hcat hKP hXG htX ht hDX hD6 hcomp
    hsyl hstd hnn

theorem NeighbourOvergroupSL.exact {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} {D : Subgroup Y} {m f : ℕ} (hmf : 5 ≤ m ∨ 2 ≤ f) (h : NeighbourOvergroupSL s D m f) :
    ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
      ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
          (∃ hsN : s ∈ normalizer (Kc : Set Y),
            Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f)) ∨
        (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D))) := by
  obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hov⟩ | hswap⟩ := h
  · obtain ⟨hZ, hmodel⟩ := lieModel_of_slmOvergroup_of_pPrimeCore_eq_bot hO hKc hov hmf
    exact ⟨Kc, hKc, hDKK, .inl ⟨hKt, hDK, hsK, ⟨hsN, hov.1⟩, hZ, hmodel⟩⟩
  · exact ⟨Kc, hKc, hDKK, .inr hswap⟩

end CFSG.SeitzReduction.E6Pilot
