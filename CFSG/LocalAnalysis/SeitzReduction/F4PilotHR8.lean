module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.Inheritance

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def NeighbourOvergroup {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (f : ℕ) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Sp6Overgroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)))

theorem neighbour_overgroup_of_pPrimeCore_eq_bot (hcat : Sp6CatalogueClauses) {Y : Type}
    [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    {f : ℕ} (hD6 : LieModel D .PSp 3 2 f) : NeighbourOvergroup s D f := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, -, hfix, hswap⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  have hDq : IsQuasisimple D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDs) hDc.1
  refine ⟨Kc, hKc, hDKK, ?_⟩
  by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
  · left
    obtain ⟨hDK, hDcomp⟩ := hfix hKt
    have hDne : D ≠ Kc := by
      rintro rfl
      exact hnn (normal_of_isComponent_of_standard hKc hstd)
    have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
    have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := by
      intro hKs
      rw [inf_eq_left.mpr hKs] at hDcomp
      exact hDne (eq_of_isComponent_subgroupOf hKc.1 hDK hDcomp)
    have hτ2 := orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
    have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
      rw [fixedSubgroup_normalizerMonoidHom]
      intro x hx
      exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
    set D' : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) :=
      (D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) with hD'
    have hD'c : IsComponent D' :=
      isComponent_subgroupOf_subgroupOf (map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
    have hD'6 : LieModel D' .PSp 3 2 f :=
      LieType.CurtisTits.lieModel_of_mulEquiv (subgroupOfSubgroupOfEquiv hDK hDfix).symm hD6
    have hcatK := hsec Kc hKc
    have hsK : s ∉ Kc := fun hsK =>
      sp6_not_inner_of_clauses hcat hKc.1 hcatK _ hτ2 D' hD'c hD'6
        (normalizerMonoidHom_mem_range_conj Kc hsN hsK)
    have hD'map : D'.map (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)).subtype =
        D.subgroupOf Kc := by
      rw [hD', subgroupOf_map_subtype, inf_eq_left.mpr hDfix]
    exact ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN, sp6_overgroup_catalogue hcat hKc.1 hcatK _
      hτ2 D' hD'c hD'6 (fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl D' hD'map)⟩
  · right
    obtain ⟨hcomm, -, -, ⟨φ⟩⟩ := hswap hKt
    have hZ : center D = ⊥ :=
      center_eq_bot_of_isQuasisimple hDq (isSimpleGroup_of_lieModel_PSp hD6)
    exact ⟨hKt, hcomm,
      ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

theorem lieModel_map_oddCore {G : Type} [Group G] {H D : Subgroup G} (hDH : D ≤ H) {f : ℕ}
    (hD6 : LieModel D .PSp 3 2 f)
    (hne : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≠ ⊥) :
    LieModel ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) .PSp 3 2 f := by
  have : IsSimpleGroup D := isSimpleGroup_of_lieModel_PSp hD6
  have hsimple : IsSimpleGroup (D.subgroupOf H) := (subgroupOfEquivOfLe hDH).isSimpleGroup
  obtain ⟨φ⟩ := nonempty_mulEquiv_map_of_isSimpleGroup (QuotientGroup.mk' (oddCore H)) hsimple hne
  exact LieType.CurtisTits.lieModel_of_mulEquiv ((subgroupOfEquivOfLe hDH).symm.trans φ) hD6

theorem neighbour_overgroup (hcat : Sp6CatalogueClauses) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G)) {f : ℕ}
    (hD6 : LieModel D .PSp 3 2 f)
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
    NeighbourOvergroup (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact neighbour_overgroup_of_pPrimeCore_eq_bot hcat
    (pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl hstd
    hnn (lieModel_map_oddCore hDX hD6 (ne_bot_of_isQuasisimple hcomp.2.2))

end CFSG.SeitzReduction.F4Pilot
