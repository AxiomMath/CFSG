module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAssemblyStatement
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR8
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.Inheritance

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def NeighbourOvergroupSp2m {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (m f : ℕ) :
    Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Sp2mOvergroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) m f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)))

theorem neighbourOvergroupSp2m_three_iff {Y : Type} [Group Y] {s : Y} {D : Subgroup Y} {f : ℕ} :
    NeighbourOvergroupSp2m s D 3 f ↔ F4Pilot.NeighbourOvergroup s D f :=
  Iff.rfl

theorem neighbour_overgroup_sp2m_of_pPrimeCore_eq_bot {m : ℕ} (hcat : Sp2mCatalogueClausesAt m)
    {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    {f : ℕ} (hDm : LieModel D .PSp m 2 f) : NeighbourOvergroupSp2m s D m f := by
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
      exact hnn (F4Pilot.normal_of_isComponent_of_standard hKc hstd)
    have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
    have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := by
      intro hKs
      rw [inf_eq_left.mpr hKs] at hDcomp
      exact hDne (F4Pilot.eq_of_isComponent_subgroupOf hKc.1 hDK hDcomp)
    have hτ2 := F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
    have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
      rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
      intro x hx
      exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
    set D' : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) :=
      (D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) with hD'
    have hD'c : IsComponent D' := F4Pilot.isComponent_subgroupOf_subgroupOf
      (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
    have hD'm : LieModel D' .PSp m 2 f :=
      LieType.CurtisTits.lieModel_of_mulEquiv
        (F4Pilot.subgroupOfSubgroupOfEquiv hDK hDfix).symm hDm
    have hD'map : D'.map (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)).subtype =
        D.subgroupOf Kc := by
      rw [hD', subgroupOf_map_subtype, inf_eq_left.mpr hDfix]
    have hcatK := hsec Kc hKc
    have hsK : s ∉ Kc := fun hsK =>
      sp2m_not_inner_of_clauses hcat hKc.1 hcatK _ hτ2 D' hD'c hD'm
        (E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK hsyl D' hD'map)
        (F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK)
    exact ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN, sp2m_overgroup_catalogue hcat hKc.1 hcatK _
      hτ2 D' hD'c hD'm
      (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl D' hD'map)⟩
  · right
    obtain ⟨hcomm, -, -, ⟨φ⟩⟩ := hswap hKt
    have hZ : center D = ⊥ :=
      F4Pilot.center_eq_bot_of_isQuasisimple hDq (F4Pilot.isSimpleGroup_of_lieModel_PSp hDm)
    exact ⟨hKt, hcomm,
      ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

theorem lieModel_PSp_map_oddCore {G : Type} [Group G] {H D : Subgroup G} (hDH : D ≤ H)
    {m f : ℕ} (hDm : LieModel D .PSp m 2 f)
    (hne : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≠ ⊥) :
    LieModel ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) .PSp m 2 f := by
  have : IsSimpleGroup D := F4Pilot.isSimpleGroup_of_lieModel_PSp hDm
  have hsimple : IsSimpleGroup (D.subgroupOf H) := (subgroupOfEquivOfLe hDH).isSimpleGroup
  obtain ⟨φ⟩ := F4Pilot.nonempty_mulEquiv_map_of_isSimpleGroup (QuotientGroup.mk' (oddCore H))
    hsimple hne
  exact LieType.CurtisTits.lieModel_of_mulEquiv ((subgroupOfEquivOfLe hDH).symm.trans φ) hDm

theorem neighbour_overgroup_sp2m {m : ℕ} (hcat : Sp2mCatalogueClausesAt m) {G : Type} [Group G]
    [Finite G] (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G)) {f : ℕ}
    (hDm : LieModel D .PSp m 2 f)
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
    NeighbourOvergroupSp2m (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => F4Pilot.catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact neighbour_overgroup_sp2m_of_pPrimeCore_eq_bot hcat
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn (lieModel_PSp_map_oddCore hDX hDm (ne_bot_of_isQuasisimple hcomp.2.2))

section Exact

theorem sp2mOvergroupType_of_mulEquiv {S S' : Type} [Group S] [Group S'] (φ : S ≃* S') {m f : ℕ}
    (h : Sp2mOvergroupType S m f) : Sp2mOvergroupType S' m f := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv φ h)
  · exact Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv φ h))
  · exact Or.inr (Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv φ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv φ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv φ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (LieType.CurtisTits.lieModel_of_mulEquiv φ h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (LieType.CurtisTits.lieModel_of_mulEquiv φ h))))))

theorem map_fixedSubgroup_of_apply_comm {K K' : Type*} [Group K] [Group K'] (ψ : K ≃* K')
    {σ : MulAut K} {σ' : MulAut K'} (h : ∀ x, σ' (ψ x) = ψ (σ x)) :
    (fixedSubgroup σ).map ψ.toMonoidHom = fixedSubgroup σ' := by
  ext y
  obtain ⟨x, rfl⟩ := ψ.surjective y
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  change σ x = x ↔ σ' (ψ x) = ψ x
  rw [h, ψ.injective.eq_iff]

theorem nonempty_fixedSubgroup_mulEquiv_of_center_eq_bot {K : Type} [Group K]
    (hZ : center K = ⊥) (τ : MulAut K) :
    Nonempty (fixedSubgroup (F4Pilot.centerQuotientAut τ) ≃* fixedSubgroup τ) := by
  set ψ : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm with hψ
  have hψmk : ∀ x : K, ψ x = QuotientGroup.mk' (center K) x := by
    intro x
    rw [hψ, MulEquiv.symm_apply_eq]
    rfl
  have hcomm : ∀ x, F4Pilot.centerQuotientAut τ (ψ x) = ψ (τ x) := by
    intro x
    rw [hψmk, hψmk, F4Pilot.centerQuotientAut_mk]
  have hmap := map_fixedSubgroup_of_apply_comm ψ hcomm
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
    ((fixedSubgroup τ).equivMapOfInjective ψ.toMonoidHom ψ.injective).symm⟩

theorem NeighbourOvergroupSp2m.exact {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} {D : Subgroup Y} (hDs : D ≤ centralizer ({s} : Set Y)) {m f : ℕ}
    (hDm : LieModel D .PSp m 2 f) (h : NeighbourOvergroupSp2m s D m f) :
    ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
      ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
          (∃ hsN : s ∈ normalizer (Kc : Set Y),
            Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ Sp2mOvergroupType Kc m f ∧ Kc ⊓ centralizer ({s} : Set Y) = D) ∨
        (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D))) := by
  obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hov⟩ | hswap⟩ := h
  · obtain ⟨hout, hodd, htype, hfix⟩ := hov
    have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc hodd
    have htype' : Sp2mOvergroupType Kc m f := sp2mOvergroupType_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) htype
    obtain ⟨ψ⟩ := nonempty_fixedSubgroup_mulEquiv_of_center_eq_bot hZ
      (Kc.normalizerMonoidHom ⟨s, hsN⟩)
    have hfix' : LieModel (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) .PSp m 2 f :=
      LieType.CurtisTits.lieModel_of_mulEquiv ψ hfix
    have hcard : Nat.card (Kc ⊓ centralizer ({s} : Set Y) : Subgroup Y) ≤ Nat.card D := by
      rw [← F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN,
        card_map_of_injective Kc.subtype_injective,
        F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hfix',
        F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hDm]
    exact ⟨Kc, hKc, hDKK, .inl ⟨hKt, hDK, hsK, ⟨hsN, hout⟩, hZ, htype',
      (Subgroup.eq_of_le_of_card_ge (le_inf hDK.le hDs) hcard).symm⟩⟩
  · exact ⟨Kc, hKc, hDKK, .inr hswap⟩

end Exact

end CFSG.SeitzReduction.SymplecticPilot
