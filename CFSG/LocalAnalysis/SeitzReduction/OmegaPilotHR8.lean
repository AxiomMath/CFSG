module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OmegaNeighbourAlternative {Y : Type} [Group Y] (s : Y) (D Kc : Subgroup Y)
    (m f : ℕ) : Prop :=
  D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          OmegaOvergroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) m f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D)))

@[expose] def NeighbourOvergroupOmega {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (m f : ℕ) :
    Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ OmegaNeighbourAlternative s D Kc m f

theorem OmegaNeighbourAlternative.map_conj_of_swap {Y : Type} [Group Y] {s : Y} (hs2 : s ^ 2 = 1)
    {D Kc : Subgroup Y} {m f : ℕ} (hDKK : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥) (hZ : center Kc = ⊥)
    (hφ : Nonempty (Kc ≃* D)) :
    OmegaNeighbourAlternative s D (Kc.map (MulAut.conj s).toMonoidHom) m f := by
  obtain ⟨φ⟩ := hφ
  have hKK := CentralizerComponents.map_conj_map_conj hs2 Kc
  set ψ : Kc ≃* Kc.map (MulAut.conj s).toMonoidHom :=
    Kc.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
  refine ⟨by rw [hKK, sup_comm]; exact hDKK, Or.inr ⟨by rw [hKK]; exact fun h => hKt h.symm, ?_,
    ?_, ⟨ψ.symm.trans φ⟩⟩⟩
  · rw [hKK, commutator_comm]
    exact hcomm
  · rw [← map_center_eq ψ, hZ, Subgroup.map_bot]

theorem neighbour_overgroup_omega_of_pPrimeCore_eq_bot {m f : ℕ} (hmf : (m, f) ≠ (4, 1))
    (hcat : OmegaCatalogueClausesAt m) {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    {tag : StatedLieTag} (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus)
    (hDm : LieModel (D ⧸ center D) tag m 2 f) (hZD : Odd (Nat.card (center D))) :
    NeighbourOvergroupOmega s D m f ∧
      ∀ Lc : Subgroup Y, IsComponent Lc → ⁅D, Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative s D Lc m f := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, hiff, hfix, hswap⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  have hK : OmegaNeighbourAlternative s D Kc m f := by
    refine ⟨hDKK, ?_⟩
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
      obtain ⟨hD'c, hD'm, hD'map, hD'Z⟩ :=
        UnitaryPilot.isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK hDs hDcomp hDm
      have hcatK := hsec Kc hKc
      have hsK : s ∉ Kc := fun hsK =>
        omega_not_inner_of_clauses hcat hKc.1 hcatK _ hτ2 htag hmf _ hD'c hD'm (hD'Z ▸ hZD)
          (E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK hsyl _ hD'map)
          (F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK)
      exact ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN, omega_overgroup_catalogue hcat
        hKc.1 hcatK _ hτ2 htag _ hD'c hD'm
        (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl _ hD'map)⟩
    · right
      obtain ⟨hcomm, -, hdiag, -⟩ := hswap hKt
      exact ⟨hKt, hcomm,
        LinearPilot.center_eq_bot_and_nonempty_mulEquiv_of_swap hO hs hKc hKt hcomm hdiag hDs
          hsyl⟩
  refine ⟨⟨Kc, hKc, hK⟩, fun Lc hLc hDLc => ?_⟩
  rcases (hiff Lc hLc).1 hDLc with rfl | rfl
  · exact hK
  · by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
    · rw [hKt]
      exact hK
    · obtain ⟨-, ⟨hKt', -⟩ | ⟨-, hcomm, hZ, hφ⟩⟩ := hK
      · exact absurd hKt' hKt
      · exact OmegaNeighbourAlternative.map_conj_of_swap hs2 hDKK hKt hcomm hZ hφ

theorem OmegaNeighbourAlternative.exact {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} {D Kc : Subgroup Y} (hKc : IsComponent Kc) {m f : ℕ} (hmf : (m, f) ≠ (4, 1))
    (h : OmegaNeighbourAlternative s D Kc m f) :
    D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
      ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
          (∃ hsN : s ∈ normalizer (Kc : Set Y),
            Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .POmegaPlus m 2 (2 * f)) ∨
        (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧
            Nonempty (Kc ≃* D))) := by
  obtain ⟨hDKK, ⟨hKt, hDK, hsK, hsN, hout, hZodd, hlist⟩ | hswap⟩ := h
  · have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc hZodd
    have hmodel : LieModel (Kc ⧸ center Kc) .POmegaPlus m 2 (2 * f) :=
      hlist.resolve_right (not_omegaSmall_of_ne hmf)
    exact ⟨hDKK, .inl ⟨hKt, hDK, hsK, ⟨hsN, hout⟩, hZ, LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel⟩⟩
  · exact ⟨hDKK, .inr hswap⟩

theorem orderOf_normalizerMonoidHom_of_not_mem_range {Y : Type} [Group Y] {s : Y}
    (hs2 : s ^ 2 = 1) {Kc : Subgroup Y} {hsN : s ∈ normalizer (Kc : Set Y)}
    (hout : Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) :
    orderOf (Kc.normalizerMonoidHom ⟨s, hsN⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hs2) fun h1 => ?_
  apply hout
  rw [h1]
  exact one_mem _

theorem neighbour_overgroup_omega {m f : ℕ} (hmf : (m, f) ≠ (4, 1))
    (hcat : OmegaCatalogueClausesAt m) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G))
    (hDq : CFSG.IsQuasisimple D) {tag : StatedLieTag}
    (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus) (hDm : LieModel (D ⧸ center D) tag m 2 f)
    (hZD : Odd (Nat.card (center D)))
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
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc m f := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => F4Pilot.catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hne := ne_bot_of_isQuasisimple hcomp.2.2
  exact neighbour_overgroup_omega_of_pPrimeCore_eq_bot hmf hcat
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn htag (UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq hDm hne)
    (UnitaryPilot.odd_card_center_map_subgroupOf_oddCore hDX hDq hZD hne)

end CFSG.SeitzReduction.OmegaPilot
