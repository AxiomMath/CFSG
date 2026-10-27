module

public import CFSG.GF2Type.Smith1979.WidthSix
import CFSG.Holt.General.NoRelevantBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.Yardstones.M3aba7dc4b8a8
  CFSG.EvenSporadicStandard

@[expose] def Smith1979WidthSixCharTwoKP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) = 2 ^ 13 →
        Smith1979WidthSixList G

theorem smith1979WidthSix_of_core (h77 : AschbacherFSmith1977Statement)
    (hDW : DW.DW37Statement) (h80 : Smith1980OrthogonalStatement)
    (hAS : Quasithin.H13.InputAS91) (hcore : WidthSixCore) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharTwoType G)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) {z : G} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 (coreQ z)) (hcard : Nat.card (coreQ z) = 2 ^ 13) :
    Smith1979WidthSixList G := by
  have hcard' : Nat.card (coreQ z) = 2 ^ (1 + 2 * 6) := by rw [hcard]
  by_cases hwc : ZWeaklyClosedInCore z
  · exact Or.inr (Or.inl ((h77 G hnonab z hz hext 6 hcard' (by omega) hwc).resolve_right
      fun h => by omega))
  by_cases hred : CoreReducible z
  · exact Or.inl (psl_of_reducible hDW hz hext hcard' (by norm_num) hwc hred)
  have hS6 : (setting hz hext hcard').width = 6 := setting_width hz hext hcard'
  have hQ := setting_QG hz hext hcard'
  have hex := DW.W4Rank.exists_conj_of_not_weaklyClosed (setting hz hext hcard')
    (setting_z hz hext hcard') hQ hwc
  have hirr : ¬ (setting hz hext hcard').IsReducible := fun h =>
    hred (coreReducible_of_isReducible _ (setting_z hz hext hcard') hQ h)
  rcases hcore G hK (setting hz hext hcard') hS6 hex hirr with
    ⟨q, hq, hiso⟩ | ⟨-, hnc⟩ | ⟨hJ1, hJ2⟩
  ·
    haveI : (generalizedFitting (Subgroup.centralizer ({z} : Set G))).Normal :=
      CFSG.Holt.General.NoRelevant.generalizedFitting_normal
    set Mbar := Subgroup.centralizer ({z} : Set G) ⧸
      generalizedFitting (Subgroup.centralizer ({z} : Set G)) with hMbardef
    have hMbar : timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G)))
        Mbar :=
      ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
    have hMbar' : timmesfeldQuotientIso
        (timmesfeldFStar (Subgroup.centralizer ({(setting hz hext hcard').z} : Set G))) Mbar := by
      rw [← Bridge.generalizedFitting_eq_timmesfeldFStar]
      exact hMbar
    obtain ⟨e⟩ := Bridge.nonempty_mulEquiv_Mbar_ofFStar hz (timmesfeld_hypotheses hext hcard').1
      hMbar'
    have hiso' : Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
        Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q) := by
      rcases hiso with hA | hB
      · obtain ⟨f⟩ := hA
        exact Or.inl ⟨e.symm.trans f⟩
      · obtain ⟨f⟩ := hB
        exact Or.inr ⟨e.symm.trans f⟩
    have h := h80 G hnonab z hz hext 6 hcard' (by norm_num) (by decide) Mbar hMbar q hq hiso'
    by_cases hplus : timmesfeldPlusType q
    · exact Or.inr (Or.inr (Or.inl (h.1 hplus)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h.2 hplus))))
  ·
    exact absurd hchar hnc
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hAS G inferInstance hnonab z hz hJ1 hJ2 ?_)))))
    obtain ⟨g, hgQ, hgz⟩ := hex
    have hO2 : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = coreQ z := by
      change (CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype =
        (generalizedFitting (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype
      have h1 := hJ1.1
      change CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G)) =
        generalizedFitting (Subgroup.centralizer ({z} : Set G)) at h1
      rw [h1]
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hO2, ← hQ, inv_inv]
      exact hgQ
    · rw [inv_inv]
      exact hgz

theorem smith1979WidthSixCharTwoKP_of_core (h77 : AschbacherFSmith1977Statement)
    (hDW : DW.DW37Statement) (h80 : Smith1980OrthogonalStatement)
    (hAS : Quasithin.H13.InputAS91) (hcore : WidthSixCore) : Smith1979WidthSixCharTwoKP :=
  fun _ _ _ _ hnonab hchar hK _ hz hext hcard =>
    smith1979WidthSix_of_core h77 hDW h80 hAS hcore hnonab hchar hK hz hext hcard

end CFSG.GF2Type.Smith1979
