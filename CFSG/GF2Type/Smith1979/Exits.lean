module

public import CFSG.GF2Type.AschbacherFSmith1977
public import CFSG.GF2Type.Entry
public import CFSG.GF2Type.ModelPSL
public import CFSG.LargeExtraspecial.DW37Statement
public import CFSG.LargeExtraspecial.DWW4Rank
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.Yardstones.M3aba7dc4b8a8

variable {G : Type} [Group G] [Finite G] {z : G}

noncomputable abbrev setting {w : ℕ} (hz : orderOf z = 2) (hext : IsExtraspecialPGroup 2 (coreQ z))
    (hcard : Nat.card (coreQ z) = 2 ^ (1 + 2 * w)) : Setting G :=
  Setting.ofFStar z hz (timmesfeld_hypotheses hext hcard).1

theorem setting_z {w : ℕ} (hz : orderOf z = 2) (hext : IsExtraspecialPGroup 2 (coreQ z))
    (hcard : Nat.card (coreQ z) = 2 ^ (1 + 2 * w)) : (setting hz hext hcard).z = z :=
  rfl

theorem setting_width {w : ℕ} (hz : orderOf z = 2) (hext : IsExtraspecialPGroup 2 (coreQ z))
    (hcard : Nat.card (coreQ z) = 2 ^ (1 + 2 * w)) : (setting hz hext hcard).width = w :=
  Bridge.width_ofFStar hz _ (timmesfeld_hypotheses hext hcard).2

theorem setting_QG {w : ℕ} (hz : orderOf z = 2) (hext : IsExtraspecialPGroup 2 (coreQ z))
    (hcard : Nat.card (coreQ z) = 2 ^ (1 + 2 * w)) : (setting hz hext hcard).QG = coreQ z := by
  change (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype =
    (generalizedFitting (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype
  rw [← Bridge.generalizedFitting_eq_timmesfeldFStar]

theorem psu_of_weaklyClosed [IsSimpleGroup G] (h77 : AschbacherFSmith1977Statement) {w : ℕ}
    (hset : GF2RankFourSetting G z) (hext : IsExtraspecialPGroup 2 (coreQ z))
    (hcard : Nat.card (coreQ z) = 2 ^ (1 + 2 * w)) (hw : 5 ≤ w) (hwc : ZWeaklyClosedInCore z) :
    LieModel G .PSU (w + 2) 2 1 :=
  (h77 G hset.1 z hset.2.2.2.2.1 hext w hcard (by omega) hwc).resolve_right fun h => by omega

theorem psl_of_reducible [IsSimpleGroup G] (hDW : DW.DW37Statement) {w : ℕ} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 (coreQ z)) (hcard : Nat.card (coreQ z) = 2 ^ (1 + 2 * w))
    (hw : 5 ≤ w) (hnwc : ¬ ZWeaklyClosedInCore z) (hred : CoreReducible z) :
    LieModel G .PSL (w + 2) 2 1 := by
  obtain ⟨g₀, hg₀Q, hg₀⟩ := DW.W4Rank.exists_conj_of_not_weaklyClosed (setting hz hext hcard)
    (setting_z hz hext hcard) (setting_QG hz hext hcard) hnwc
  obtain ⟨A, hlo, hhi, hnorm⟩ := hred
  have hQ := setting_QG hz hext hcard
  have hRed : (setting hz hext hcard).IsReducible :=
    DW.W4Rank.isReducible_of_lt (setting hz hext hcard) (by rw [hQ]; exact hlo)
      (by rw [hQ]; exact hhi) hnorm
  obtain ⟨e⟩ := hDW G (setting hz hext hcard) g₀ (by rw [setting_width]; exact hw) hg₀Q hg₀ hRed
  have h := lieModel_psl_two_of_mulEquiv (by rw [setting_width]; omega) e
  rwa [setting_width] at h

end CFSG.GF2Type.Smith1979
