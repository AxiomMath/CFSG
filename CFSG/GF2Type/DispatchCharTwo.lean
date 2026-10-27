module

public import CFSG.GF2Type.Dispatch
public import CFSG.GF2Type.Smith1979CharTwoKP
import CFSG.GF2Type.Entry
import CFSG.GF2Type.ListIntro
import CFSG.GF2Type.ModelPSL
import CFSG.GF2Type.ModelPSU
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GF2Type.Smith1980Orthogonal
public import CFSG.GF2Type.Smith1980TypeE
public import CFSG.LargeExtraspecial.BridgeConclusion

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.RankThree.GF2n
  CFSG.LargeExtraspecial.Bridge
open scoped MatrixGroups

section CasesAt

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G} (hz : orderOf z = 2)
  (hext : IsExtraspecialPGroup 2
    (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)))) {w : ℕ}
  (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
    2 ^ (1 + 2 * w))

include hz hext hcard

theorem gf2TypeList_of_width_three_four_at (h79 : Smith1979Conclusion G) (hw : w = 3 ∨ w = 4) :
    GF2TypeList G := by
  rcases hw with rfl | rfl
  · rcases (h79 z hz hext _ hcard).1 rfl with h | h | h | h | h
    · exact gf2TypeList_of_psl (by norm_num) h
    · exact gf2TypeList_of_psu (by norm_num) h
    · exact gf2TypeList_of_sporadic (s := .M24) (by simp) h
    · exact gf2TypeList_of_sporadic (s := .He) (by simp) h
    · exact gf2TypeList_of_sporadic (s := .Suz) (by simp) h
  · rcases (h79 z hz hext _ hcard).2.1 rfl with h | h | h | h | h | h | h | h | h | h
    · exact gf2TypeList_of_psl (by norm_num) h
    · exact gf2TypeList_of_psu (by norm_num) h
    · exact gf2TypeList_of_omegaPlus (by norm_num) h
    · exact gf2TypeList_of_omegaMinus (by norm_num) h
    · exact gf2TypeList_of_exceptional (s := .trialityD4) (by simp) h
    · exact gf2TypeList_of_three (s := .POmegaPlus) (n := 4) (by simp) h
    · exact gf2TypeList_of_sporadic (s := .Co2) (by simp) h
    · exact gf2TypeList_of_sporadic (s := .Co1) (by simp) h
    · exact gf2TypeList_of_sporadic (s := .Th) (by simp) h
    · exact gf2TypeList_of_sporadic (s := .HN) (by simp) h

theorem gf2TypeList_of_width_six_at (h79 : Smith1979Conclusion G) (hw : w = 6) :
    GF2TypeList G := by
  subst hw
  rcases (h79 z hz hext _ hcard).2.2.1 rfl with h | h | h | h | h | h
  · exact gf2TypeList_of_psl (by norm_num) h
  · exact gf2TypeList_of_psu (by norm_num) h
  · exact gf2TypeList_of_omegaPlus (by norm_num) h
  · exact gf2TypeList_of_omegaMinus (by norm_num) h
  · exact gf2TypeList_of_sporadic (s := .J4) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .Fi24Prime) (by simp) h

theorem gf2TypeList_of_wide_at (hnonab : ∃ a b : G, a * b ≠ b * a) (h79 : Smith1979Conclusion G)
    (h80a : Smith1980OrthogonalStatement)
    (h80b : Smith1980TypeEStatement) (hT : MainStatement) (hw : 5 ≤ w) : GF2TypeList G := by
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  obtain ⟨Mbar, _, hMbar⟩ :=
    exists_quotient_generalizedFitting ↥(Subgroup.centralizer ({z} : Set G))
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have h80 := h80b G hnonab z hz hext w hcard Mbar hMbar
  rcases hT G hnonab z hz hext' w hcard' Mbar hMbar' with
    h | h | ⟨-, hev, q, hq, hqM⟩ | ⟨h6, -⟩ | ⟨h10, -, hFS⟩ | ⟨h11, hCo2⟩ | ⟨h12, hCo1⟩ |
      ⟨hsimp, t, ht, htext, hcases⟩
  · omega
  · rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact gf2TypeList_of_psl (by omega) (lieModel_psl_two_of_mulEquiv (by omega) e)
    · exact gf2TypeList_of_psu (by omega) (lieModel_psu_two_of_mulEquiv (by omega) e)
  · have h3 := h80a G hnonab z hz hext w hcard (by omega) hev Mbar hMbar q hq hqM
    by_cases hp : timmesfeldPlusType q
    · exact gf2TypeList_of_omegaPlus (by omega) (h3.1 hp)
    · exact gf2TypeList_of_omegaMinus (by omega) (h3.2 hp)
  · exact gf2TypeList_of_width_six_at hz hext hcard h79 h6
  · rw [← generalizedFitting_eq_timmesfeldFStar] at hFS
    rcases hFS with hL | hU
    · exact gf2TypeList_of_exceptional (s := .E6) (by simp) (h80.2.1 h10 hL)
    · exact gf2TypeList_of_exceptional (s := .twistedE6) (by simp) (h80.1 h10 hU)
  · exact gf2TypeList_of_sporadic (s := .B) (by simp)
      (((h79 z hz hext w hcard).2.2.2 Mbar hMbar).1 h11 hCo2)
  · exact gf2TypeList_of_sporadic (s := .M) (by simp)
      (((h79 z hz hext w hcard).2.2.2 Mbar hMbar).2 h12 hCo1)
  · rw [← generalizedFitting_eq_timmesfeldFStar] at htext hcases
    rw [timmesfeldIsExtraspecial_iff] at htext
    rcases hcases with ⟨h16, hc, hqu⟩ | ⟨h28, hc, hqu⟩
    · exact gf2TypeList_of_exceptional (s := .E7) (by simp)
        (h80.2.2.1 h16 hsimp ⟨t, ht, htext, hc, hqu⟩)
    · exact gf2TypeList_of_exceptional (s := .E8) (by simp)
        (h80.2.2.2 h28 hsimp ⟨t, ht, htext, hc, hqu⟩)

end CasesAt

theorem gf2TypeList_of_inputs_at (h76 : Aschbacher1976Statement)
    (h77 : Aschbacher1977WidthAtMostTwoStatement) (h80a : Smith1980OrthogonalStatement)
    (h80b : Smith1980TypeEStatement) (hT : MainStatement) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (h79 : Smith1979Conclusion G) {z : G}
    (hz : orderOf z = 2)
    (hsymp : GLASymplecticType
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)))) :
    GF2TypeList G := by
  rcases h76 G hnonab z hz hsymp with
    ⟨p, f, m, hp, hp2, hf, hm, hq, hmodel⟩ | h | hHS | ⟨hext, w, hw, hcard⟩
  · exact gf2TypeList_of_psl_two hp hp2 hf hm hq hmodel
  · rcases h with h | h | h
    · exact gf2TypeList_of_sporadic (s := .M11) (by simp) h
    · exact gf2TypeList_of_three (s := .PSL) (n := 3) (by simp) h
    · exact gf2TypeList_of_three (s := .PSU) (n := 3) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .HS) (by simp) hHS
  · by_cases h2 : w = 2
    · exact gf2TypeList_of_width_two hnonab hz hext hcard h77 h2
    · by_cases h34 : w = 3 ∨ w = 4
      · exact gf2TypeList_of_width_three_four_at hz hext hcard h79 h34
      · exact gf2TypeList_of_wide_at hz hext hcard hnonab h79 h80a h80b hT (by omega)

theorem gf2TypeList_of_inputs_charTwoKP (h76 : Aschbacher1976Statement)
    (h77 : Aschbacher1977WidthAtMostTwoStatement) (h79 : Smith1979StatementCharTwoKP)
    (h80a : Smith1980OrthogonalStatement) (h80b : Smith1980TypeEStatement)
    (hT : MainStatement) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharTwoType G)
    (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) {z : G} (hz : orderOf z = 2)
    (hsymp : GLASymplecticType
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)))) :
    GF2TypeList G :=
  gf2TypeList_of_inputs_at h76 h77 h80a h80b hT hnonab
    (smith1979Conclusion_of_charTwoKP h79 hnonab hchar hKP) hz hsymp

end CFSG.GF2Type
