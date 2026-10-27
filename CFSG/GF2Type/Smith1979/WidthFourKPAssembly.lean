module

public import CFSG.GF2Type.Smith1979.WidthFourKP
public import CFSG.GF2Type.Smith1979.WidthFourKPLeaves
public import CFSG.GF2Type.Smith1979.W4AsMain
public import CFSG.GF2Type.Smith1979.W4BetaTri
public import CFSG.GF2Type.Smith1979.W4AsOmega83
public import CFSG.GF2Type.AschbacherFSmith1977Holds
public import CFSG.Holt.General.NoRelevantBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.DW CFSG.Yardstones.M3aba7dc4b8a8

theorem smith1979WidthFourCharTwoKP_of_leaves
    (hR : CFSG.LargeExtraspecial.DW.DW37WidthFourStatement)
    (hD4 : WidthFourTrialityCase) (hTh : ParrottThKP) (hΩ : WidthFourOmegaCase) :
    Smith1979WidthFourCharTwoKP := by
  intro G _ _ _ hnonab hchar hK z hz hext hcard
  have hcard' : Nat.card (coreQ z) = 2 ^ (1 + 2 * 4) := by rw [hcard]
  by_cases hwc : ZWeaklyClosedInCore z
  · rcases aschbacherFSmith1977Statement_holds G hnonab z hz hext 4 hcard' (by norm_num) hwc with
      hU | ⟨-, hCo2⟩
    · have hU' : LieModel G .PSU 6 2 1 := by simpa using hU
      simp [Smith1979WidthFourList, hU']
    · simp [Smith1979WidthFourList, hCo2]
  · let S : Setting G := setting hz hext hcard'
    have hS4 : S.width = 4 := setting_width hz hext hcard'
    have hQ : S.QG = coreQ z := setting_QG hz hext hcard'
    have hzS : S.z = z := setting_z hz hext hcard'
    obtain ⟨g₀, hg₀Q, hg₀ne⟩ :=
      DW.W4Rank.exists_conj_of_not_weaklyClosed S hzS hQ hwc
    by_cases hred : CoreReducible z
    · obtain ⟨A, hlo, hhi, hnorm⟩ := hred
      have hRed : S.IsReducible :=
        DW.W4Rank.isReducible_of_lt S (by rw [hQ]; exact hlo) (by rw [hQ]; exact hhi) hnorm
      obtain ⟨e⟩ := hR G S g₀ hS4 hg₀Q hg₀ne hRed
      have hpsl : LieModel G .PSL 6 2 1 := by
        have h := lieModel_psl_two_of_mulEquiv (n := S.width + 2) (by omega) e
        simpa [hS4] using h
      exact Or.inl hpsl
    · have hirr : ¬ S.IsReducible := fun h =>
        hred (coreReducible_of_isReducible S hzS hQ h)
      by_cases hα : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g
      · obtain ⟨g, haQ, hne, hA⟩ := hα
        have hCo1 := W4As.isSporadic_co1_of_hasTypeAInL hnonab hS4 hirr haQ hne hA
        simp [Smith1979WidthFourList, hCo1]
      · have hno : S11.NoA2All S := fun g h1 h2 hA => hα ⟨g, h1, h2, hA⟩
        obtain ⟨H, C⟩ :=
          W4O83.hyp4_cons311_of_w4 Smith1980Orth.timInputs_holds.hTI hS4 hno hirr g₀ hg₀Q hg₀ne
        haveI : (generalizedFitting (Subgroup.centralizer ({z} : Set G))).Normal :=
          CFSG.Holt.General.NoRelevant.generalizedFitting_normal
        let Mbar := Subgroup.centralizer ({z} : Set G) ⧸
          generalizedFitting (Subgroup.centralizer ({z} : Set G))
        have hMbar : timmesfeldQuotientIso
            (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar :=
          ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
        have hMbar' : timmesfeldQuotientIso
            (timmesfeldFStar (Subgroup.centralizer ({S.z} : Set G))) Mbar := by
          rw [← Bridge.generalizedFitting_eq_timmesfeldFStar]
          exact hMbar
        obtain ⟨e⟩ := Bridge.nonempty_mulEquiv_Mbar_ofFStar hz
          (timmesfeld_hypotheses hext hcard').1 hMbar'
        rcases W4As.beta_trichotomy hS4 hno hirr H C with
          h8 | hA9 | ⟨t, ht, ht1, hVQ, hΩc, hdim⟩
        · have hD := hD4 G hnonab hchar hK S hS4 hno hirr g₀ H C h8
          simp [Smith1979WidthFourList, hD]
        · obtain ⟨f⟩ := hA9
          have hTh' := hTh G hnonab hchar hK z hz hext hcard hwc Mbar hMbar ⟨e.symm.trans f⟩
          simp [Smith1979WidthFourList, hTh']
        · rcases hΩ G hnonab hchar hK S hS4 hno hirr g₀ H C t ht ht1 hVQ hΩc hdim with
            ⟨q, hq, hiso⟩ | hHN | ⟨E, hEM, hel, hE⟩
          · have hiso' : Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
                Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q) := by
              rcases hiso with hA | hB
              · obtain ⟨f⟩ := hA
                exact Or.inl ⟨e.symm.trans f⟩
              · obtain ⟨f⟩ := hB
                exact Or.inr ⟨e.symm.trans f⟩
            have h := Smith1980Orth.smith1980Orthogonal_holds G hnonab z hz hext 4 hcard'
              (by norm_num) (by decide) Mbar hMbar q hq hiso'
            by_cases hp : timmesfeldPlusType q
            · have hplus : LieModel G .POmegaPlus 4 2 1 := by simpa using h.1 hp
              simp [Smith1979WidthFourList, hplus]
            · have hminus : LieModel G .POmegaMinus 4 2 1 := by simpa using h.2 hp
              simp [Smith1979WidthFourList, hminus]
          · simp [Smith1979WidthFourList, hHN]
          · obtain ⟨C83⟩ := W4As.exists_omega83Config hS4 hno
              Smith1980Orth.timInputs_holds.hTI hirr ⟨g₀, hg₀Q, hg₀ne⟩ hEM hel hE
            exact (W4O83.Omega83Config.false_of_base C83 hchar
              (fun g' h1 h2 => W4O83.hyp4_cons311_of_w4 Smith1980Orth.timInputs_holds.hTI
                hS4 hno hirr g' h1 h2) hS4 hg₀Q hg₀ne).elim

end CFSG.GF2Type.Smith1979
