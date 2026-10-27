module

public import CFSG.GF2Type.Smith1980Orth.Setup
public import CFSG.LargeExtraspecial.S14Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14 CFSG.GF2Type.Smith1980Orth

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem noA2All_of_not_isReducible [IsSimpleGroup G] (I : TimInputs) (hw : 5 ≤ S.width)
    (hirr : ¬ S.IsReducible) : S11.NoA2All S := by
  intro g haQ hne hA
  obtain ⟨α, hαL, -, hαA⟩ := hA
  have ht : S.ρ α ∈ S.Lbar g := by
    rw [← S.map_La_eq_Lbar g]
    exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
  rcases Setting.timmesfeld_12_16_of_insp5 I.hRI I.hARS I.hTri I.hFischer I.hInsp I.h36 I.hSL
      haQ hne hw ht hαA with hred | ⟨h4, -⟩ | hR | ⟨h4, -⟩
  · exact hirr hred
  · omega
  · exact Setting.not_s12GammaLResidual haQ hne hw hR
  · omega

theorem sixStage [IsSimpleGroup G] (I : TimInputs) (hw : S.width = 6)
    (hex : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (hirr : ¬ S.IsReducible) :
    S11.NoA2All S ∧ ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ Hyp4 S g ∧
      Cons311 S g ∧ ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g := by
  have hnoAll := noA2All_of_not_isReducible I (by omega) hirr
  obtain ⟨g, haQ, hne⟩ := hex
  have hno := hnoAll g haQ hne
  have H := hyp4_of I.hTI (by omega) haQ hne hno hirr
  have C := cons311_of I.hTI (by omega) haQ hne hno hirr
  exact ⟨hnoAll, g, haQ, hne, H, C,
    claim_14_3 I.hF2 I.hBen I.hTI H C (noA2_of hno) hirr (by omega)⟩

theorem classify_six [IsSimpleGroup G] (I : TimInputs) (hw : S.width = 6) (hirr : ¬ S.IsReducible)
    (hnoAll : S11.NoA2All S) {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    Rbar S g t = S.Lbar g ∨
      (LinCase S g ht ∧ (finrank (ZMod 2) (Vt S g t) = 2 ∨ finrank (ZMod 2) (Vt S g t) = 3)) ∨
      S10.Hyp10 S g t ∨
      ∃ hVQ : ¬ V S g t ≤ S.Qa g, OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 6 ∧
        Nbar S g t = zpowers t := by
  have hNo : NoA2 S g := noA2_of (hnoAll g H.conj_mem H.conj_ne)
  have hStage : ∀ t' (hSt : Stage S g t'), Hyp89 S g t' → False := by
    intro t' hSt h89
    obtain ⟨c, hocc, -⟩ := exists_config I.hCorB I.hFacts I.hCE I.h83 I.hRes I.h9 hSt h89
    have h6 : (6 : ℕ) = c.width := hw ▸ hocc.2.1
    cases c <;> simp [Config.width] at h6
  by_cases hR : Rbar S g t = S.Lbar g
  · exact Or.inl hR
  rcases timmesfeld_4_5 H hNo C ht ht1 with h | hL | ⟨hVQ, hcase⟩
  · exact absurd h hR
  ·
    refine Or.inr (Or.inl ⟨hL, ?_⟩)
    have hm := hL.two_le_finrank
    have hT := Submodule.finrank_mono (S6.Vt_le_Tt H hNo ht1 hL)
    have hU := S7.finrank_commSpace_eq H ht ht1
    have htt : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
      congrArg Subtype.val (mul_self_of_mem_Lbar S H.conj_mem ht)
    have h2 := two_mul_finrank_commSpace_le htt
    have hQ := S.finrank_Qt_eq_two_mul_width
    omega
  ·
    by_cases hLN : S.Lbar g ⊓ Nbar S g t = zpowers t
    ·
      rcases hcase with hSp | hA | hΩ | hP
      · exact absurd hLN (S6.timmesfeld_6_4 I.hCE H hNo C ht ht1 hVQ hSp).ne'
      · have := width_le_four_of_tau_not_mem H C ht ht1 hVQ hA.finrank_eq hA.tau_not_mem hLN
        omega
      · have hN := Nbar_eq_zpowers_of_N0bar H ht
          (S6.Nbar_eq_N0bar_of_omegaCase I.hCE H hNo C ht ht1 hVQ hΩ) hLN
        have hd := S7.width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
        exact Or.inr (Or.inr (Or.inr ⟨hVQ, hΩ, by omega, hN⟩))
      · have := width_le_four_of_tau_not_mem H C ht ht1 hVQ hP.finrank_eq hP.tau_not_mem hLN
        omega
    ·
      have hSt : Stage S g t := ⟨by omega, H, hnoAll, C, hirr, ht, ht1, hR, hLN⟩
      rcases hcase with hSp | hA6 | hΩ | hP
      · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inr (Or.inl hSp)⟩).elim
      · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inr (Or.inr (Or.inl hA6))⟩).elim
      · by_cases h4p : finrank (ZMod 2) (Vt S g t) = 4 ∧ RNPlus S g t
        · obtain ⟨h4, ht', W, hW, hWs⟩ := h4p
          exact Or.inr (Or.inr (Or.inl ⟨H, hNo, C, ht, ht1, hR, hLN, hVQ, hΩ, h4, W, by omega,
            hWs⟩))
        · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inl ⟨hΩ, h4p⟩⟩).elim
      · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inr (Or.inr (Or.inr hP))⟩).elim

end CFSG.GF2Type.Smith1979
