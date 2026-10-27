module

public import CFSG.GF2Type.Smith1980Orth.Setup
public import CFSG.LargeExtraspecial.S10EightV
public import CFSG.LargeExtraspecial.S13EightF
public import CFSG.LargeExtraspecial.S13EntryD
public import CFSG.LargeExtraspecial.S14Five
public import CFSG.LargeExtraspecial.S14Six
public import CFSG.LargeExtraspecial.S14W4LocDefs
public import CFSG.LargeExtraspecial.S9RCMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S14 CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

structure GoodPre (S : Setting G) (g : G) (t : S.O) : Prop where
  H : Hyp4 S g
  hNo : NoA2 S g
  C : Cons311 S g
  ht : t ∈ S.Lbar g
  ht1 : t ≠ 1
  hR : Rbar S g t ≠ S.Lbar g
  hVQ : ¬ V S g t ≤ S.Qa g
  hN : Nbar S g t = zpowers t
  irr : ¬ S.IsReducible
  noAll : S11.NoA2All S

structure GoodT (S : Setting G) (g : G) (t : S.O) : Prop extends GoodPre S g t where
  hΩ : OmegaCase H C ht ht1 hVQ

theorem exists_goodT [IsSimpleGroup G]
    (I : TimInputs) (O : OrthData S) (hw : 8 ≤ S.width)
    (hns : ¬ IsSimpleGroup (Mbar0 S)) : ∃ g t, GoodT S g t := by
  obtain ⟨g, haQ, hne⟩ := O.exists_conj_mem_Q I.hAS (by omega)
  have hirr := O.not_isReducible I.hDW (by omega) haQ hne
  have hnoAll := O.noA2All I (by omega)
  have hno := hnoAll g haQ hne
  have H := hyp4_of I.hTI (by omega) haQ hne hno hirr
  have C := cons311_of I.hTI (by omega) haQ hne hno hirr
  have hNo : NoA2 S g := noA2_of hno
  have hex := claim_14_3 I.hF2 I.hBen I.hTI H C hNo hirr (by omega)
  have hStage : ∀ t, Stage S g t → Hyp89 S g t → False := by
    intro t hSt h89
    obtain ⟨c, hocc, hext⟩ := exists_config I.hCorB I.hFacts I.hCE I.h83 I.hRes I.h9 hSt h89
    exact hns (claim_14_6 I.hCE hSt hocc hext)
  by_cases hlin : ∀ (t : S.O) (ht : t ∈ S.Lbar g), t ≠ 1 →
      Rbar S g t = S.Lbar g ∨ LinCase S g ht
  · exfalso
    have hy : S11.Hyp S g := ⟨H, C, hnoAll, fun {t} ht ht1 => hlin t ht ht1⟩
    obtain ⟨hw6, -⟩ := S11.timmesfeld_11_9 hy (I.h111 G S g hy hirr (by omega) hex) I.hCE
      (by omega) (I.h118 G S)
    omega
  push Not at hlin
  obtain ⟨t, ht, ht1, hR, hL⟩ := hlin
  have hVQ : ¬ V S g t ≤ S.Qa g := by
    intro hVQ
    rcases timmesfeld_4_5 H hNo C ht ht1 with h | h | ⟨h, -⟩
    · exact hR h
    · exact hL h
    · exact h hVQ
  by_cases hLN : S.Lbar g ⊓ Nbar S g t = zpowers t
  · rcases timmesfeld_4_5_of_not_le H hNo C ht ht1 hVQ with hSp | hA | hΩ | hP
    · exact absurd hLN (S6.timmesfeld_6_4 I.hCE H hNo C ht ht1 hVQ hSp).ne'
    · have := width_le_four_of_tau_not_mem H C ht ht1 hVQ hA.finrank_eq hA.tau_not_mem hLN
      omega
    · exact ⟨g, t, ⟨H, hNo, C, ht, ht1, hR, hVQ, Nbar_eq_zpowers_of_N0bar H ht
        (S6.Nbar_eq_N0bar_of_omegaCase I.hCE H hNo C ht ht1 hVQ hΩ) hLN, hirr, hnoAll⟩, hΩ⟩
    · have := width_le_four_of_tau_not_mem H C ht ht1 hVQ hP.finrank_eq hP.tau_not_mem hLN
      omega
  have hSt : Stage S g t := ⟨by omega, H, hnoAll, C, hirr, ht, ht1, hR, hLN⟩
  rcases timmesfeld_4_5_of_not_le H hNo C ht ht1 hVQ with hSp | hA6 | hΩ | hP
  · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inr (Or.inl hSp)⟩).elim
  · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inr (Or.inr (Or.inl hA6))⟩).elim
  · by_cases h4p : finrank (ZMod 2) (Vt S g t) = 4 ∧ RNPlus S g t
    ·
      obtain ⟨h4, hp⟩ := h4p
      obtain ⟨ht', W, hW, hWs⟩ := hp
      have X : S10.Hyp10 S g t := ⟨H, hNo, C, ht, ht1, hR, hLN, hVQ, hΩ, h4, W, by omega, hWs⟩
      have h7 : 7 ≤ S.width := by omega
      obtain ⟨P, hPM, hP1, hP3, hPn⟩ :=
        S10.timmesfeld_10_8_o3 I.hCE (S10.noPGL25 S g) hnoAll X h7
      have Y := S13.hyp13_of hPM hP1 hP3 hPn X h7 hirr I.hCE hnoAll (S10.noPGL25 S g)
      by_cases hii : ∀ τ (hτ : τ ∈ S.Lbar g), τ ∉ S13.Ebar S g P →
          Rbar S g τ = S.Lbar g ∨ LinCase S g hτ
      · exact (S13.Hyp13.timmesfeld_13_8 I.hCE Y hii).elim
      push Not at hii
      obtain ⟨τ, hτ, hτE, hRτ, hLτ⟩ := hii
      have hτ1 : τ ≠ 1 := fun h => hτE (h ▸ one_mem _)
      rcases timmesfeld_4_5 Y.H Y.hNo Y.C hτ hτ1 with hRL | hLin | ⟨hVQτ, hcase⟩
      · exact absurd hRL hRτ
      · exact absurd hLin hLτ
      have hdim := Y.finrank_Vt_of_not_mem hτ hτE hτ1 hVQτ
      have h2 := card_Lbar_eq_mul Y.haQ hτ (t := τ)
      rw [Y.C.card_Lbar] at h2
      have hτA : τ ∈ S.Lbar g ⊓ Nbar S g τ := ⟨hτ, S6.self_mem_Nbar Y.H hτ⟩
      have hτ2 : Nat.card (zpowers τ) = 2 := S7.card_zpowers_eq_two Y.H hτ hτ1
      rcases hcase with hSp | hA | hΩτ | hP
      · exfalso
        have hc := card_Lbar_inf_Nbar_sp Y.H Y.C hτ hτ1 hVQτ hSp
        rw [hdim, Nat.sub_self, pow_zero] at hc
        have hb := Subgroup.eq_bot_of_card_eq _ hc
        have hm : τ ∈ (⊥ : Subgroup S.O) := hb ▸ hτA
        exact hτ1 ((mem_bot).mp hm)
      · rw [hA.finrank_eq] at hdim
        omega
      · have hc := S7.card_LmodN_of_omegaCase Y.H Y.C hτ hτ1 hΩτ
        rw [hdim] at hc
        rw [hc] at h2
        have hLNτ : S.Lbar g ⊓ Nbar S g τ = zpowers τ := by
          symm
          refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hτA) ?_
          rw [hτ2]
          have e : 2 ^ (S.width - 1) = 2 ^ (S.width - 2) * 2 := by
            rw [← pow_succ]
            congr 1
            omega
          have hpos : 0 < 2 ^ (S.width - 2) := by positivity
          rw [e] at h2
          have := Nat.eq_of_mul_eq_mul_left hpos h2
          omega
        exact ⟨g, τ, ⟨Y.H, Y.hNo, Y.C, hτ, hτ1, hRτ, hVQτ, S13.Nbar_eq_zpowers_of_N0bar' Y.H hτ
          (S6.Nbar_eq_N0bar_of_omegaCase I.hCE Y.H Y.hNo Y.C hτ hτ1 hVQτ hΩτ) hLNτ, hirr, hnoAll⟩,
          hΩτ⟩
      · rw [hP.finrank_eq] at hdim
        omega
    · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inl ⟨hΩ, h4p⟩⟩).elim
  · exact (hStage t hSt ⟨H, C, ht, ht1, hVQ, Or.inr (Or.inr (Or.inr hP))⟩).elim

end CFSG.GF2Type.Smith1980Orth
