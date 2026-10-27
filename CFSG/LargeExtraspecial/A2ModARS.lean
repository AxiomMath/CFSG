module

public import CFSG.Timmesfeld.ARS.CaseBMain
public import CFSG.Timmesfeld.ARS.CaseEMain
public import CFSG.Timmesfeld.ARS.CaseHFinal
public import CFSG.Timmesfeld.ARS.CaseMLeviOf
public import CFSG.Timmesfeld.ARS.CaseOADegSU
public import CFSG.Timmesfeld.ARS.CaseOAExcl
public import CFSG.Timmesfeld.ARS.CaseOANSLStar
public import CFSG.Timmesfeld.ARS.ExclNSMain
public import CFSG.Timmesfeld.ARS.InductionCases
public import CFSG.Timmesfeld.ARS.Sec8HypDegenInput

public section

namespace CFSG.LargeExtraspecial.A2Mod

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.LieType CFSG.Blueprint

@[expose] def OutputPlus (G : Type) [Group G] (R : Set (Subgroup G)) : Prop :=
  (∃ m, 2 ≤ m ∧ HasGenConfig R (edgeA m)) ∨ (∃ m, 4 ≤ m ∧ HasGenConfig R (edgeD m)) ∨
    HasGenConfig R (edgeE 6) ∨ HasGenConfig R (edgeE 7) ∨ HasGenConfig R (edgeE 8) ∨
    (NonSimplyLacedOutcome G ∧ NSLFrame G R) ∨
    ∃ A ∈ R,
      (∃ f, 1 ≤ f ∧ Nat.card A = 2 ^ f ∧ TwistedD4Frame G f ∧ LieModel G .trialityD4 0 2 f) ∨
      (∃ f, 2 ≤ f ∧ Nat.card A = 2 ^ f ∧ G2Frame G f ∧ LieModel G .G2 0 2 f) ∨
      (Nat.card A = 2 ∧ LieModel G .PSU 3 3 1)

theorem arsOutputPlus {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R) :
    OutputPlus G R := by
  have := h.finite
  have hs : InductionStep := inductionStep_of_cases caseLStep
    (caseHStep_of_frameInput caseHFrameInput) caseBStep
    (caseMaxStep_of_inputs degenerate813Input
      (caseOAStep_of_inputs₄ oaNonSimplyLacedInput oaDegenerateInput)
      (caseMStep_of_frame (Transvection.subgroupTransvectionStatementFrame_of
        (Transvection.transvectionStatementFrame_of_large
          Transvection.transvectionStatementFrameLarge)))
      (caseEStep_of ExclNS.caseENonSimplyLacedInput))
  obtain ⟨A, hA, -⟩ := h.nondeg
  by_cases hmax : IsCoatom (Subgroup.normalizer (A : Set G))
  · by_cases hσ : sigmaSet R A = lambdaSet R A
    · have hH : SigmaEqLambda R := sigmaEqLambda_of_mem h.root hA hσ
      have h3 := CaseH.three_le_ncard_linesThrough h hH hA hmax
      by_cases h23 : Nat.card A = 2 ∧ (linesThrough R A).ncard = 3
      · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨A, hA, .inr (.inr
          ⟨h23.1, lieModel_PSU_of_caseH h hH hA h23.1 h23.2⟩)⟩)))))
      · have hT := CaseH.mTransitive_of_not_two_three h hH hA h3 h23
        rcases caseHFrameInput G R h hH hT A hA h3 h23 with ⟨f, hf, hAf, hG⟩ | ⟨f, hf, hAf, hG⟩
        · have hmodel : LieModel G .G2 0 2 f := by
            obtain ⟨F, _, _, hF, φ, hc, hgen, hnt⟩ := hG
            have hq : 3 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
            obtain ⟨-, -, -, -, hm⟩ :=
              exists_lieModel_of_coneCompatible_G2 Nat.prime_two (by omega) hq hF h.center hc hgen
                hnt
            exact hm
          exact .inr (.inr (.inr (.inr (.inr (.inr ⟨A, hA, .inr (.inl ⟨f, hf, hAf, hG,
            hmodel⟩)⟩)))))
        · have hmodel : LieModel G .trialityD4 0 2 f := by
            obtain ⟨F, _, _, hF, σ, hσ', φ, hc, hgen, hnt⟩ := hG
            obtain ⟨-, -, -, -, hm⟩ := exists_lieModel_of_coneCompatible_twistedD4 Nat.prime_two
              hf hF σ hσ' h.center hc hgen hnt
            exact hm
          exact .inr (.inr (.inr (.inr (.inr (.inr ⟨A, hA, .inl ⟨f, hf, hAf, hG, hmodel⟩⟩)))))
    · rcases output_of_step hs G R h with c | c | c | c | c | ⟨hns, hd | hF⟩
      · exact .inl c
      · exact .inr (.inl c)
      · exact .inr (.inr (.inl c))
      · exact .inr (.inr (.inr (.inl c)))
      · exact .inr (.inr (.inr (.inr (.inl c))))
      · exact absurd (hd A hA) hσ
      · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hns, hF⟩)))))
  · obtain ⟨Δ, hΔ, hAΔ⟩ := (exists_isTI_iff h hA).1 hmax
    have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
      fun _ hA _ hB e => eq_of_omegaSet_eq h hA hB e
    obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow h.root h.noIsolated h.nondeg hΩ hΔ.isWeakTI hAΔ
    obtain ⟨hm2, X, hX⟩ := Linear.exists_isRootFrame h.root h.noIsolated h.nondeg hΩ hΔ hAΔ hm
    exact .inl ⟨m, hm2, _, _, hX.isConfig, hX.iSup_adj_eq_top⟩

theorem arsOutputPlus_of_card_eq_two {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    (h2 : ∀ A ∈ R, Nat.card A = 2) :
    (∃ m, 2 ≤ m ∧ HasGenConfig R (edgeA m)) ∨ (∃ m, 4 ≤ m ∧ HasGenConfig R (edgeD m)) ∨
      HasGenConfig R (edgeE 6) ∨ HasGenConfig R (edgeE 7) ∨ HasGenConfig R (edgeE 8) ∨
      (NonSimplyLacedOutcome G ∧ NSLFrame G R) ∨
      (TwistedD4Frame G 1 ∧ LieModel G .trialityD4 0 2 1) ∨ LieModel G .PSU 3 3 1 := by
  rcases arsOutputPlus h with c | c | c | c | c | c |
      ⟨A, hA, ⟨f, hf, hAf, hG, hm⟩ | ⟨f, hf, hAf, -, -⟩ | ⟨-, hm⟩⟩
  · exact .inl c
  · exact .inr (.inl c)
  · exact .inr (.inr (.inl c))
  · exact .inr (.inr (.inr (.inl c)))
  · exact .inr (.inr (.inr (.inr (.inl c))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl c)))))
  · obtain rfl : f = 1 := Nat.pow_right_injective le_rfl
      (show 2 ^ f = 2 ^ 1 by rw [← hAf, h2 A hA, pow_one])
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hG, hm⟩))))))
  · have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    rw [← hAf, h2 A hA] at this
    norm_num at this
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr hm))))))

end CFSG.LargeExtraspecial.A2Mod
