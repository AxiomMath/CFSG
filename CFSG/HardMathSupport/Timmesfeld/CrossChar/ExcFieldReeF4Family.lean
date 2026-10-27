module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem three_dvd_reeF4_pow_four_sub_one (m : ℕ) : 3 ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 := by
  have h : (2 ^ (2 * m + 1)) ^ 4 = 16 ^ (2 * m + 1) := by
    rw [pow_right_comm]
    norm_num
  rw [h]
  have h2 := Nat.sub_dvd_pow_sub_pow 16 1 (2 * m + 1)
  rw [one_pow] at h2
  exact (by norm_num : 3 ∣ 16 - 1).trans h2

theorem crossCharFamAt_reeF4_dvd : CrossCharFamAt .reeF4 fun idx p =>
    ∃ m : ℕ, idx.1 = .reeF4 m ∧ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 := by
  rintro ⟨d, hv⟩ _ p hp hp2 - ⟨m, hd, hdvd⟩
  change d = _ at hd
  subst hd
  obtain ⟨X, _, _, _, hm1, hX, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have : Finite (Cat ⟨.reeF4 m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hp35 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact Or.inl h
    · exact absurd (h ▸ hp) (by norm_num)
    · exact Or.inr h
  have hr : RankLE2 p (F4.reeGamma X m) := by
    rcases hp35 with rfl | hp5
    · exact RankLE2.of_mulEquiv e (rankLE2_three_cat_reeF4 hv)
    · exact RankLE2.of_mulEquiv e (rankLE2_of_noPowThree hp fun _ hE hc =>
        CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five (reeTitsModel_cat_reeF4 hv) hp
          hp5 hE hc)
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_reeGamma_of_dvd hm1 hX hp hp2 hdvd hr)

theorem crossCharFamAt_reeF4_field : CrossCharFamAt .reeF4 fun idx p =>
    ∃ m : ℕ, idx.1 = .reeF4 m ∧ 5 ≤ p ∧ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 ∧ p ∣ 2 * m + 1 :=
  CrossCharFamAt.mono (fun _ _ ⟨m, hm, _, hd, _⟩ => ⟨m, hm, hd⟩) crossCharFamAt_reeF4_dvd

theorem crossCharFamAt_reeF4_three_field : CrossCharFamAt .reeF4 fun idx p =>
    ∃ m : ℕ, idx.1 = .reeF4 m ∧ p = 3 ∧ 3 ∣ 2 * m + 1 :=
  CrossCharFamAt.mono (fun _ _ ⟨m, hm, hp, _⟩ => ⟨m, hm, hp ▸ three_dvd_reeF4_pow_four_sub_one m⟩)
    crossCharFamAt_reeF4_dvd

theorem crossCharFamAt_reeF4_open :
    CrossCharFamAt .reeF4 fun idx p => ¬ regimeReeF4Vac idx p :=
  crossCharFamAt_reeF4_open_of crossCharFamAt_reeF4_field crossCharFamAt_reeF4_three_field

end CFSG.HardMathSupport.Timmesfeld.CrossChar
