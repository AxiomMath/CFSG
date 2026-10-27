module

public import CFSG.Certificates.Kernel.M3BFib.CompSound

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open Timmesfeld.M3B (WT B0 LA Da Db adOne adQ adPow adOf)

noncomputable instance (r : ℕ) : Decidable (GoodRow r) := inferInstanceAs (Decidable (enc (dig3 r) = r))

theorem lpM_ok : LpOK (toMat (B0 ())) LpM := by
  unfold LpOK
  decide +kernel

theorem one_sound : GoodPD oneK ∧ dK oneK = toD adOne := by
  unfold GoodPD
  decide +kernel

theorem a_sound : GoodPD DaK ∧ dK DaK = toD (Da ()) := by
  unfold GoodPD
  decide +kernel

theorem b_sound : GoodPD DbK ∧ dK DbK = toD (Db ()) := by
  unfold GoodPD
  decide +kernel

theorem q_sound : ∀ j : Fin 12, GoodPD (qK j) ∧ dK (qK j) = toD (adQ (B0 ()) j) := by
  unfold GoodPD
  decide +kernel

theorem comp_sound {D D' : PD} {E E' : Timmesfeld.M3B.AD} (h : GoodPD D ∧ dK D = toD E)
    (h' : GoodPD D' ∧ dK D' = toD E') :
    GoodPD (compK LpM D D') ∧ dK (compK LpM D D') = toD (Timmesfeld.M3B.comp (B0 ()) E E') := by
  obtain ⟨g, e⟩ := compK_sound lpM_ok h.1 h'.1
  exact ⟨g, by rw [e, toD_comp, h.2, h'.2]⟩

theorem pow_sound {D : PD} {E : Timmesfeld.M3B.AD} (h : GoodPD D ∧ dK D = toD E) :
    ∀ k : ℕ, GoodPD (powK LpM D k) ∧ dK (powK LpM D k) = toD (adPow (B0 ()) E k)
  | 0 => one_sound
  | k + 1 => comp_sound (pow_sound h k) h

theorem LA_getD_two : (LA ()).getD 2 adOne = adPow (B0 ()) (Da ()) 55 := rfl
theorem LA_getD_three : (LA ()).getD 3 adOne = adPow (B0 ()) (Db ()) 21 := rfl
theorem LA_getD_q (j : Fin 12) : (LA ()).getD (4 + j) adOne = adQ (B0 ()) j := by
  fin_cases j <;> rfl
theorem LA_size : (LA ()).size = 16 := rfl

theorem letter_sound (i : ℕ) :
    GoodPD (LK.getD i oneK) ∧ dK (LK.getD i oneK) = toD ((LA ()).getD i adOne) := by
  rcases lt_or_ge i 16 with h | h
  · rcases lt_or_ge i 4 with h4 | h4
    · interval_cases i
      · exact a_sound
      · exact b_sound
      · rw [LA_getD_two]
        exact pow_sound a_sound 55
      · rw [LA_getD_three]
        exact pow_sound b_sound 21
    · obtain ⟨j, rfl⟩ : ∃ j : Fin 12, i = 4 + j := ⟨⟨i - 4, by omega⟩, by simp; omega⟩
      rw [LA_getD_q]
      have e : LK.getD (4 + j) oneK = qK j := by fin_cases j <;> rfl
      rw [e]
      exact q_sound j
  · rw [List.getD_eq_default _ _ (by simp [LK]; omega), Array.getD, dif_neg (by rw [LA_size]; omega)]
    exact one_sound

theorem adOfK_sound : ∀ t : WT,
    GoodPD (adOfK LpM LK t) ∧ dK (adOfK LpM LK t) = toD (adOf (B0 ()) (LA ()) t)
  | .gen i => letter_sound i
  | .mul a b => comp_sound (adOfK_sound a) (adOfK_sound b)
  | .pow t k => pow_sound (adOfK_sound t) k

end CFSG.KC.M3BF

end
