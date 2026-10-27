module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Bridge
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Core

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

theorem pslNoOffender_holds :
    FFO.PSLNoOffender := by
  intro m f r hm hr hr2 hrmq
  have hrm : r ∣ m := hrmq.trans (Nat.gcd_dvd_left m (2 ^ f - 1))
  have hrq : r ∣ 2 ^ f - 1 := hrmq.trans (Nat.gcd_dvd_right m (2 ^ f - 1))
  by_cases hf0 : f = 0
  · subst f
    intro V _ _ _ L E _ _ _ hmodel _ _ _ _
    exfalso
    obtain ⟨-, K, _iK, _iKfin, hKcard, -⟩ := hmodel
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h2 : Nat.card K = 1 := by simpa using hKcard
    omega
  · have hf : 1 ≤ f := Nat.pos_of_ne_zero hf0
    have hmne4 : m ≠ 4 := by
      rintro rfl
      have hrm4 : r ∣ 2 ^ 2 := by simpa using hrm
      have hr2' : r = 2 :=
        (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrm4)
      exact hr2 hr2'
    have hm5 : 5 ≤ m := by omega
    exact FFO.PSL.pslNoOffenderAt_of_linear (m := m) (f := f) (r := r) (by omega) hf hr
      (FFO.PSL.psl_linear_core hm5 hr hr2 hrm hrq)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
