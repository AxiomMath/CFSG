module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Lie
public import CFSG.GH74.KGroups.L33
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

private theorem exists_A2_of_lieL3 {t : TauCeti.LieTypeIndex} (h : LieL3 t) :
    ∃ q : TauCeti.PrimePower, t = .A 2 q := by
  cases t with
  | A r q =>
    by_cases hr : r = 2
    · subst hr
      exact ⟨q, rfl⟩
    · exact absurd h (by simp [LieL3, hr])
  | _ => exact absurd h (by simp [LieL3])

private theorem card_mulAut_A2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.card = 3) :
    Nat.card (MulAut (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) = 11232 := by
  have hcard : q.p ^ q.exponent = 3 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  have hp3 : q.p = 3 := by
    have hdvd : q.p ∣ 3 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  have he1 : q.exponent = 1 := by
    rw [hp3] at hcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (show 3 ^ q.exponent = 3 ^ 1 by simpa using hcard)
  have hK0 := CFSG.Models.lieModel_A 2 q hv (MulEquiv.refl _)
  rw [hp3, he1] at hK0
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hK0
  obtain ⟨eP⟩ := CFSG.GH74.KGroups.L33.equiv_of_lieModel hB
  exact CFSG.GH74.KGroups.L33.card_mulAut eP

theorem kd1912TwoL33_holds : KD1912TwoL33 := by
  rintro S _ _ - - ⟨t, hv⟩ hd hPSL e A hA
  change k2Lie 13 t at hd
  change LieL3 t at hPSL
  obtain ⟨q, rfl⟩ := exists_A2_of_lieL3 hPSL
  have hq : q.card = 3 := by
    simpa [k2Lie] using hd
  obtain ⟨eS⟩ := e
  have hcard : Nat.card (MulAut S) = 11232 := by
    rw [Nat.card_congr (MulAut.congr eS).toEquiv]
    exact card_mulAut_A2 q hv hq
  have hA13 : Nat.card A ≤ 13 := by
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian (p := 13) (by norm_num) hA
    have hdvd : Nat.card A ∣ Nat.card (MulAut S) := Subgroup.card_subgroup_dvd_card A
    rw [hk, hcard] at hdvd
    rw [hk]
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have h169 : 13 ^ 2 ∣ 13 ^ k := pow_dvd_pow 13 (by omega)
      have := h169.trans hdvd
      norm_num at this
    interval_cases k <;> norm_num
  exact ys03_weak_of_card_le (by norm_num) hA13

end CFSG.LocalAnalysis.GLTheoremA
