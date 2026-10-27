module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HSp44
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCLinearDegree

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open CFSG.Open CFSG.Blueprint

theorem pow_four_eq_one_of_pow_eight_eq_one {K : Type*} [Field K] [CharP K 2] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4) {x : Matrix.GeneralLinearGroup ι K}
    (hx : x ^ 8 = 1) : x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  set X : Matrix ι ι K := (x : Matrix ι ι K)
  have hX8 : X ^ 8 = 1 := by
    have := congrArg (fun g : Matrix.GeneralLinearGroup ι K => (g : Matrix ι ι K)) hx
    simpa [X] using this
  have hX : X ^ (2 ^ 3) = 1 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hX8
  have hnil : IsNilpotent (X - 1) := by
    refine ⟨2 ^ 3, ?_⟩
    rw [sub_pow_char_pow_of_commute 2 3 (Commute.one_right X), hX, one_pow, sub_self]
  have hd' := CFSG.ComponentClassification.UnbalancedGS.LinearDegree.pow_card_eq_zero_of_isNilpotent
    hnil
  rw [hι] at hd'
  have h0 : X ^ 4 = 1 := by
    have h := hd'
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at h
    rw [sub_pow_char_pow_of_commute 2 2 (Commute.one_right X), one_pow, sub_eq_zero] at h
    exact h
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact h0

theorem orderOf_ne_eight_statedSp_gf4 (g : StatedSp 2 (GaloisField 2 2)) : orderOf g ≠ 8 := by
  intro h
  have hg8 : g ^ 8 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one g
  have hcoe : ((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (GaloisField 2 2))) ^ 8 = 1 := by
    have := congrArg
      (fun u : StatedSp 2 (GaloisField 2 2) =>
        (u : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (GaloisField 2 2))) hg8
    simpa using this
  have hcard : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
  have h4 : ((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (GaloisField 2 2))) ^ 4 = 1 :=
    pow_four_eq_one_of_pow_eight_eq_one (K := GaloisField 2 2) (ι := Fin 2 ⊕ Fin 2) hcard hcoe
  have hg4 : g ^ 4 = 1 := Subtype.ext (by simpa using h4)
  have hdvd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one hg4
  rw [h] at hdvd
  exact absurd hdvd (by norm_num)

theorem orderOf_ne_eight_of_lieModel_psp_two_two_two {N : Type} [Group N]
    (hN : LieModel N .PSp 2 2 2) (g : N) : orderOf g ≠ 8 := by
  obtain ⟨φ⟩ := CFSG.EvenSporadicStandard.M22Std.P21H.nonempty_mulEquiv_statedSp44 hN
  intro h
  exact orderOf_ne_eight_statedSp_gf4 (φ g) (by rw [MulEquiv.orderOf_eq φ g, h])

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
