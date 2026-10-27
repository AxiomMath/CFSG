module

public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import Mathlib.GroupTheory.Sylow

open MulAction Pointwise Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p n : ℕ} {P : Type*} [Group P] {X : Subgroup P}

theorem prime_dvd_index_of_lt_top (hp : p.Prime) (hP : Nat.card P = p ^ n) (hX : X < ⊤) :
    p ∣ X.index := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hP ▸ X.index_dvd_card)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hX.ne (Subgroup.index_eq_one.mp (by simpa using hj))
  exact hj ▸ dvd_pow_self p hj0

theorem prime_dvd_natCard_range_leftCoset_of_lt_top (hp : p.Prime) (hP : Nat.card P = p ^ n)
    (hX : X < ⊤) : p ∣ Nat.card (Set.range fun g : P => g • (X : Set P)) := by
  rw [natCard_range_leftCoset]
  exact prime_dvd_index_of_lt_top hp hP hX

theorem prime_dvd_relIndex_normalizer (hp : p.Prime) (hP : Nat.card P = p ^ n) (hX : X < ⊤) :
    p ∣ X.relIndex (normalizer (X : Set P)) := by
  have := Fact.mk hp
  have : Finite P := Nat.finite_of_card_ne_zero (by simp [hP, hp.pos.ne'])
  obtain ⟨m, hm⟩ := ((IsPGroup.of_card hP).to_subgroup X).exists_card_eq
  have hfix : Nat.card (fixedPoints X (P ⧸ X)) = X.relIndex (normalizer (X : Set P)) := by
    rw [Nat.card_congr (Sylow.fixedPointsMulLeftCosetsEquivQuotient X)]
    simp [Subgroup.relIndex, Subgroup.index_eq_card]
  have hcong := natCard_modEq_natCard_fixedPoints (P := X) (X := P ⧸ X) hm
  rw [hfix, ← Subgroup.index_eq_card] at hcong
  exact Nat.modEq_zero_iff_dvd.mp
    ((Nat.modEq_zero_iff_dvd.mpr (prime_dvd_index_of_lt_top hp hP hX)).symm.trans hcong).symm

theorem le_relIndex_normalizer (hp : p.Prime) (hP : Nat.card P = p ^ n) (hX : X < ⊤) :
    p ≤ X.relIndex (normalizer (X : Set P)) := by
  have : Finite P := Nat.finite_of_card_ne_zero (by simp [hP, hp.pos.ne'])
  have h0 : X.relIndex (normalizer (X : Set P)) ≠ 0 := by
    simpa [Subgroup.relIndex] using
      Subgroup.index_ne_zero_of_finite (H := X.comap (normalizer (X : Set P)).subtype)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (prime_dvd_relIndex_normalizer hp hP hX)

theorem lt_normalizer_of_natCard_eq_pow (hp : p.Prime) (hP : Nat.card P = p ^ n) (hX : X < ⊤) :
    X < normalizer (X : Set P) := by
  refine Subgroup.le_normalizer.lt_of_not_ge fun hle => ?_
  have h1 : X.relIndex (normalizer (X : Set P)) = 1 := Subgroup.relIndex_eq_one.mpr hle
  have h2 := le_relIndex_normalizer hp hP hX
  have := hp.two_le
  omega

theorem normalizerCondition_of_isPGroup [Finite P] [Fact p.Prime] (hP : IsPGroup p P) :
    NormalizerCondition P := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact fun _ hX => lt_normalizer_of_natCard_eq_pow Fact.out hn hX

end

end CFSG.FeitThompson
