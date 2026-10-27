module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcUCat
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClGen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace CrossExcU

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Subgroup

section Numerics

variable {p a : ℕ}

theorem crossExcU_dvd_pow_sub_one_iff (ha : 1 ≤ a) (j : ℕ) :
    p ∣ a ^ j - 1 ↔ ((a : ZMod p)) ^ j = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ ha), Nat.cast_pow, Nat.cast_one,
    sub_eq_zero]

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem crossExcU_card_cast_eq (h : UnitaryFieldData ℓ f K) :
    ((Nat.card K : ℕ) : ZMod p) = (-((ℓ ^ f : ℕ) : ZMod p)) ^ 2 := by
  rw [h.card_eq_sq]
  push_cast
  ring

theorem crossExcU_card_pow_iff_of_odd (h : UnitaryFieldData ℓ f K)
    (hodd : Odd (unitaryOrder ℓ f p)) (j : ℕ) :
    p ∣ Nat.card K ^ j - 1 ↔ unitaryOrder ℓ f p ∣ j := by
  rw [crossExcU_dvd_pow_sub_one_iff Finite.card_pos, crossExcU_card_cast_eq h, ← pow_mul,
    ← unitaryOrder_dvd_iff (2 * j)]
  exact (Nat.coprime_two_right.2 hodd).dvd_mul_left

theorem crossExcU_card_pow_iff_of_even (h : UnitaryFieldData ℓ f K)
    (heven : Even (unitaryOrder ℓ f p)) (j : ℕ) :
    p ∣ Nat.card K ^ j - 1 ↔ unitaryOrder ℓ f p / 2 ∣ j := by
  rw [crossExcU_dvd_pow_sub_one_iff Finite.card_pos, crossExcU_card_cast_eq h, ← pow_mul,
    ← unitaryOrder_dvd_iff (2 * j)]
  obtain ⟨d, hd⟩ := heven
  have he : unitaryOrder ℓ f p / 2 = d := by omega
  rw [he, hd, ← two_mul, Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)]

end Numerics

section Odd

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem unitaryAbelianAt_of_odd (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : ¬ p ∣ ℓ) (hodd : Odd (unitaryOrder ℓ f p)) (n : ℕ) :
    UnitaryAbelianAt ℓ f K n p (unitaryOrder ℓ f p) := by
  intro hne P hP
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [h.card_eq_sq]
    exact fun hd => hpℓ (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd))
  have hGL : IsMulCommutative (P.map (unitarySU ℓ f K n).subtype) :=
    isMulCommutative_of_isPGroup_GL_matrix (hp.odd_of_ne_two (by omega)) hpK
      (unitaryOrder_pos hp hpℓ) (crossExcU_card_pow_iff_of_odd h hodd) hne (hP.map _)
  exact crossExcCl_isMulCommutative_of_map_injective _ (Subgroup.subtype_injective _) hGL

end Odd

end CrossExcU

end CFSG.LocalAnalysis.RankFourTheoremC
