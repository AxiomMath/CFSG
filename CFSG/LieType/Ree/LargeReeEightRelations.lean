module

public import CFSG.LieType.Ree.LargeReeEightBlocks

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open scoped commutatorElement

theorem check_two_central :
    wordCheck Tag.F4 2 [(1, 0, 3, 1), (4, 0, 0, 1), (0, 1, 40, 1), (0, 4, 39, 1)]
      [(1, 1, 44, 1), (4, 4, 43, 1), (0, 1, 40, 1), (0, 4, 39, 1), (1, 0, 3, 1),
        (4, 0, 0, 1)] = true := by
  decide +kernel

theorem check_first_two :
    wordCheck Tag.F4 2 [(1, 0, 16, 1), (4, 0, 15, 1), (6, 0, 43, 1), (0, 1, 3, 1), (0, 4, 0, 1)]
      [(1, 1, 24, 1), (4, 4, 22, 1), (0, 1, 3, 1), (0, 4, 0, 1), (1, 0, 16, 1), (4, 0, 15, 1),
        (6, 0, 43, 1)] = true := by
  decide +kernel

theorem check_central_two :
    wordCheck Tag.F4 2 [(1, 0, 44, 1), (4, 0, 43, 1), (0, 1, 3, 1), (0, 4, 0, 1)]
      [(0, 1, 3, 1), (0, 4, 0, 1), (1, 0, 44, 1), (4, 0, 43, 1)] = true := by
  decide +kernel

theorem check_first_central :
    wordCheck Tag.F4 2 [(1, 0, 16, 1), (4, 0, 15, 1), (6, 0, 43, 1), (0, 1, 40, 1),
      (0, 4, 39, 1)]
      [(0, 1, 40, 1), (0, 4, 39, 1), (1, 0, 16, 1), (4, 0, 15, 1), (6, 0, 43, 1)] = true := by
  decide +kernel

theorem check_central_three_two :
    wordCheck Tag.F4 2 [(1, 0, 44, 1), (4, 0, 43, 1), (0, 1, 40, 1), (0, 4, 39, 1)]
      [(0, 1, 40, 1), (0, 4, 39, 1), (1, 0, 44, 1), (4, 0, 43, 1)] = true := by
  decide +kernel

theorem check_central_one_two :
    wordCheck Tag.F4 2 [(1, 0, 24, 1), (4, 0, 22, 1), (0, 1, 40, 1), (0, 4, 39, 1)]
      [(0, 1, 40, 1), (0, 4, 39, 1), (1, 0, 24, 1), (4, 0, 22, 1)] = true := by
  decide +kernel

theorem check_central_one_three :
    wordCheck Tag.F4 2 [(1, 0, 24, 1), (4, 0, 22, 1), (0, 1, 44, 1), (0, 4, 43, 1)]
      [(0, 1, 44, 1), (0, 4, 43, 1), (1, 0, 24, 1), (4, 0, 22, 1)] = true := by
  decide +kernel

variable {K : Type} [Field K] [CharP K F4.prime]

theorem fourCoord_zero_left
    (f : Fin 4) (d : K) :
    fourCoord f 0 d =
      pinnedX F4.tag K (fourRoot f 2) d * pinnedX F4.tag K (fourRoot f 3) (d ^ 4) := by
  rw [fourCoord_eq, zero_pow (by norm_num), zero_pow (by norm_num), add_zero, pinnedX_zero,
    pinnedX_zero, one_mul, one_mul]

theorem fourCoord_zero_right
    (f : Fin 4) (c : K) :
    fourCoord f c 0 = pinnedX F4.tag K (fourRoot f 0) c *
      pinnedX F4.tag K (fourRoot f 1) (c ^ 4) * pinnedX F4.tag K (fourRoot f 3) (c ^ 6) := by
  rw [fourCoord_eq, zero_pow (by norm_num), zero_add, pinnedX_zero, mul_one]

theorem twoRoot_zero_zero : twoRoot 0 0 = F4.tag.rootCertificate.root 3 := by decide +kernel

theorem twoRoot_zero_one : twoRoot 0 1 = F4.tag.rootCertificate.root 0 := by decide +kernel

theorem fourRoot_one_two : fourRoot 1 2 = F4.tag.rootCertificate.root 24 := by decide +kernel

theorem fourRoot_one_three : fourRoot 1 3 = F4.tag.rootCertificate.root 22 := by decide +kernel

theorem fourRoot_two_two : fourRoot 2 2 = F4.tag.rootCertificate.root 40 := by decide +kernel

theorem fourRoot_two_three : fourRoot 2 3 = F4.tag.rootCertificate.root 39 := by decide +kernel

theorem fourRoot_three_zero : fourRoot 3 0 = F4.tag.rootCertificate.root 16 := by decide +kernel

theorem fourRoot_three_one : fourRoot 3 1 = F4.tag.rootCertificate.root 15 := by decide +kernel

theorem fourRoot_three_two : fourRoot 3 2 = F4.tag.rootCertificate.root 44 := by decide +kernel

theorem fourRoot_three_three : fourRoot 3 3 = F4.tag.rootCertificate.root 43 := by
  decide +kernel

theorem two_cast_eq_zero : ((2 : ℕ) : K) = 0 :=
  have : CharP K 2 := ‹CharP K F4.prime›
  CharP.cast_eq_zero K 2

theorem twoCoord_mul_fourCoord
    (s t : K) :
    twoCoord 0 s * fourCoord 2 0 t = fourCoord 3 0 (s * t) * (fourCoord 2 0 t * twoCoord 0 s) := by
  have h := factorPinned_eq_of_wordCheck check_two_central K two_cast_eq_zero s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  rw [twoCoord_eq, fourCoord_zero_left, fourCoord_zero_left, twoRoot_zero_zero, twoRoot_zero_one,
    fourRoot_two_two, fourRoot_two_three, fourRoot_three_two, fourRoot_three_three, mul_pow]
  simp only [mul_assoc] at h ⊢
  exact h

theorem commutator_twoCoord_fourCoord
    (s t : K) :
    ⁅twoCoord 0 s, fourCoord 2 0 t⁆ = fourCoord 3 0 (s * t) := by
  rw [commutatorElement_def, twoCoord_mul_fourCoord]
  group

theorem fourCoord_mul_twoCoord
    (s t : K) :
    fourCoord 3 s 0 * twoCoord 0 t = fourCoord 1 0 (s * t) * (twoCoord 0 t * fourCoord 3 s 0) := by
  have h := factorPinned_eq_of_wordCheck check_first_two K two_cast_eq_zero s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  rw [twoCoord_eq, fourCoord_zero_right, fourCoord_zero_left, twoRoot_zero_zero, twoRoot_zero_one,
    fourRoot_three_zero, fourRoot_three_one, fourRoot_three_three, fourRoot_one_two,
    fourRoot_one_three, mul_pow]
  simp only [mul_assoc] at h ⊢
  exact h

theorem commute_fourCoord_zero_twoCoord
    (s t : K) :
    Commute (fourCoord 3 0 s) (twoCoord 0 t) := by
  have h := factorPinned_eq_of_wordCheck check_central_two K two_cast_eq_zero s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  change _ * _ = _ * _
  rw [twoCoord_eq, fourCoord_zero_left, twoRoot_zero_zero, twoRoot_zero_one, fourRoot_three_two,
    fourRoot_three_three]
  simp only [mul_assoc] at h ⊢
  exact h

theorem commute_fourCoord_first_central
    (s t : K) :
    Commute (fourCoord 3 s 0) (fourCoord 2 0 t) := by
  have h := factorPinned_eq_of_wordCheck check_first_central K two_cast_eq_zero s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  change _ * _ = _ * _
  rw [fourCoord_zero_right, fourCoord_zero_left, fourRoot_three_zero, fourRoot_three_one,
    fourRoot_three_three, fourRoot_two_two, fourRoot_two_three]
  simp only [mul_assoc] at h ⊢
  exact h

theorem commute_fourCoord_central_three_two
    (s t : K) :
    Commute (fourCoord 3 0 s) (fourCoord 2 0 t) := by
  have h := factorPinned_eq_of_wordCheck check_central_three_two K two_cast_eq_zero s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  change _ * _ = _ * _
  rw [fourCoord_zero_left, fourCoord_zero_left, fourRoot_three_two, fourRoot_three_three,
    fourRoot_two_two, fourRoot_two_three]
  simp only [mul_assoc] at h ⊢
  exact h

theorem commute_fourCoord_one_two
    (s t : K) :
    Commute (fourCoord 1 0 s) (fourCoord 2 0 t) := by
  have h := factorPinned_eq_of_wordCheck check_central_one_two K two_cast_eq_zero s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  change _ * _ = _ * _
  rw [fourCoord_zero_left, fourCoord_zero_left, fourRoot_one_two, fourRoot_one_three,
    fourRoot_two_two, fourRoot_two_three]
  simp only [mul_assoc] at h ⊢
  exact h

theorem commute_fourCoord_one_three
    (s t : K) :
    Commute (fourCoord 1 0 s) (fourCoord 3 0 t) := by
  have h := factorPinned_eq_of_wordCheck check_central_one_three K two_cast_eq_zero s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  change _ * _ = _ * _
  rw [fourCoord_zero_left, fourCoord_zero_left, fourRoot_one_two, fourRoot_one_three,
    fourRoot_three_two, fourRoot_three_three]
  simp only [mul_assoc] at h ⊢
  exact h

variable [Finite K]

theorem commutator_fourCoord_twoCoord
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (c d s : K) :
    ⁅fourCoord 3 c d, twoCoord 0 s⁆ = fourCoord 1 0 (c * s) := by
  have h1 := fourCoord_mul_twoCoord c s
  have h2 := (commute_fourCoord_zero_twoCoord d s).eq
  rw [fourCoord_eq_mul hK, commutatorElement_def]
  calc fourCoord 3 c 0 * fourCoord 3 0 d * twoCoord 0 s * (fourCoord 3 c 0 * fourCoord 3 0 d)⁻¹ *
        (twoCoord 0 s)⁻¹ =
      fourCoord 3 c 0 * (fourCoord 3 0 d * twoCoord 0 s) * (fourCoord 3 0 d)⁻¹ *
        (fourCoord 3 c 0)⁻¹ * (twoCoord 0 s)⁻¹ := by group
    _ = fourCoord 3 c 0 * twoCoord 0 s * (fourCoord 3 c 0)⁻¹ * (twoCoord 0 s)⁻¹ := by
      rw [h2]
      group
    _ = fourCoord 1 0 (c * s) := by
      rw [h1]
      group

theorem commute_fourCoord_three_two
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (c d g : K) :
    Commute (fourCoord 3 c d) (fourCoord 2 0 g) := by
  rw [fourCoord_eq_mul hK]
  exact (commute_fourCoord_first_central c g).mul_left (commute_fourCoord_central_three_two d g)

end CFSG.LieType.Ree.LargeReeCover
