module

public import CFSG.LieType.Chevalley.EvenRootCommutatorTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootOps
open scoped commutatorElement

theorem g2_even_root_commutator_table
    {R : Type*} [CommRing R] [CharP R 2] (x y : R) :
    ⁅pinnedX .G2 R ![1, 0] x, pinnedX .G2 R ![0, 1] y⁆ =
        pinnedX .G2 R ![1, 1] (x * y) * pinnedX .G2 R ![1, 2] (x * y ^ 2) *
          pinnedX .G2 R ![1, 3] (x * y ^ 3) * pinnedX .G2 R ![2, 3] (x ^ 2 * y ^ 3) ∧
      ⁅pinnedX .G2 R ![0, 1] x, pinnedX .G2 R ![1, 1] y⁆ =
        pinnedX .G2 R ![2, 3] (x * y ^ 2) * pinnedX .G2 R ![1, 3] (x ^ 2 * y) ∧
      ⁅pinnedX .G2 R ![0, 1] x, pinnedX .G2 R ![1, 2] y⁆ = pinnedX .G2 R ![1, 3] (x * y) ∧
      ⁅pinnedX .G2 R ![1, 0] x, pinnedX .G2 R ![1, 3] y⁆ = pinnedX .G2 R ![2, 3] (x * y) ∧
      ⁅pinnedX .G2 R ![1, 1] x, pinnedX .G2 R ![1, 2] y⁆ = pinnedX .G2 R ![2, 3] (x * y) ∧
      ⁅pinnedX .G2 R ![1, 2] x, pinnedX .G2 R ![0, -1] y⁆ =
        pinnedX .G2 R ![1, 0] (x * y ^ 2) * pinnedX .G2 R ![2, 3] (x ^ 2 * y) ∧
      Commute (pinnedX .G2 R ![1, 0] x) (pinnedX .G2 R ![1, 1] y) ∧
      Commute (pinnedX .G2 R ![1, 0] x) (pinnedX .G2 R ![1, 2] y) ∧
      Commute (pinnedX .G2 R ![1, 0] x) (pinnedX .G2 R ![2, 3] y) ∧
      Commute (pinnedX .G2 R ![0, 1] x) (pinnedX .G2 R ![1, 3] y) ∧
      Commute (pinnedX .G2 R ![0, 1] x) (pinnedX .G2 R ![2, 3] y) ∧
      Commute (pinnedX .G2 R ![1, 1] x) (pinnedX .G2 R ![1, 3] y) ∧
      Commute (pinnedX .G2 R ![1, 1] x) (pinnedX .G2 R ![2, 3] y) ∧
      Commute (pinnedX .G2 R ![1, 2] x) (pinnedX .G2 R ![1, 3] y) ∧
      Commute (pinnedX .G2 R ![1, 2] x) (pinnedX .G2 R ![2, 3] y) ∧
      Commute (pinnedX .G2 R ![1, 3] x) (pinnedX .G2 R ![2, 3] y) := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : R) = 1 := by linear_combination h2
  have e5 : orbitCertRoot .G2 5 = ![0, -1] := List.ofFn_injective (by decide +kernel)
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e7 : orbitCertRoot .G2 7 = ![1, 0] := List.ofFn_injective (by decide +kernel)
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot .G2 10 = ![1, 3] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  rw [← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11]
  set s₁ : WeylGroup .G2 := simple .G2 ⟨0, by decide⟩
  set s₂ : WeylGroup .G2 := simple .G2 ⟨1, by decide⟩
  have f6 : s₁ • orbitCertRoot .G2 6 = orbitCertRoot .G2 8 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f9 : s₁ • orbitCertRoot .G2 9 = orbitCertRoot .G2 9 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f10 : s₁ • orbitCertRoot .G2 10 = orbitCertRoot .G2 11 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f11 : s₁ • orbitCertRoot .G2 11 = orbitCertRoot .G2 10 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have g6 : (s₂ * s₁) • orbitCertRoot .G2 6 = orbitCertRoot .G2 9 := by
    rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have g8 : (s₂ * s₁) • orbitCertRoot .G2 8 = orbitCertRoot .G2 5 := by
    rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have g9 : (s₂ * s₁) • orbitCertRoot .G2 9 = orbitCertRoot .G2 8 := by
    rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have g10 : (s₂ * s₁) • orbitCertRoot .G2 10 = orbitCertRoot .G2 11 := by
    rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have g11 : (s₂ * s₁) • orbitCertRoot .G2 11 = orbitCertRoot .G2 7 := by
    rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have k6 : (s₁ * s₂ * s₁) • orbitCertRoot .G2 6 = orbitCertRoot .G2 9 := by
    rw [mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have k10 : (s₁ * s₂ * s₁) • orbitCertRoot .G2 10 = orbitCertRoot .G2 10 := by
    rw [mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have l7 : s₂ • orbitCertRoot .G2 7 = orbitCertRoot .G2 10 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have l11 : s₂ • orbitCertRoot .G2 11 = orbitCertRoot .G2 11 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have r0 : ((7, 6, 12, [(1, 1, 8, 1), (1, 2, 9, -1), (1, 3, 10, -1), (2, 3, 11, 1)]) :
      PairRow) ∈ pairTable .G2 := by decide +kernel
  have r1 : ((7, 10, 12, [(1, 1, 11, 1)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r2 : ((7, 8, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r3 : ((7, 11, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r4 : ((7, 9, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r6 : ((6, 10, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r7 : ((6, 8, 12, [(1, 1, 9, -2), (1, 2, 11, -3), (2, 1, 10, -3)]) : PairRow) ∈
      pairTable .G2 := by decide +kernel
  have r8 : ((6, 11, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r9 : ((6, 9, 12, [(1, 1, 10, 3)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    commute_pinnedX_of_two_eq_zero h2 r2 rfl 1 (one 7) (one 8) x y,
    commute_pinnedX_of_two_eq_zero h2 r4 rfl 1 (one 7) (one 9) x y,
    commute_pinnedX_of_two_eq_zero h2 r3 rfl 1 (one 7) (one 11) x y,
    commute_pinnedX_of_two_eq_zero h2 r6 rfl 1 (one 6) (one 10) x y,
    commute_pinnedX_of_two_eq_zero h2 r8 rfl 1 (one 6) (one 11) x y,
    commute_pinnedX_of_two_eq_zero h2 r8 rfl s₁ f6 f11 x y,
    commute_pinnedX_of_two_eq_zero h2 r6 rfl s₁ f6 f10 x y,
    commute_pinnedX_of_two_eq_zero h2 r6 rfl (s₁ * s₂ * s₁) k6 k10 x y,
    commute_pinnedX_of_two_eq_zero h2 r6 rfl (s₂ * s₁) g6 g10 x y,
    commute_pinnedX_of_two_eq_zero h2 r3 rfl s₂ l7 l11 x y⟩
  · rw [commutatorElement_pinnedX_of_two_eq_zero h2 r0 1 (one 7) (one 6)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, Int.cast_one,
      Int.cast_neg, CharTwo.neg_eq, one_mul, pow_one, mul_one, mul_assoc]
  · rw [commutatorElement_pinnedX_of_two_eq_zero h2 r7 1 (one 6) (one 8)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, Int.cast_neg,
      Int.cast_ofNat, CharTwo.neg_eq, h2, h3, zero_mul, pinnedX_zero, one_mul, pow_one, mul_one]
  · rw [commutatorElement_pinnedX_of_two_eq_zero h2 r9 1 (one 6) (one 9)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, Int.cast_ofNat,
      h3, one_mul, pow_one, mul_one]
  · rw [commutatorElement_pinnedX_of_two_eq_zero h2 r1 1 (one 7) (one 10)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, Int.cast_one,
      one_mul, pow_one, mul_one]
  · rw [commutatorElement_pinnedX_of_two_eq_zero h2 r9 s₁ f6 f9]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, f10, Int.cast_ofNat,
      h3, one_mul, pow_one, mul_one]
  · rw [commutatorElement_pinnedX_of_two_eq_zero h2 r7 (s₂ * s₁) g6 g8]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, g9, g10, g11,
      Int.cast_neg, Int.cast_ofNat, CharTwo.neg_eq, h2, h3, zero_mul, pinnedX_zero, one_mul,
      pow_one, mul_one]

end CFSG.LieType.Chevalley
