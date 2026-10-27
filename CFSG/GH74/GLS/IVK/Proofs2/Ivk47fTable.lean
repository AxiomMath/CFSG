module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

theorem g2_commute_table {R : Type*} [CommRing R] (x y : R) :
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
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e7 : orbitCertRoot .G2 7 = ![1, 0] := List.ofFn_injective (by decide +kernel)
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot .G2 10 = ![1, 3] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  rw [← e6, ← e7, ← e8, ← e9, ← e10, ← e11]
  set s₁ : WeylGroup .G2 := simple .G2 ⟨0, by decide⟩
  set s₂ : WeylGroup .G2 := simple .G2 ⟨1, by decide⟩
  have f6 : s₁ • orbitCertRoot .G2 6 = orbitCertRoot .G2 8 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f10 : s₁ • orbitCertRoot .G2 10 = orbitCertRoot .G2 11 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f11 : s₁ • orbitCertRoot .G2 11 = orbitCertRoot .G2 10 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have g6 : (s₂ * s₁) • orbitCertRoot .G2 6 = orbitCertRoot .G2 9 := by
    rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have g10 : (s₂ * s₁) • orbitCertRoot .G2 10 = orbitCertRoot .G2 11 := by
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
  have r2 : ((7, 8, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r3 : ((7, 11, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r4 : ((7, 9, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r6 : ((6, 10, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have r8 : ((6, 11, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  exact ⟨commute_pinnedX_of_nil r2 rfl 1 (one 7) (one 8) x y,
    commute_pinnedX_of_nil r4 rfl 1 (one 7) (one 9) x y,
    commute_pinnedX_of_nil r3 rfl 1 (one 7) (one 11) x y,
    commute_pinnedX_of_nil r6 rfl 1 (one 6) (one 10) x y,
    commute_pinnedX_of_nil r8 rfl 1 (one 6) (one 11) x y,
    commute_pinnedX_of_nil r8 rfl s₁ f6 f11 x y,
    commute_pinnedX_of_nil r6 rfl s₁ f6 f10 x y,
    commute_pinnedX_of_nil r6 rfl (s₁ * s₂ * s₁) k6 k10 x y,
    commute_pinnedX_of_nil r6 rfl (s₂ * s₁) g6 g10 x y,
    commute_pinnedX_of_nil r3 rfl s₂ l7 l11 x y⟩

theorem g2_commute_three {R : Type*} [CommRing R] (h3 : (3 : R) = 0) (x y : R) :
    Commute (pinnedX .G2 R ![0, 1] x) (pinnedX .G2 R ![1, 2] y) ∧
      Commute (pinnedX .G2 R ![1, 1] x) (pinnedX .G2 R ![1, 2] y) := by
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  rw [← e6, ← e8, ← e9]
  set s₁ : WeylGroup .G2 := simple .G2 ⟨0, by decide⟩
  have f6 : s₁ • orbitCertRoot .G2 6 = orbitCertRoot .G2 8 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f9 : s₁ • orbitCertRoot .G2 9 = orbitCertRoot .G2 9 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have r9 : ((6, 9, 12, [(1, 1, 10, 3)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  have hz : ((3 : ℤ) : R) = 0 := by simpa using h3
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, -, h⟩ := commutatorElement_pinnedX_signs (R := R) r9 1 (one 6) (one 9)
    have h1 := h x y
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hz, zero_mul, mul_zero,
      pinnedX_zero, mul_one] at h1
    exact (commutatorElement_eq_one_iff_commute.1 h1)
  · obtain ⟨σ, -, h⟩ := commutatorElement_pinnedX_signs (R := R) r9 s₁ f6 f9
    have h1 := h x y
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hz, zero_mul, mul_zero,
      pinnedX_zero, mul_one] at h1
    exact (commutatorElement_eq_one_iff_commute.1 h1)

theorem g2_rel_ab {R : Type*} [CommRing R] :
    ∃ e : R, (e = 1 ∨ e = -1) ∧ ∀ x y : R,
      ⁅pinnedX .G2 R ![1, 0] x, pinnedX .G2 R ![1, 3] y⁆ = pinnedX .G2 R ![2, 3] (e * (x * y)) := by
  have e7 : orbitCertRoot .G2 7 = ![1, 0] := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot .G2 10 = ![1, 3] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  rw [← e7, ← e10, ← e11]
  have r1 : ((7, 10, 12, [(1, 1, 11, 1)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r1 1 (one 7) (one 10)
  refine ⟨σ (1, 1, 11, 1), hσ _, fun x y => ?_⟩
  rw [h x y]
  simp [one]

theorem g2_rel_ar {R : Type*} [CommRing R] :
    ∃ e₁ e₂ e₃ e₄ : R, (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ (e₃ = 1 ∨ e₃ = -1) ∧
      (e₄ = 1 ∨ e₄ = -1) ∧ ∀ x y : R,
      ⁅pinnedX .G2 R ![1, 0] x, pinnedX .G2 R ![0, 1] y⁆ =
        pinnedX .G2 R ![1, 1] (e₁ * (x * y)) * pinnedX .G2 R ![1, 2] (e₂ * (x * y ^ 2)) *
          pinnedX .G2 R ![1, 3] (e₃ * (x * y ^ 3)) * pinnedX .G2 R ![2, 3] (e₄ * (x ^ 2 * y ^ 3)) := by
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e7 : orbitCertRoot .G2 7 = ![1, 0] := List.ofFn_injective (by decide +kernel)
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot .G2 10 = ![1, 3] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  rw [← e6, ← e7, ← e8, ← e9, ← e10, ← e11]
  have r0 : ((7, 6, 12, [(1, 1, 8, 1), (1, 2, 9, -1), (1, 3, 10, -1), (2, 3, 11, 1)]) : PairRow) ∈
      pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r0 1 (one 7) (one 6)
  refine ⟨σ (1, 1, 8, 1), -σ (1, 2, 9, -1), -σ (1, 3, 10, -1), σ (2, 3, 11, 1), hσ _, ?_, ?_,
    hσ _, fun x y => ?_⟩
  · rcases hσ (1, 2, 9, -1) with h | h <;> simp [h]
  · rcases hσ (1, 3, 10, -1) with h | h <;> simp [h]
  · rw [h x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, Int.cast_one,
      Int.cast_neg, pow_one, mul_one, mul_assoc, neg_mul, one_mul, mul_neg]

theorem g2_rel_ru {R : Type*} [CommRing R] (h3 : (3 : R) = 0) :
    ∃ e : R, (e = 1 ∨ e = -1) ∧ ∀ x y : R,
      ⁅pinnedX .G2 R ![0, 1] x, pinnedX .G2 R ![1, 1] y⁆ = pinnedX .G2 R ![1, 2] (e * (x * y)) := by
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  rw [← e6, ← e8, ← e9]
  have r7 : ((6, 8, 12, [(1, 1, 9, -2), (1, 2, 11, -3), (2, 1, 10, -3)]) : PairRow) ∈
      pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  have hz : ((3 : ℤ) : R) = 0 := by simpa using h3
  have hm2 : ((-2 : ℤ) : R) = 1 := by
    push_cast
    linear_combination (-1 : R) * h3
  have hm3 : ((-3 : ℤ) : R) = 0 := by
    push_cast
    linear_combination (-1 : R) * h3
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r7 1 (one 6) (one 8)
  refine ⟨σ (1, 1, 9, -2), hσ _, fun x y => ?_⟩
  rw [h x y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, hm2, hm3, zero_mul,
    mul_zero, pinnedX_zero, mul_one, one_mul, pow_one]

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47
