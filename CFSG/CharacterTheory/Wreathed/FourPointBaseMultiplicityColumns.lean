module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseGram
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FourPointBaseMultiplicity

open CFSG.Wreathed.ConditionalGeneralBase

section Sums

variable {M : Type*} [AddCommMonoid M]

theorem sum_Icc_one_three (F : ℕ → M) : ∑ k ∈ Finset.Icc 1 3, F k = F 1 + F 2 + F 3 := by
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

theorem sum_Ico_one_four (F : ℕ → M) : ∑ k ∈ Finset.Ico 1 4, F k = F 1 + F 2 + F 3 := by
  rw [show Finset.Ico 1 4 = {1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

theorem sum_zmod_four (F : ZMod 4 → M) : ∑ r : ZMod 4, F r = F 0 + F 1 + F 2 + F 3 := by
  rw [show (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc,
    add_assoc]

end Sums

section Orthogonality

variable {ι : Type*} (B : Finset ι)

theorem sum_mul_conj_eq_zero_symm (W Z : ι → ℂ) (h : ∑ χ ∈ B, W χ * conj (Z χ) = 0) :
    ∑ χ ∈ B, Z χ * conj (W χ) = 0 := by
  have h' := congrArg conj h
  rw [map_sum, map_zero] at h'
  rw [← h']
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem sum_mul_conj_comb (W p q r : ι → ℂ) (α β : ℂ) (hr : ∀ χ ∈ B, r χ = α * p χ + β * q χ)
    (hp : ∑ χ ∈ B, W χ * conj (p χ) = 0) (hq : ∑ χ ∈ B, W χ * conj (q χ) = 0) :
    ∑ χ ∈ B, W χ * conj (r χ) = 0 := by
  have h : ∀ χ ∈ B, W χ * conj (r χ) =
      conj α * (W χ * conj (p χ)) + conj β * (W χ * conj (q χ)) := by
    intro χ hχ
    rw [hr χ hχ, map_add, map_mul, map_mul]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, hq,
    mul_zero, mul_zero, add_zero]

theorem sum_mul_conj_sum_eq_zero {κ : Type*} (s : Finset κ) (W : ι → ℂ) (w : κ → ι → ℂ)
    (a : ℂ) (c : κ → ℂ) (hw : ∀ n ∈ s, ∑ χ ∈ B, W χ * conj (w n χ) = 0) :
    ∑ χ ∈ B, W χ * conj (a * ∑ n ∈ s, c n * w n χ) = 0 := by
  have h : ∀ χ ∈ B, W χ * conj (a * ∑ n ∈ s, c n * w n χ) =
      conj a * ∑ n ∈ s, conj (c n) * (W χ * conj (w n χ)) := by
    intro χ _
    rw [map_mul, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_eq_zero fun n hn => by rw [← Finset.mul_sum, hw n hn, mul_zero], mul_zero]

theorem sum_comb_mul_conj_eq_zero {κ : Type*} (s : Finset κ) (Z T : ι → ℂ) (g : κ → ι → ℂ)
    (c : κ → ℂ) (hZ : ∀ χ ∈ B, Z χ = ∑ j ∈ s, g j χ * c j)
    (hg : ∀ j ∈ s, ∑ χ ∈ B, g j χ * conj (T χ) = 0) : ∑ χ ∈ B, Z χ * conj (T χ) = 0 := by
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ χ hχ, Finset.sum_mul], Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  calc ∑ χ ∈ B, g j χ * c j * conj (T χ) = c j * ∑ χ ∈ B, g j χ * conj (T χ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ => by ring
    _ = 0 := by rw [hg j hj, mul_zero]

end Orthogonality

section Orbits

variable {ι : Type*} (c : ZMod 4 → ZMod 4 → ι → ℂ)
  (hsw : ∀ r s χ, c r s χ = c s r χ) (hrot : ∀ r s χ, c r s χ = c s (-r - s) χ)
include hsw hrot

theorem orbit_values (χ : ι) :
    c 1 2 χ = c 1 1 χ ∧ c 2 1 χ = c 1 1 χ ∧ c 2 0 χ = c 2 2 χ ∧ c 0 2 χ = c 2 2 χ ∧
      c 3 2 χ = c 3 3 χ ∧ c 2 3 χ = c 3 3 χ ∧ c 0 1 χ = c 1 0 χ ∧ c 0 3 χ = c 1 0 χ ∧
      c 3 0 χ = c 1 0 χ ∧ c 1 3 χ = c 1 0 χ ∧ c 3 1 χ = c 1 0 χ := by
  have e12 : c 1 2 χ = c 1 1 χ := by
    rw [hrot 1 1 χ, show (-(1 : ZMod 4) - 1) = 2 by decide]
  have e20 : c 2 0 χ = c 2 2 χ := by
    rw [hrot 2 2 χ, show (-(2 : ZMod 4) - 2) = 0 by decide]
  have e32 : c 3 2 χ = c 3 3 χ := by
    rw [hrot 3 3 χ, show (-(3 : ZMod 4) - 3) = 2 by decide]
  have e03 : c 0 3 χ = c 1 0 χ := by
    rw [hrot 1 0 χ, show (-(1 : ZMod 4) - 0) = 3 by decide]
  have e13 : c 1 3 χ = c 0 1 χ := by
    rw [hrot 0 1 χ, show (-(0 : ZMod 4) - 1) = 3 by decide]
  have e01 : c 0 1 χ = c 1 0 χ := hsw 0 1 χ
  refine ⟨e12, by rw [hsw 2 1 χ, e12], e20, by rw [hsw 0 2 χ, e20], e32,
    by rw [hsw 2 3 χ, e32], e01, e03, by rw [hsw 3 0 χ, e03], by rw [e13, e01],
    by rw [hsw 3 1 χ, e13, e01]⟩

theorem orbit_constant :
    let O : Fin 5 → Finset (ZMod 4 × ZMod 4) :=
      ![{(0, 0)}, {(1, 1), (1, 2), (2, 1)}, {(2, 2), (2, 0), (0, 2)},
        {(3, 3), (3, 2), (2, 3)}, {(1, 0), (0, 1), (3, 1), (1, 3), (0, 3), (3, 0)}]
    ∀ k : Fin 5, ∀ p ∈ O k, ∀ q ∈ O k, ∀ χ, c p.1 p.2 χ = c q.1 q.2 χ := by
  intro O
  let rep : Fin 5 → ZMod 4 × ZMod 4 := ![(0, 0), (1, 1), (2, 2), (3, 3), (1, 0)]
  have hrep : ∀ k : Fin 5, ∀ p ∈ O k, ∀ χ, c p.1 p.2 χ = c (rep k).1 (rep k).2 χ := by
    intro k p hp χ
    obtain ⟨e12, e21, e20, e02, e32, e23, e01, e03, e30, e13, e31⟩ :=
      orbit_values c hsw hrot χ
    fin_cases k <;> simp only [O, rep, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    · rw [hp]
    · rcases hp with rfl | rfl | rfl
      · rfl
      · exact e12
      · exact e21
    · rcases hp with rfl | rfl | rfl
      · rfl
      · exact e20
      · exact e02
    · rcases hp with rfl | rfl | rfl
      · rfl
      · exact e32
      · exact e23
    · rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      · exact e01
      · exact e31
      · exact e13
      · exact e03
      · exact e30
  intro k p hp q hq χ
  rw [hrep k p hp χ, hrep k q hq χ]

theorem antidiagonal_sums (h00 : ∀ χ, c 0 0 χ = 0) (χ : ι) :
    ∑ r : ZMod 4, c r (0 - r) χ = 2 * c 1 0 χ + c 2 2 χ ∧
      ∑ r : ZMod 4, c r (1 - r) χ = 2 * c 1 0 χ + 2 * c 3 3 χ ∧
      ∑ r : ZMod 4, c r (2 - r) χ = 2 * c 2 2 χ + c 1 1 χ + c 3 3 χ ∧
      ∑ r : ZMod 4, c r (3 - r) χ = 2 * c 1 0 χ + 2 * c 1 1 χ := by
  obtain ⟨e12, e21, e20, e02, e32, e23, e01, e03, e30, e13, e31⟩ := orbit_values c hsw hrot χ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sum_zmod_four, show (0 : ZMod 4) - 0 = 0 by decide, show (0 : ZMod 4) - 1 = 3 by decide,
      show (0 : ZMod 4) - 2 = 2 by decide, show (0 : ZMod 4) - 3 = 1 by decide, h00, e13, e31]
    ring
  · rw [sum_zmod_four, show (1 : ZMod 4) - 0 = 1 by decide, show (1 : ZMod 4) - 1 = 0 by decide,
      show (1 : ZMod 4) - 2 = 3 by decide, show (1 : ZMod 4) - 3 = 2 by decide, e01, e23, e32]
    ring
  · rw [sum_zmod_four, show (2 : ZMod 4) - 0 = 2 by decide, show (2 : ZMod 4) - 1 = 1 by decide,
      show (2 : ZMod 4) - 2 = 0 by decide, show (2 : ZMod 4) - 3 = 3 by decide, e02, e20]
    ring
  · rw [sum_zmod_four, show (3 : ZMod 4) - 0 = 3 by decide, show (3 : ZMod 4) - 1 = 2 by decide,
      show (3 : ZMod 4) - 2 = 1 by decide, show (3 : ZMod 4) - 3 = 0 by decide, e03, e12, e21,
      e30]
    ring

end Orbits

theorem dualSix_counts :
    let idx : Fin 4 → ZMod 4 × ZMod 4 := ![(1, 1), (2, 2), (3, 3), (1, 0)]
    let Gr : Matrix (Fin 4) (Fin 4) ℤ := !![8, 6, 6, 6; 6, 8, 6, 6; 6, 6, 8, 6; 6, 6, 6, 7]
    ∀ l l' : Fin 4, (6 : ℤ) +
      ((Finset.univ : Finset (Fin 6)).filter (fun k => dualSixFun (idx l') k = idx l)).card =
        Gr l l' := by
  intro idx Gr l l'
  fin_cases l <;> fin_cases l' <;> decide

end CFSG.Wreathed.FourPointBaseMultiplicity
