module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NoninvertingSection
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsAlgebra

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
  (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)

theorem weighted_section_vanishing {x u : G} (hx : x * x = 1) {e : ℕ}
    (hu : orderOf u ∣ 2 ^ e) (hnr : ¬ IsConj u u⁻¹) {r : G}
    (hr : r ∈ Subgroup.centralizer {u}) (hodd : Odd (orderOf r)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character x * (basis.representation χ).character x *
        (basis.representation χ).character (u * r) /
          (basis.representation χ).character 1 = 0 :=
  (CFSG.LyonsUnitaryFour.brauer_noninverting_block_section_vanishing basis ideal 2 principal x x
    u hx hx e hu fun t _ h => hnr (isConj_iff.mpr ⟨t, h⟩)).1 r hr
    (Nat.coprime_two_left.mpr hodd)

theorem weighted_rows_vanishing {x u : G} (hx : x * x = 1) {e : ℕ} (hu : orderOf u ∣ 2 ^ e)
    (hnr : ¬ IsConj u u⁻¹) {Φ : G → ℂ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (v : basis.index → Fin 2 → ℂ)
    (hrow : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ r ∈ Subgroup.centralizer {u}, Odd (orderOf r) →
        (basis.representation χ).character (u * r) = v χ 0 + v χ 1 * (1 + ε * Φ r))
    {r₂ : G} (hr₂ : r₂ ∈ Subgroup.centralizer {u}) (hodd₂ : Odd (orderOf r₂))
    (hΦ : Φ r₂ ≠ Φ 1) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character x * (basis.representation χ).character x * v χ 0 /
          (basis.representation χ).character 1 = 0 ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character x * (basis.representation χ).character x * v χ 1 /
          (basis.representation χ).character 1 = 0 := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set S0 := ∑ χ ∈ B, (basis.representation χ).character x * (basis.representation χ).character x *
    v χ 0 / (basis.representation χ).character 1 with hS0
  set S1 := ∑ χ ∈ B, (basis.representation χ).character x * (basis.representation χ).character x *
    v χ 1 / (basis.representation χ).character 1 with hS1
  have hexp : ∀ r ∈ Subgroup.centralizer {u}, Odd (orderOf r) →
      S0 + (1 + ε * Φ r) * S1 = 0 := by
    intro r hr hodd
    have h := weighted_section_vanishing basis ideal principal hx hu hnr hr hodd
    rw [← h, hS0, hS1, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hrow χ hχ r hr hodd]
    ring
  have h1 := hexp 1 (Subgroup.one_mem _) (by simp)
  have h2 := hexp r₂ hr₂ hodd₂
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hdiff : (ε : ℂ) * (Φ r₂ - Φ 1) * S1 = 0 := by linear_combination h2 - h1
  have hS1z : S1 = 0 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hε0
      · exact absurd (sub_eq_zero.mp h) hΦ
    · exact h
  refine ⟨?_, hS1z⟩
  rw [hS1z, mul_zero, add_zero] at h1
  exact h1

theorem exists_ne_of_unique_rows {u : G} {C : Subgroup G} {Φ : G → ℂ} {ε : ℤ} {χ₀ : basis.index}
    (v : Fin 2 → ℂ)
    (hrow : ∀ r ∈ C, Odd (orderOf r) →
      (basis.representation χ₀).character (u * r) = v 0 + v 1 * (1 + ε * Φ r))
    (huniq : ∀ w : Fin 2 → ℂ, (∀ r ∈ C, Odd (orderOf r) →
      (basis.representation χ₀).character (u * r) = w 0 + w 1 * (1 + ε * Φ r)) → w = v) :
    ∃ r ∈ C, Odd (orderOf r) ∧ Φ r ≠ Φ 1 := by
  by_contra hcon
  push Not at hcon
  have hw := huniq ![v 0 + v 1 * (1 + ε * Φ 1) - (1 + ε * Φ 1) * (v 1 + 1), v 1 + 1]
    fun r hr hodd => by
      rw [hrow r hr hodd, hcon r hr hodd]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
  have h : v 1 + 1 = v 1 := by simpa using congrFun hw 1
  have : (1 : ℂ) = 0 := by linear_combination h
  exact one_ne_zero this

omit [Fintype G] in
theorem weighted_fourier_vanishing {ι : Type*} {B : Finset ι} {m M : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hm : m = 2 * M) (V : ι → ℕ → ℂ) (w : ι → ℂ)
    (hk : ∀ k ∈ Finset.Ico 1 m, k ≠ M → ∑ χ ∈ B, w χ * V χ k = 0) {j : ℕ} (hj : Even j) :
    ∑ χ ∈ B, w χ * fourierTransform m ζ (V χ) j = 0 := by
  simp only [fourierTransform, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk' => ?_
  by_cases hkM : k = M
  · subst hkM
    obtain ⟨j', rfl⟩ := hj
    have hpow : ζ ^ ((j' + j') * k) = 1 := by
      rw [show (j' + j') * k = m * j' by rw [hm]; ring, pow_mul, hζ.pow_eq_one, one_pow]
    simp [hpow]
  · have h := hk k hk' hkM
    calc ∑ χ ∈ B, w χ * ((m : ℂ)⁻¹ * ((ζ ^ (j * k) - 1) * V χ k)) =
        (m : ℂ)⁻¹ * (ζ ^ (j * k) - 1) * ∑ χ ∈ B, w χ * V χ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => by ring
      _ = 0 := by rw [h, mul_zero]

theorem weighted_power_vanishing {x y : G} (hx : x * x = 1) {e M : ℕ}
    (hyo : ∀ i : ℕ, orderOf (y ^ (2 * i + 1)) ∣ 2 ^ e)
    (hynr : ∀ i : ℕ, ¬ IsConj (y ^ (2 * i + 1)) (y ^ (2 * i + 1))⁻¹) (c : basis.index → ℂ)
    (hc : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      c χ = (M : ℂ)⁻¹ *
        ∑ i ∈ Finset.range M, (basis.representation χ).character (y ^ (2 * i + 1))) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      c χ * ((basis.representation χ).character x * (basis.representation χ).character x /
        (basis.representation χ).character 1) = 0 := by
  have h : ∀ i ∈ Finset.range M,
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character x * (basis.representation χ).character x *
          (basis.representation χ).character (y ^ (2 * i + 1) * 1) /
            (basis.representation χ).character 1 = 0 := fun i _ =>
    weighted_section_vanishing basis ideal principal hx (hyo i) (hynr i) (Subgroup.one_mem _)
      (by simp)
  have hB : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      c χ * ((basis.representation χ).character x * (basis.representation χ).character x /
        (basis.representation χ).character 1) = (M : ℂ)⁻¹ * ∑ i ∈ Finset.range M,
          (basis.representation χ).character x * (basis.representation χ).character x *
            (basis.representation χ).character (y ^ (2 * i + 1) * 1) /
              (basis.representation χ).character 1 := fun χ hχ => by
    rw [hc χ hχ, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_one]
    ring
  rw [Finset.sum_congr rfl hB, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_eq_zero h, mul_zero]

theorem weighted_central_fourier_vanishing {x a : G} (hx : x * x = 1) {m M : ℕ}
    (hm : m = 2 * M) {e : ℕ} (ha : ∀ k : ℕ, orderOf (a ^ k) ∣ 2 ^ e)
    (hnr : ∀ k ∈ Finset.Ico 1 m, k ≠ M → ¬ IsConj (a ^ k) (a ^ k)⁻¹) {Φ : G → ℂ} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : basis.index → ℕ → Fin 2 → ℂ)
    (hrow : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf r) →
        (basis.representation χ).character (a ^ k * r) = v χ k 0 + v χ k 1 * (1 + ε * Φ r))
    (hne : ∀ k ∈ Finset.Ico 1 m,
      ∃ r ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf r) ∧ Φ r ≠ Φ 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {j : ℕ} (hj : Even j) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character x * (basis.representation χ).character x /
        (basis.representation χ).character 1 * fourierTransform m ζ (fun k => v χ k 0) j =
      0 := by
  refine weighted_fourier_vanishing hζ hm (fun χ k => v χ k 0)
    (fun χ => (basis.representation χ).character x * (basis.representation χ).character x /
      (basis.representation χ).character 1) (fun k hk hkM => ?_) hj
  obtain ⟨r₂, hr₂, hodd, hΦ⟩ := hne k hk
  have h := (weighted_rows_vanishing basis ideal principal hx (ha k) (hnr k hk hkM) hε
    (fun χ ℓ => v χ k ℓ) (fun χ hχ r hr hro => hrow χ hχ k hk r hr hro) hr₂ hodd hΦ).1
  refine (Finset.sum_congr rfl fun χ _ => ?_).trans h
  ring

end CFSG.Wreathed.ConditionalGlobalDegrees
