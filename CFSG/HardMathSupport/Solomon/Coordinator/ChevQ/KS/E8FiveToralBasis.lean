module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

theorem exists_basis_of_commGroup {A : Type*} [CommGroup A] (hexp : ∀ x : A, x ^ 5 = 1)
    (hcard : Nat.card A = 5 ^ 3) :
    ∃ x : Fin 3 → A, (∀ a : A, ∃ n : Fin 3 → ℕ, a = x 0 ^ n 0 * x 1 ^ n 1 * x 2 ^ n 2) ∧
      ∀ i j k : ℕ, x 0 ^ i * x 1 ^ j * x 2 ^ k = 1 → 5 ∣ i ∧ 5 ∣ j ∧ 5 ∣ k := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsmul : ∀ y : Additive A, (5 : ℕ) • y = 0 := by
    intro y
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hexp _
  letI : Module (ZMod 5) (Additive A) := AddCommGroup.zmodModule hsmul
  have hA : Nat.card A ≠ 0 := by
    rw [hcard]
    norm_num
  haveI : Finite (Additive A) := Nat.finite_of_card_ne_zero hA
  have h1 : Nat.card (Additive A) = 5 ^ Module.finrank (ZMod 5) (Additive A) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 5), Nat.card_zmod]
  have hrank : Module.finrank (ZMod 5) (Additive A) = 3 := by
    have h2 : (5 : ℕ) ^ 3 = 5 ^ Module.finrank (ZMod 5) (Additive A) := by
      rw [← h1]
      exact hcard.symm
    exact (Nat.pow_right_injective (by norm_num) h2).symm
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 3) (ZMod 5) (Additive A)) :=
    ⟨Module.finBasisOfFinrankEq (ZMod 5) (Additive A) hrank⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → A, ∀ t, Additive.ofMul (x t) = b t :=
    ⟨fun t => Additive.toMul (b t), fun t => rfl⟩
  have hform : ∀ n : Fin 3 → ℕ,
      Additive.ofMul (x 0 ^ n 0 * x 1 ^ n 1 * x 2 ^ n 2) = n 0 • b 0 + n 1 • b 1 + n 2 • b 2 := by
    intro n
    simp only [ofMul_mul, ofMul_pow, hx]
  have key : ∀ (c : ZMod 5) (y : Additive A), c.val • y = c • y := by
    intro c y
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 5), ZMod.natCast_zmod_val]
  refine ⟨x, ?_, ?_⟩
  · intro a
    have hv := b.sum_repr (Additive.ofMul a)
    rw [Fin.sum_univ_three] at hv
    obtain ⟨n, hn⟩ : ∃ n : Fin 3 → ℕ,
        Additive.ofMul a = n 0 • b 0 + n 1 • b 1 + n 2 • b 2 := by
      refine ⟨fun t => (b.repr (Additive.ofMul a) t).val, ?_⟩
      simp only [key]
      exact hv.symm
    refine ⟨n, ?_⟩
    apply Additive.ofMul.injective
    rw [hform n]
    exact hn
  · intro i j k h
    have h' : Additive.ofMul (x 0 ^ i * x 1 ^ j * x 2 ^ k) = Additive.ofMul 1 := by
      rw [h]
    simp only [ofMul_mul, ofMul_pow, hx, ofMul_one] at h'
    have hsum : ∑ t : Fin 3, (![(i : ZMod 5), (j : ZMod 5), (k : ZMod 5)] t) • b t = 0 := by
      rw [Fin.sum_univ_three]
      simpa [Nat.cast_smul_eq_nsmul] using h'
    have hall := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum
    have hi : ((i : ℕ) : ZMod 5) = 0 := hall 0
    have hj : ((j : ℕ) : ZMod 5) = 0 := hall 1
    have hk : ((k : ℕ) : ZMod 5) = 0 := hall 2
    exact ⟨(ZMod.natCast_eq_zero_iff i 5).mp hi, (ZMod.natCast_eq_zero_iff j 5).mp hj,
      (ZMod.natCast_eq_zero_iff k 5).mp hk⟩

theorem exists_basis_of_cube {G : Type*} [Group G] {E : Subgroup G}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ x ∈ E, x ^ 5 = 1)
    (hcard : Nat.card E = 5 ^ 3) :
    ∃ x₀ ∈ E, ∃ x₁ ∈ E, ∃ x₂ ∈ E, E ≤ Subgroup.closure {x₀, x₁, x₂} ∧
      ∀ i j k : ℕ, x₀ ^ i * x₁ ^ j * x₂ ^ k = 1 → 5 ∣ i ∧ 5 ∣ j ∧ 5 ∣ k := by
  letI : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm := fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2) }
  have hexp' : ∀ x : E, x ^ 5 = 1 := fun x => Subtype.ext (hexp x.1 x.2)
  obtain ⟨x, hgen, hrel⟩ := exists_basis_of_commGroup hexp' hcard
  refine ⟨(x 0 : G), (x 0).2, (x 1 : G), (x 1).2, (x 2 : G), (x 2).2, ?_, ?_⟩
  · intro g hg
    obtain ⟨n, hn⟩ := hgen ⟨g, hg⟩
    have hg' : g = (x 0 : G) ^ n 0 * (x 1 : G) ^ n 1 * (x 2 : G) ^ n 2 :=
      congrArg Subtype.val hn
    rw [hg']
    refine mul_mem (mul_mem (pow_mem ?_ _) (pow_mem ?_ _)) (pow_mem ?_ _) <;>
      exact Subgroup.subset_closure (by simp)
  · intro i j k h
    apply hrel i j k
    exact Subtype.ext h

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
