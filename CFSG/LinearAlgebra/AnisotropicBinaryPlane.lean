module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.Algebra.QuadraticAlgebra.Basic

public section

namespace CFSG.LinearAlgebra

open QuadraticAlgebra

variable {K : Type*} [Field K] {ε : K}

theorem sq_ne_one_add_mul_of_anisotropic [CharP K 2]
    (hQ : ∀ x y : K, x ^ 2 + ε * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0) (r : K) :
    r ^ 2 ≠ 1 + ε * r := fun h =>
  one_ne_zero (hQ r 1 (by linear_combination h + (1 + ε * r) * CharTwo.two_eq_zero (R := K))).2

theorem anisotropic_binary_plane_norm_field [CharP K 2]
    (hQ : ∀ x y : K, x ^ 2 + ε * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0) :
    (∀ x y u v : K, (⟨x, y⟩ * ⟨u, v⟩ : QuadraticAlgebra K 1 ε) =
        ⟨x * u + y * v, x * v + y * u + ε * y * v⟩) ∧
      (1 : QuadraticAlgebra K 1 ε) = ⟨1, 0⟩ ∧ IsField (QuadraticAlgebra K 1 ε) ∧
      (∀ a : K, algebraMap K (QuadraticAlgebra K 1 ε) a = ⟨a, 0⟩) ∧
      Function.Injective (algebraMap K (QuadraticAlgebra K 1 ε)) ∧
      Module.finrank K (QuadraticAlgebra K 1 ε) = 2 ∧
      (∀ x y : K, star (⟨x, y⟩ : QuadraticAlgebra K 1 ε) = ⟨x + ε * y, y⟩) ∧
      (∀ (c : K) (z : QuadraticAlgebra K 1 ε), star (c • z) = c • star z) ∧
      (starRingAut : RingAut (QuadraticAlgebra K 1 ε)) ≠ 1 ∧
      orderOf (starRingAut : RingAut (QuadraticAlgebra K 1 ε)) = 2 ∧
      (∀ z : QuadraticAlgebra K 1 ε, star z = z ↔ z.im = 0) ∧
      (∀ x y : K, (⟨x, y⟩ : QuadraticAlgebra K 1 ε) * star ⟨x, y⟩ =
        ⟨x ^ 2 + ε * x * y + y ^ 2, 0⟩) ∧
      ∀ n : ℕ, 1 ≤ n → Nat.card K = 2 ^ n →
        Nat.card (QuadraticAlgebra K 1 ε) = 2 ^ (2 * n) ∧
          ∀ z : QuadraticAlgebra K 1 ε, star z = z ^ 2 ^ n := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hε : ε ≠ 0 := fun h => one_ne_zero (hQ 1 1 (by linear_combination h2 + h)).1
  have : Fact (∀ r : K, r ^ 2 ≠ 1 + ε * r) := ⟨sq_ne_one_add_mul_of_anisotropic hQ⟩
  have hstar : ∀ x y : K, star (⟨x, y⟩ : QuadraticAlgebra K 1 ε) = ⟨x + ε * y, y⟩ :=
    fun x y => by ext <;> simp [CharTwo.neg_eq]
  have hlin : ∀ (c : K) (z : QuadraticAlgebra K 1 ε), star (c • z) = c • star z := fun c z => by
    ext
    · simp only [re_star, re_smul, im_smul, smul_eq_mul]
      ring
    · simp
  have hne : (starRingAut : RingAut (QuadraticAlgebra K 1 ε)) ≠ 1 := fun h => hε <| by
    simpa [hstar] using congrArg (fun f : RingAut (QuadraticAlgebra K 1 ε) => (f ⟨0, 1⟩).re) h
  have hord : orderOf (starRingAut : RingAut (QuadraticAlgebra K 1 ε)) = 2 :=
    orderOf_eq_prime (RingEquiv.ext fun z => by simp [sq, RingAut.mul_apply]) hne
  refine ⟨fun x y u v => by ext <;> simp, rfl, Field.toIsField _, fun _ => rfl,
    algebraMap_injective, finrank_eq_two 1 ε, hstar, hlin, hne, hord,
    fun z => ?_, fun x y => ?_, fun n hn hK => ?_⟩
  · rw [← mk_eta z, hstar]
    simp [QuadraticAlgebra.ext_iff, hε]
  · rw [hstar]
    ext <;> simp
    · ring
    · linear_combination (x * y + ε * y * y) * h2
  · have hcard : Nat.card (QuadraticAlgebra K 1 ε) = 2 ^ (2 * n) := by
      rw [Nat.card_congr (equivProd 1 ε), Nat.card_prod, hK, ← pow_add, two_mul]
    refine ⟨hcard, fun z => ?_⟩
    obtain ⟨φ, hφ, hφord, hφtop, hAut, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        (F := QuadraticAlgebra K 1 ε) Nat.prime_two (by omega) hcard
    have hφn : ∀ (m : ℕ) (w : QuadraticAlgebra K 1 ε), (φ ^ m) w = w ^ 2 ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => intro w; rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ']
    have hφnord : orderOf (φ ^ n) = 2 := by
      rw [orderOf_pow_of_dvd (by omega) (by rw [hφord]; exact dvd_mul_left n 2), hφord,
        Nat.mul_div_cancel _ (by omega)]
    have : Finite (RingAut (QuadraticAlgebra K 1 ε)) :=
      Nat.finite_of_card_ne_zero (by rw [hAut]; omega)
    have : Fintype (RingAut (QuadraticAlgebra K 1 ε)) := Fintype.ofFinite _
    have : IsCyclic (RingAut (QuadraticAlgebra K 1 ε)) :=
      isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
    have h2dvd : 2 ∣ Fintype.card (RingAut (QuadraticAlgebra K 1 ε)) := by
      rw [← Nat.card_eq_fintype_card, hAut]
      exact dvd_mul_right 2 n
    obtain ⟨g, hg⟩ := Finset.card_eq_one.1
      ((IsCyclic.card_orderOf_eq_totient h2dvd).trans Nat.totient_two)
    have hmem : ∀ f : RingAut (QuadraticAlgebra K 1 ε), orderOf f = 2 → f = g := fun f hf =>
      Finset.mem_singleton.1 (hg ▸ Finset.mem_filter.2 ⟨Finset.mem_univ f, hf⟩)
    rw [← starRingAut_apply, hmem _ hord, ← hmem _ hφnord, hφn]

end CFSG.LinearAlgebra
