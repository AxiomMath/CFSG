module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseDecomposition
public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionOrbits
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsPowers

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatRelative

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.AdaptedBaseFusion

section Inversion

variable {A : Type*} [Group A] [Fintype A] {σ υ : A} {m : ℕ} [NeZero m] {ζ : ℂ}
  {lam : ZMod m → ZMod m → A →* ℂ}

theorem sum_multiplicity_mul_lam (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ) (u : A) :
    ∑ i : ZMod m, ∑ j : ZMod m,
      (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lam i j x)) * lam i j u = χ u := by
  have hterm : ∀ i j : ZMod m, (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lam i j x)) *
      lam i j u = (Nat.card A : ℂ)⁻¹ * ∑ x, χ x * lam i j (x⁻¹ * u) := by
    intro i j
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [conj_monoidHom_apply, mul_assoc, ← map_mul]
  have hcard : (Nat.card A : ℂ) = (m : ℂ) ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast card_eq_sq hc hgen hσ hυ hint hζ lam hlam
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  calc ∑ i : ZMod m, ∑ j : ZMod m,
        (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lam i j x)) * lam i j u
      = (Nat.card A : ℂ)⁻¹ * ∑ x, χ x * ∑ i : ZMod m, ∑ j : ZMod m, lam i j (x⁻¹ * u) := by
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
        simp only [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    _ = (Nat.card A : ℂ)⁻¹ * ∑ x, χ x * (if x⁻¹ * u = 1 then (m : ℂ) ^ 2 else 0) := by
        simp only [sum_indices_linearCharacter hc hgen hσ hυ hint hζ lam hlam]
    _ = χ u := by
        simp only [inv_mul_eq_one, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
        rw [hcard]
        field_simp

theorem eq_neg_of_multiplicity (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ) (κ : ℂ)
    (hκ : ∀ i j : ZMod m, (i, j) ≠ (0, 0) →
      (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lam i j x)) =
        (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lam 0 0 x)) + κ)
    {u : A} (hu : u ≠ 1) : χ u = -κ := by
  set t₀ := (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lam 0 0 x)) with ht₀
  have hsplit : ∀ i j : ZMod m,
      (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lam i j x)) * lam i j u =
        (t₀ + κ) * lam i j u - (if (i, j) = (0, 0) then κ else 0) * lam i j u := by
    intro i j
    by_cases h : (i, j) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
      rw [ite_eq_left h]
      ring
    · rw [hκ i j h, ite_eq_right h]
      ring
  have hone : ∑ i : ZMod m, ∑ j : ZMod m, (if (i, j) = (0, 0) then κ else 0) * lam i j u =
      κ := by
    rw [Finset.sum_eq_single (0 : ZMod m), Finset.sum_eq_single (0 : ZMod m),
      ite_eq_left rfl, lam_zero hc hgen lam hlam u, mul_one]
    · intro j _ hj
      rw [ite_eq_right fun h => hj (Prod.ext_iff.mp h).2, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => by
        rw [ite_eq_right fun h => hi (Prod.ext_iff.mp h).1, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have h := sum_multiplicity_mul_lam hc hgen hσ hυ hint hζ hlam χ u
  simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_indices_linearCharacter hc hgen hσ hυ hint hζ lam hlam u, ite_eq_right hu,
    mul_zero, zero_sub] at h
  rw [hone] at h
  exact h.symm

end Inversion

section Adapted

variable {G : Type} [Group G]

theorem adapted_facts [Finite G] {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (U : Subgroup G) (hU : U = modelBase S e) {σ υ : U} {g : G}
    (hA : IsAdaptedBase U (wreathModelHom S e (Original.a (2 ^ n)))
      (wreathModelHom S e (Original.z (2 ^ n))) σ υ g) :
    Commute σ υ ∧ Subgroup.closure ({σ, υ} : Set U) = ⊤ ∧ orderOf σ = 2 ^ n ∧
      orderOf υ = 2 ^ n ∧ Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥ := by
  subst hU
  exact ⟨commute_left_right hA, hA.closure_eq_top, orderOf_left' hA, orderOf_right' hA,
    zpowers_left_inf_right' hA⟩

theorem pow_not_isConj_inv [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {k : ℕ} (hk : k ∈ Finset.Ico 1 (2 ^ n)) (hkM : k ≠ 2 ^ n / 2) :
    ¬ IsConj (wreathModelHom S e (Original.a (2 ^ n)) ^ k)
      (wreathModelHom S e (Original.a (2 ^ n)) ^ k)⁻¹ := by
  intro hconj
  have ha := orderOf_wreathModelHom_a n S e
  have hk' := Finset.mem_Ico.mp hk
  have hinv : (wreathModelHom S e (Original.a (2 ^ n)) ^ k)⁻¹ =
      wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n - k) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add, show 2 ^ n - k + k = 2 ^ n by omega]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ha)
  rw [hinv] at hconj
  have h := ConditionalFourier.wreath_powers_eq_of_isConj n hn S e hk
    (Finset.mem_Ico.mpr ⟨Nat.sub_pos_of_lt hk'.2, Nat.sub_lt (Nat.two_pow_pos n) hk'.1⟩) hconj
  generalize 2 ^ n = m at h hk' hkM
  omega

end Adapted

end CFSG.Wreathed.FlatRelative
