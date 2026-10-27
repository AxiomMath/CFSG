module

public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasisDegreeSum

public noncomputable section

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical Matrix

universe u

theorem trace_cube_one_average_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (S : Module.End ℂ V) (hS : S * S * S = 1) :
    ∃ a : ℕ, ((Module.finrank ℂ V : ℂ) + LinearMap.trace ℂ V S +
      LinearMap.trace ℂ V (S * S)) / 3 = a := by
  set E : Module.End ℂ V := (3 : ℂ)⁻¹ • (1 + S + S * S) with hE
  have hsq : (1 + S + S * S) * (1 + S + S * S) = (3 : ℂ) • (1 + S + S * S) := by
    have h3 : S * (S * S) = 1 := by rw [← mul_assoc, hS]
    have h4 : S * S * (S * S) = S := by rw [← mul_assoc, hS, one_mul]
    simp only [add_mul, mul_add, one_mul, mul_one, h3, h4, hS]
    module
  have hidem : IsIdempotentElem E := by
    change E * E = E
    rw [hE, smul_mul_smul_comm, hsq, smul_smul]
    congr 1
    norm_num
  have htr := (LinearMap.IsIdempotentElem.isProj_range E hidem).trace
  refine ⟨Module.finrank ℂ (LinearMap.range E), ?_⟩
  rw [← htr, hE, map_smul, map_add, map_add, LinearMap.trace_one, smul_eq_mul]
  ring

theorem exists_complex_primitive_cube_root : ∃ ω : ℂ, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨s, hs⟩ := Complex.isSquare (-3)
  exact ⟨(-1 + s) / 2, by linear_combination (-1 / 4 : ℂ) * hs⟩

theorem order_three_character_coefficients {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (v : G) (hv : v ^ 3 = 1)
    (hreal : data.character v⁻¹ = data.character v) :
    ∃ a b : ℕ, (data.character 1 + 2 * data.character v) / 3 = a ∧
      (data.character 1 - data.character v) / 3 = b := by
  set T := data.representation v with hTdef
  have hT : T * T * T = 1 := by
    rw [hTdef, ← map_mul, ← map_mul, ← pow_three', hv, map_one]
  have hvv : v * v = v⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three', hv])
  have hsquare : LinearMap.trace ℂ data.vector (T * T) = data.character v := by
    rw [hTdef, ← map_mul, hvv]
    exact hreal
  have hone : data.character 1 = (Module.finrank ℂ data.vector : ℂ) :=
    Representation.char_one _
  have hchar : LinearMap.trace ℂ data.vector T = data.character v := rfl
  obtain ⟨a, ha⟩ := trace_cube_one_average_natural T hT
  obtain ⟨ω, hω⟩ := exists_complex_primitive_cube_root
  have hω3 : ω * ω * ω = 1 := by linear_combination (ω - 1) * hω
  have hS : (ω • T) * (ω • T) * (ω • T) = 1 := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hT, hω3, one_smul]
  obtain ⟨b, hb⟩ := trace_cube_one_average_natural (ω • T) hS
  refine ⟨a, b, ?_, ?_⟩
  · rw [← ha, hsquare, hchar, hone]
    ring
  · rw [← hb, smul_mul_smul_comm, map_smul, map_smul, hsquare, hchar, hone, smul_eq_mul,
      smul_eq_mul]
    linear_combination (-(data.character v) / 3) * hω

@[expose] def oddClassRestrictionBasis (K : Type u) [Group K] :
    Fin 2 → {g : K // Odd (orderOf g)} → ℂ :=
  ![fun _ => 1, fun g => if (g : K) = 1 then 2 else -1]

theorem single_order_three_odd_class_integral_restriction_basis {K : Type u} [Group K]
    [Fintype K] (basis : FiniteIrreducibleCharacterBasis K) (v : K) (hv : orderOf v = 3)
    (hconj : ∀ g : K, g ≠ 1 → Odd (orderOf g) → IsConj g v) :
    (∀ j, ∃ f : K → ℂ, (∀ g x : K, f (x * g * x⁻¹) = f g) ∧
      ∀ g : {g : K // Odd (orderOf g)}, f g = oddClassRestrictionBasis K j g) ∧
    LinearIndependent ℂ (oddClassRestrictionBasis K) ∧
    (∀ f : K → ℂ, (∀ g x : K, f (x * g * x⁻¹) = f g) →
      ∃ α : Fin 2 → ℂ, ∀ g : {g : K // Odd (orderOf g)},
        f g = ∑ j, α j * oddClassRestrictionBasis K j g) ∧
    (∀ θ, ∃ n : ℤ, (basis.representation θ).character v = n) ∧
    ∃ D : Matrix basis.index (Fin 2) ℤ,
      (∀ θ, (D θ 0 : ℂ) = ((basis.representation θ).character 1 +
          2 * (basis.representation θ).character v) / 3 ∧
        (D θ 1 : ℂ) = ((basis.representation θ).character 1 -
          (basis.representation θ).character v) / 3) ∧
      (∀ θ (α : Fin 2 → ℂ), (∀ g : {g : K // Odd (orderOf g)},
          (basis.representation θ).character g = ∑ j, α j * oddClassRestrictionBasis K j g) ↔
        ∀ j, α j = D θ j) ∧
      (Dᵀ * D).map (Int.cast : ℤ → ℚ) = (1 / 9 : ℚ) •
        !![(Nat.card K : ℚ) + 4 * Nat.card (Subgroup.centralizer {v}),
          (Nat.card K : ℚ) - 2 * Nat.card (Subgroup.centralizer {v});
          (Nat.card K : ℚ) - 2 * Nat.card (Subgroup.centralizer {v}),
          (Nat.card K : ℚ) + Nat.card (Subgroup.centralizer {v})] ∧
      (Nat.card K = 96 → Nat.card (Subgroup.centralizer {v}) = 12 →
        Dᵀ * D = !![16, 8; 8, 12]) := by
  have hv3 : v ^ 3 = 1 := hv ▸ pow_orderOf_eq_one v
  have hvne : v ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hv
    omega
  have hvodd : Odd (orderOf v) := by
    rw [hv]
    decide
  have honeodd : Odd (orderOf (1 : K)) := by
    rw [orderOf_one]
    exact odd_one
  have hclass : ∀ f : K → ℂ, (∀ g x : K, f (x * g * x⁻¹) = f g) →
      ∀ g : K, g ≠ 1 → Odd (orderOf g) → f g = f v := by
    intro f hf g hg hodd
    obtain ⟨x, hx⟩ := isConj_iff.mp (hconj g hg hodd)
    rw [← hx, hf]
  have hbasis (g : {g : K // Odd (orderOf g)}) (α : Fin 2 → ℂ) :
      ∑ j, α j * oddClassRestrictionBasis K j g =
        α 0 + α 1 * (if (g : K) = 1 then 2 else -1) := by
    simp [oddClassRestrictionBasis, Fin.sum_univ_two]
  have hθclass : ∀ θ, ∀ g x : K, (basis.representation θ).character (x * g * x⁻¹) =
      (basis.representation θ).character g := fun θ g x =>
    Representation.char_conj (basis.representation θ).representation g x
  have hinv : ∀ θ, (basis.representation θ).character v⁻¹ =
      (basis.representation θ).character v := fun θ =>
    hclass _ (hθclass θ) v⁻¹ (inv_ne_one.mpr hvne) (by rw [orderOf_inv]; exact hvodd)
  choose a b hab using fun θ =>
    order_three_character_coefficients (basis.representation θ) v hv3 (hinv θ)
  have hval : ∀ θ, (basis.representation θ).character v = (a θ : ℂ) - (b θ : ℂ) :=
    fun θ => by linear_combination (hab θ).1 - (hab θ).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨fun _ => 1, fun _ _ => rfl, fun _ => rfl⟩
    · refine ⟨fun g => if g = 1 then 2 else -1, ?_, fun _ => rfl⟩
      intro g x
      simp only [conj_eq_one_iff]
  · unfold oddClassRestrictionBasis
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrFun hst ⟨1, honeodd⟩
    have h2 := congrFun hst ⟨v, hvodd⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ite_eq_left, ite_eq_right hvne,
      Pi.zero_apply, mul_one] at h1 h2
    constructor
    · linear_combination (1 / 3 : ℂ) * h1 + (2 / 3 : ℂ) * h2
    · linear_combination (1 / 3 : ℂ) * h1 - (1 / 3 : ℂ) * h2
  · intro f hf
    refine ⟨![(f 1 + 2 * f v) / 3, (f 1 - f v) / 3], ?_⟩
    rintro ⟨g, hg⟩
    rw [hbasis]
    by_cases hg1 : g = 1
    · subst hg1
      simp
      ring
    · rw [ite_eq_right hg1, hclass f hf g hg1 hg]
      simp
      ring
  · intro θ
    exact ⟨(a θ : ℤ) - b θ, by push_cast; exact hval θ⟩
  let D : Matrix basis.index (Fin 2) ℤ := Matrix.of fun θ => ![(a θ : ℤ), (b θ : ℤ)]
  have hD0 : ∀ θ, (D θ 0 : ℂ) = 1 / 3 * (basis.representation θ).character 1 +
      2 / 3 * (basis.representation θ).character v := fun θ => by
    simp only [D, Matrix.of_apply, Matrix.cons_val_zero, Int.cast_natCast]
    linear_combination -(hab θ).1
  have hD1 : ∀ θ, (D θ 1 : ℂ) = 1 / 3 * (basis.representation θ).character 1 +
      -1 / 3 * (basis.representation θ).character v := fun θ => by
    simp only [D, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.cast_natCast]
    linear_combination -(hab θ).2
  have hS11 := finiteIrreducibleCharacterBasis_sum_degree_sq basis
  have hS12 := complete_regular_character_sum basis v hvne
  have hS22 : ∑ θ, (basis.representation θ).character v ^ 2 =
      (Nat.card (Subgroup.centralizer {v}) : ℂ) := by
    rw [← conjugatorCount_self, ← complete_character_column_sum basis v v]
    exact Finset.sum_congr rfl fun θ _ => by rw [hinv θ, sq]
  have hquad (p q r s : ℂ) : ∑ θ, (p * (basis.representation θ).character 1 +
      q * (basis.representation θ).character v) * (r * (basis.representation θ).character 1 +
      s * (basis.representation θ).character v) =
      p * r * Nat.card K + q * s * Nat.card (Subgroup.centralizer {v}) := by
    rw [← hS11, ← hS22, ← add_zero (p * r * _), ← mul_zero (p * s + q * r), ← hS12,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun θ _ => by ring
  have hgram : (Dᵀ * D).map (Int.cast : ℤ → ℚ) = (1 / 9 : ℚ) •
      !![(Nat.card K : ℚ) + 4 * Nat.card (Subgroup.centralizer {v}),
        (Nat.card K : ℚ) - 2 * Nat.card (Subgroup.centralizer {v});
        (Nat.card K : ℚ) - 2 * Nat.card (Subgroup.centralizer {v}),
        (Nat.card K : ℚ) + Nat.card (Subgroup.centralizer {v})] := by
    ext i j
    apply Rat.cast_injective (α := ℂ)
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', smul_eq_mul, Fin.zero_eta, Fin.mk_one,
        Fin.isValue] <;>
      push_cast <;>
      simp only [hD0, hD1, hquad] <;>
      ring
  refine ⟨D, fun θ => ⟨?_, ?_⟩, ?_, hgram, ?_⟩
  · rw [hD0]
    ring
  · rw [hD1]
    ring
  · intro θ α
    constructor
    · intro hα
      have h1 := hα ⟨1, honeodd⟩
      have h2 := hα ⟨v, hvodd⟩
      rw [hbasis] at h1 h2
      simp only [ite_eq_left, ite_eq_right hvne] at h1 h2
      intro j
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue]
        rw [hD0]
        linear_combination (-1 / 3 : ℂ) * h1 + (-2 / 3 : ℂ) * h2
      · simp only [Fin.mk_one, Fin.isValue]
        rw [hD1]
        linear_combination (-1 / 3 : ℂ) * h1 + (1 / 3 : ℂ) * h2
    · intro hα g
      rw [hbasis, hα 0, hα 1, hD0, hD1]
      by_cases hg1 : (g : K) = 1
      · rw [ite_eq_left hg1, hg1]
        ring
      · rw [ite_eq_right hg1, hclass _ (hθclass θ) g hg1 g.2]
        ring
  · intro hM hc
    ext i j
    have hij := congrFun (congrFun hgram i) j
    rw [hM, hc] at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> exact_mod_cast hij

end CFSG.Wreathed
