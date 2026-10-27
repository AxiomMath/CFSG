module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Representations.SymmetricAlternatingSquareCharacters
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped ComplexConjugate

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

noncomputable def frobeniusSchurIndicator [Fintype G] (χ : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, χ (g ^ 2)

theorem frobeniusSchurIndicator_def [Fintype G] (χ : G → ℂ) :
    frobeniusSchurIndicator χ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, χ (g ^ 2) := (rfl)

section

variable [Fintype G]

theorem frobeniusSchurIndicator_add (χ ψ : G → ℂ) :
    frobeniusSchurIndicator (χ + ψ) =
      frobeniusSchurIndicator χ + frobeniusSchurIndicator ψ := by
  simp only [frobeniusSchurIndicator_def, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem frobeniusSchurIndicator_smul (c : ℂ) (χ : G → ℂ) :
    frobeniusSchurIndicator (c • χ) = c * frobeniusSchurIndicator χ := by
  simp only [frobeniusSchurIndicator_def, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem frobeniusSchurIndicator_one : frobeniusSchurIndicator (1 : G → ℂ) = 1 := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [frobeniusSchurIndicator_def]
  simp [Nat.card_eq_fintype_card, Finset.card_univ, hcard]

omit [Group G] in
theorem cfInner_one_right (f : G → ℂ) :
    cfInner f (1 : G → ℂ) = (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g := by
  simp [cfInner_def]

variable [FiniteDimensional ℂ V]

theorem frobeniusSchurIndicator_character_eq_cfInner_sub (ρ : Representation ℂ G V) :
    frobeniusSchurIndicator ρ.character =
      cfInner (Representation.symmetricSquare ρ).toRepresentation.character (1 : G → ℂ) -
        cfInner (Representation.alternatingSquare ρ).toRepresentation.character (1 : G → ℂ) := by
  rw [cfInner_one_right, cfInner_one_right, ← mul_sub, ← Finset.sum_sub_distrib,
    frobeniusSchurIndicator_def]
  congr 1
  exact Finset.sum_congr rfl fun g _ =>
    (Representation.character_symmetricSquare_sub_alternatingSquare
      (by norm_num : (2 : ℂ) ≠ 0) ρ g).symm

theorem frobeniusSchurIndicator_character (ρ : Representation ℂ G V) :
    frobeniusSchurIndicator ρ.character =
      (finrank ℂ (Representation.symmetricSquare ρ).toRepresentation.invariants : ℂ) -
        (finrank ℂ (Representation.alternatingSquare ρ).toRepresentation.invariants : ℂ) := by
  have : Invertible ((Nat.card G : ℂ)) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  rw [← Representation.card_inv_mul_sum_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_eq_finrank,
    frobeniusSchurIndicator_character_eq_cfInner_sub, cfInner_one_right, cfInner_one_right]

theorem add_finrank_invariants_eq_cfInner (ρ : Representation ℂ G V) :
    (finrank ℂ (Representation.symmetricSquare ρ).toRepresentation.invariants : ℂ) +
        (finrank ℂ (Representation.alternatingSquare ρ).toRepresentation.invariants : ℂ)
      = cfInner ρ.character (fun g => conj (ρ.character g)) := by
  have : Invertible ((Nat.card G : ℂ)) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  rw [← Representation.card_inv_mul_sum_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_eq_finrank, ← mul_add, ← Finset.sum_add_distrib,
    cfInner_def]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.character_symmetricSquare_add_alternatingSquare
      (by norm_num : (2 : ℂ) ≠ 0) ρ g, Complex.conj_conj, sq]

end

section

variable [Fintype G]

theorem exists_frobeniusSchurIndicator_eq_sub {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ a b : ℕ, frobeniusSchurIndicator χ = (a : ℂ) - (b : ℂ) ∧
      a + b = if χ = fun g => conj (χ g) then 1 else 0 := by
  classical
  obtain ⟨X, hXirr, rfl⟩ := mem_Irr.1 hχ
  rw [fdRepCharacter_eq]
  refine ⟨finrank ℂ (Representation.symmetricSquare X.ρ).toRepresentation.invariants,
    finrank ℂ (Representation.alternatingSquare X.ρ).toRepresentation.invariants,
    frobeniusSchurIndicator_character X.ρ, ?_⟩
  have hconj : (fun g => conj (Representation.character X.ρ g)) ∈ Irr G := by
    rw [← fdRepCharacter_eq]
    exact conj_mem_Irr hχ
  have h := add_finrank_invariants_eq_cfInner X.ρ
  rw [cfInner_eq_ite_of_mem_Irr (by rw [← fdRepCharacter_eq]; exact hχ) hconj] at h
  have hc : ((finrank ℂ (Representation.symmetricSquare X.ρ).toRepresentation.invariants +
      finrank ℂ (Representation.alternatingSquare X.ρ).toRepresentation.invariants : ℕ) : ℂ)
      = ((if Representation.character X.ρ = fun g => conj (Representation.character X.ρ g) then 1
        else 0 : ℕ) : ℂ) := by
    push_cast
    rw [h]
  exact Nat.cast_inj.1 hc

theorem frobeniusSchurIndicator_eq_zero_or_one_or_neg_one {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    frobeniusSchurIndicator χ = 0 ∨ frobeniusSchurIndicator χ = 1 ∨
      frobeniusSchurIndicator χ = -1 := by
  classical
  obtain ⟨a, b, hν, hab⟩ := exists_frobeniusSchurIndicator_eq_sub hχ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (le_trans (Nat.le_add_right a b)
      (by split at hab <;> omega)) with ha | ha
  · rcases (show b = 0 ∨ b = 1 by split at hab <;> omega) with hb | hb
    · exact Or.inl (by simp [hν, ha, hb])
    · exact Or.inr (Or.inr (by simp [hν, ha, hb]))
  · exact Or.inr (Or.inl (by simp [hν, ha, show b = 0 by split at hab <;> omega]))

theorem frobeniusSchurIndicator_eq_zero_iff {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    frobeniusSchurIndicator χ = 0 ↔ χ ≠ fun g => conj (χ g) := by
  classical
  obtain ⟨a, b, hν, hab⟩ := exists_frobeniusSchurIndicator_eq_sub hχ
  constructor
  · intro h0 hreal
    rw [if_pos hreal] at hab
    rw [h0] at hν
    have : a = b := Nat.cast_inj.1 (sub_eq_zero.1 hν.symm)
    omega
  · intro hne
    rw [if_neg hne] at hab
    simp [hν, show a = 0 by omega, show b = 0 by omega]

theorem frobeniusSchurIndicator_eq_zero_iff_not_forall_im_eq_zero {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    frobeniusSchurIndicator χ = 0 ↔ ¬ ∀ g, (χ g).im = 0 := by
  rw [frobeniusSchurIndicator_eq_zero_iff hχ, ne_eq, funext_iff, not_iff_not]
  exact forall_congr' fun g => by rw [eq_comm, Complex.conj_eq_iff_im]

theorem frobeniusSchurIndicator_ne_zero_iff {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    frobeniusSchurIndicator χ ≠ 0 ↔ ∀ g, (χ g).im = 0 := by
  rw [ne_eq, frobeniusSchurIndicator_eq_zero_iff_not_forall_im_eq_zero hχ, not_not]

end

end CFSG.FeitThompson
