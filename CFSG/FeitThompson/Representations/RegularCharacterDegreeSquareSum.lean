module

public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped ComplexConjugate

variable {G : Type*} [Group G]

noncomputable section

omit [Group G] in
theorem finrank_monoidAlgebra [Monoid G] [Finite G] :
    finrank ℂ (MonoidAlgebra ℂ G) = Nat.card G := by
  have : Fintype G := Fintype.ofFinite G
  rw [finrank_eq_card_basis (MonoidAlgebra.basis G ℂ), Nat.card_eq_fintype_card]

private theorem toMatrix_leftRegular_diag [Fintype G] [DecidableEq G] (g x : G) :
    LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
        (Representation.leftRegular ℂ G g) x x = if g = 1 then (1 : ℂ) else 0 := by
  set b := MonoidAlgebra.basis G ℂ with hb
  rw [LinearMap.toMatrix_apply]
  have hbx : b x = MonoidAlgebra.single x (1 : ℂ) := MonoidAlgebra.basis_apply ℂ x
  rw [hbx, Representation.ofMulAction_single]
  have hgx : (g • x) = g * x := rfl
  rw [hgx, ← MonoidAlgebra.basis_apply (R := G) ℂ (g * x), ← hb, b.repr_self_apply]
  by_cases hg : g = 1
  · simp [hg]
  · rw [if_neg hg, if_neg]
    intro h
    exact hg (mul_right_cancel (b := x) (by rw [h, one_mul]))

theorem leftRegular_character_one [Finite G] :
    (Representation.leftRegular ℂ G).character 1 = (Nat.card G : ℂ) := by
  have : Fintype G := Fintype.ofFinite G
  rw [Representation.char_one, finrank_monoidAlgebra]

theorem leftRegular_character_of_ne_one [Finite G] {g : G} (hg : g ≠ 1) :
    (Representation.leftRegular ℂ G).character g = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  simp only [Matrix.diag_apply, toMatrix_leftRegular_diag, if_neg hg, Finset.sum_const_zero]

theorem leftRegular_character_apply [Finite G] [DecidableEq G] (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Nat.card G : ℂ) else 0 := by
  by_cases hg : g = 1
  · subst hg; rw [if_pos rfl, leftRegular_character_one]
  · rw [if_neg hg, leftRegular_character_of_ne_one hg]

theorem Irr.conj_character_one [Finite G] {χ : G → ℂ} (hχ : χ ∈ Irr G) : conj (χ 1) = χ 1 := by
  obtain ⟨n, -, hn, -⟩ := Irr.exists_degree hχ
  rw [hn, Complex.conj_natCast]

theorem cfInner_leftRegular_character [Fintype G] (χ : G → ℂ) :
    cfInner (Representation.leftRegular ℂ G).character χ = conj (χ 1) := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_ne_zero]
  rw [cfInner_def, Finset.sum_eq_single_of_mem (1 : G) (Finset.mem_univ _)]
  · rw [leftRegular_character_one, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  · intro g _ hg
    rw [leftRegular_character_of_ne_one hg, zero_mul]

theorem leftRegular_character_eq_sum [Finite G] :
    (Representation.leftRegular ℂ G).character
      = ∑ χ : irrFinset G, ((χ : G → ℂ) 1) • (χ : G → ℂ) := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul (Representation.leftRegular ℂ G)
  rw [hm]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have h1 : ((m χ : ℂ)) = (χ : G → ℂ) 1 := by
    rw [← cfInner_eq_multiplicity hm χ, cfInner_leftRegular_character,
      Irr.conj_character_one (mem_irrFinset.1 χ.2)]
  rw [h1]

theorem sum_character_one_sq [Finite G] :
    ∑ χ : irrFinset G, ((χ : G → ℂ) 1) ^ 2 = (Nat.card G : ℂ) := by
  have h := congrFun leftRegular_character_eq_sum (1 : G)
  rw [leftRegular_character_one] at h
  rw [h, Finset.sum_apply]
  exact Finset.sum_congr rfl fun χ _ => by simp [sq]

theorem sum_character_one_sq' [Finite G] :
    ∑ χ ∈ irrFinset G, (χ 1) ^ 2 = (Nat.card G : ℂ) := by
  rw [← Finset.sum_coe_sort (irrFinset G) fun χ : G → ℂ => (χ 1) ^ 2]
  exact sum_character_one_sq

theorem exists_degree_sum_sq_eq_card [Finite G] :
    ∃ d : irrFinset G → ℕ, (∀ χ : irrFinset G, (χ : G → ℂ) 1 = (d χ : ℂ)) ∧
      ∑ χ : irrFinset G, d χ ^ 2 = Nat.card G := by
  classical
  choose d hdpos hdeq hddvd using fun χ : irrFinset G => Irr.exists_degree (mem_irrFinset.1 χ.2)
  refine ⟨d, hdeq, ?_⟩
  have hcast : ((∑ χ : irrFinset G, d χ ^ 2 : ℕ) : ℂ) = ((Nat.card G : ℕ) : ℂ) := by
    push_cast
    rw [← sum_character_one_sq (G := G)]
    exact (Finset.sum_congr rfl fun χ _ => by rw [hdeq χ]).symm
  exact Nat.cast_injective hcast

end

end CFSG.FeitThompson
