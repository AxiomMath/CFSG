module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
import CFSG.FeitThompson.Representations.SchurLemmaAlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem Representation.norm_character_eq_finrank_of_mem_center [Finite K]
    (ρ : Representation ℂ K V) [ρ.IsIrreducible] {z : K} (hz : z ∈ Subgroup.center K) :
    ‖ρ.character z‖ = (finrank ℂ V : ℝ) := by
  have hnt : Nontrivial V := Representation.nontrivial_of_isIrreducible ρ inferInstance
  have hcomm : ∀ g : K, Commute (ρ z) (ρ g) := by
    intro g
    have h1 : Commute z g := (Subgroup.mem_center_iff.mp hz g).symm
    exact h1.map ρ
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_eq_smul_one_of_commute ρ (ρ z) hcomm
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hev : Module.End.HasEigenvalue (ρ z) c :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by rw [hc]; simp), hv⟩
  have hnorm : ‖c‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one
      (Representation.pow_orderOf_eq_one_of_hasEigenvalue ρ hev)
      (isOfFinOrder_of_finite z).orderOf_pos.ne'
  have htr : ρ.character z = c * (finrank ℂ V : ℂ) := by
    rw [Representation.character, hc, map_smul, LinearMap.trace_one]; simp
  rw [htr, norm_mul, hnorm, one_mul, Complex.norm_natCast]

theorem sum_norm_sq_character_of_isIrreducible [Fintype K] (ρ : Representation ℂ K V)
    [ρ.IsIrreducible] : ∑ k : K, ‖ρ.character k‖ ^ 2 = (Nat.card K : ℝ) := by
  classical
  have h : cfInner ρ.character ρ.character = 1 := by
    rw [cfInner_character_character ρ ρ, if_pos ⟨Representation.Equiv.refl ρ⟩]
  rw [cfInner_self_eq_sum_norm_sq] at h
  have hK : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.card_pos (α := K)).ne'
  have h2 : ∑ k : K, ((‖ρ.character k‖ : ℂ)) ^ 2 = (Nat.card K : ℂ) := by
    field_simp at h
    linear_combination h
  have h3 : ((∑ k : K, ‖ρ.character k‖ ^ 2 : ℝ) : ℂ) = ((Nat.card K : ℝ) : ℂ) := by
    push_cast; exact h2
  exact Complex.ofReal_inj.1 h3

theorem Representation.finrank_sq_le_index_of_le_center [Finite K] (ρ : Representation ℂ K V)
    [ρ.IsIrreducible] {Z : Subgroup K} (hZ : Z ≤ Subgroup.center K) :
    finrank ℂ V ^ 2 ≤ Z.index := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set n : ℕ := finrank ℂ V with hn
  have hcen : ∀ z ∈ (Z : Set K).toFinset, ‖ρ.character z‖ ^ 2 = (n : ℝ) ^ 2 := by
    intro z hz
    rw [Representation.norm_character_eq_finrank_of_mem_center ρ (hZ (by simpa using hz))]
  have hle : ∑ z ∈ (Z : Set K).toFinset, ‖ρ.character z‖ ^ 2 ≤ ∑ k : K, ‖ρ.character k‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => by positivity
  rw [Finset.sum_congr rfl hcen, Finset.sum_const, nsmul_eq_mul,
    show ((Z : Set K).toFinset).card = Nat.card Z by
      simp [Set.toFinset_card, Nat.card_eq_fintype_card],
    sum_norm_sq_character_of_isIrreducible ρ,
    show (Nat.card K : ℝ) = (Z.index : ℝ) * (Nat.card Z : ℝ) by
      rw [← Nat.cast_mul, Subgroup.index_mul_card]] at hle
  have hZpos : (0 : ℝ) < Nat.card Z := by exact_mod_cast Nat.card_pos
  have : (n : ℝ) ^ 2 ≤ (Z.index : ℝ) := le_of_mul_le_mul_right (by linarith [hle]) hZpos
  exact_mod_cast this

theorem norm_apply_one_sq_le_index_of_le_center [Finite K] {θ : K → ℂ} (hθ : θ ∈ Irr K)
    {Z : Subgroup K} (hZ : Z ≤ Subgroup.center K) : ‖θ 1‖ ^ 2 ≤ (Z.index : ℝ) := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hθ
  have := hW
  have h1 : ‖FDRep.character W 1‖ = (finrank ℂ W.V : ℝ) := by rw [W.char_one]; simp
  rw [h1]
  exact_mod_cast Representation.finrank_sq_le_index_of_le_center (V := W.V) W.ρ hZ

theorem exists_degree_eq_and_sq_le_index_of_le_center [Finite K] {θ : K → ℂ} (hθ : θ ∈ Irr K)
    {Z : Subgroup K} (hZ : Z ≤ Subgroup.center K) :
    ∃ n : ℕ, θ 1 = n ∧ n ^ 2 ≤ Z.index := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hθ
  have := hW
  exact ⟨finrank ℂ W.V, W.char_one,
    Representation.finrank_sq_le_index_of_le_center (V := W.V) W.ρ hZ⟩

end CFSG.FeitThompson
