module

public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Nat.Totient

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

variable {k : Type*} [Field k]

theorem finrank_splittingField_le_two {h : k[X]} (hmon : h.Monic) (hdeg : h.natDegree = 2) :
    Module.finrank k h.SplittingField ≤ 2 := by
  by_cases hroot : ∃ x : k, h.IsRoot x
  ·
    obtain ⟨x, hx⟩ := hroot
    have hs : h.Splits := Polynomial.Splits.of_natDegree_eq_two hdeg hx
    have h1 : (⊥ : Subalgebra k h.SplittingField) = ⊤ :=
      ((IsSplittingField.splits_iff (L := h.SplittingField) h).mp hs).symm
    have h2 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp h1
    omega
  ·
    have hirr : Irreducible h := by
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · simp [hdeg]
      · intro x hx; exact hroot ⟨x, hx⟩
    have : Fact (Irreducible h) := ⟨hirr⟩
    have hne : h ≠ 0 := hmon.ne_zero
    have : Module.Finite k (AdjoinRoot h) := (AdjoinRoot.powerBasis hne).finite
    have hrank : Module.finrank k (AdjoinRoot h) = 2 := by
      rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
    have hsplits : (h.map (algebraMap k (AdjoinRoot h))).Splits := by
      refine Polynomial.Splits.of_natDegree_eq_two (x := AdjoinRoot.root h) ?_ ?_
      · rw [hmon.natDegree_map, hdeg]
      · have := AdjoinRoot.isRoot_root h
        rwa [AdjoinRoot.algebraMap_eq]
    let φ : h.SplittingField →ₐ[k] AdjoinRoot h :=
      IsSplittingField.lift h.SplittingField h hsplits
    have := LinearMap.finrank_le_finrank_of_injective
      (f := φ.toLinearMap) φ.toRingHom.injective
    omega

theorem exists_eq_mul_linear_splittingField {h : k[X]} (hmon : h.Monic)
    (hdeg : h.natDegree = 2) : ∃ a b : h.SplittingField,
      h.map (algebraMap k h.SplittingField) = (X - C a) * (X - C b) := by
  set H := h.map (algebraMap k h.SplittingField) with hH
  have hs : H.Splits := IsSplittingField.splits _ h
  have hHm : H.Monic := hmon.map _
  have hHd : H.natDegree = 2 := by rw [hH, hmon.natDegree_map, hdeg]
  have hcard : Multiset.card H.roots = 2 := by rw [← hs.natDegree_eq_card_roots, hHd]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨a, b, ?_⟩
  rw [hs.eq_prod_roots_of_monic hHm, hab]
  simp

theorem natCard_splittingField_eq_or [Finite k] {h : k[X]} (hmon : h.Monic)
    (hdeg : h.natDegree = 2) :
    Nat.card h.SplittingField = Nat.card k ∨
      Nat.card h.SplittingField = Nat.card k ^ 2 := by
  have hfd : FiniteDimensional k h.SplittingField := IsSplittingField.finiteDimensional _ h
  have hle := finrank_splittingField_le_two hmon hdeg
  have hpos : 0 < Module.finrank k h.SplittingField := Module.finrank_pos
  have hcard := Module.natCard_eq_pow_finrank (K := k) (V := h.SplittingField)
  interval_cases hr : Module.finrank k h.SplittingField
  · left; simpa [hr] using hcard
  · right; simpa [hr] using hcard

theorem exists_finiteField_natCard_eq_or_and_eq_mul_linear (k : Type u) [Field k] [Finite k]
    {h : k[X]} (hmon : h.Monic) (hdeg : h.natDegree = 2) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Finite E),
      Function.Injective (algebraMap k E) ∧
      (Nat.card E = Nat.card k ∨ Nat.card E = Nat.card k ^ 2) ∧
      ∃ a b : E, h.map (algebraMap k E) = (X - C a) * (X - C b) :=
  ⟨h.SplittingField, inferInstance, inferInstance, inferInstance,
    FaithfulSMul.algebraMap_injective _ _, natCard_splittingField_eq_or hmon hdeg,
    exists_eq_mul_linear_splittingField hmon hdeg⟩

end CFSG.FeitThompson
