module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Data
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*}

@[expose] def rowFiber (B : Finset ι) (row : ι → LyonsRow) (R : LyonsRow) : Finset ι :=
  B.filter fun χ => row χ = R

theorem mem_rowFiber {B : Finset ι} {row : ι → LyonsRow} {R : LyonsRow} {χ : ι} :
    χ ∈ rowFiber B row R ↔ χ ∈ B ∧ row χ = R := by
  simp [rowFiber]

theorem sum_eq_sum_rowFiber {β : Type*} [AddCommMonoid β] (B : Finset ι) (row : ι → LyonsRow)
    (F : ι → β) :
    ∑ χ ∈ B, F χ = ∑ R ∈ (B.val.map row).toFinset, ∑ χ ∈ rowFiber B row R, F χ := by
  symm
  unfold rowFiber
  apply Finset.sum_fiberwise_of_maps_to
  intro χ hχ
  simp only [Multiset.mem_toFinset, Multiset.mem_map]
  exact ⟨χ, hχ, rfl⟩

theorem card_rowFiber (B : Finset ι) (row : ι → LyonsRow) (R : LyonsRow) :
    (rowFiber B row R).card = (B.val.map row).count R := by
  rw [Multiset.count_map, rowFiber, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun χ _ => eq_comm

theorem exists_unique_of_count_eq_one {B : Finset ι} {row : ι → LyonsRow} {R : LyonsRow}
    (h : (B.val.map row).count R = 1) :
    ∃ χ ∈ B, row χ = R ∧ ∀ ψ ∈ B, row ψ = R → ψ = χ := by
  rw [← card_rowFiber] at h
  obtain ⟨χ, hχ⟩ := Finset.card_eq_one.mp h
  have hmem : χ ∈ rowFiber B row R := by rw [hχ]; exact Finset.mem_singleton_self χ
  refine ⟨χ, (mem_rowFiber.mp hmem).1, (mem_rowFiber.mp hmem).2, fun ψ hψ hψR => ?_⟩
  have : ψ ∈ rowFiber B row R := mem_rowFiber.mpr ⟨hψ, hψR⟩
  rw [hχ] at this
  exact Finset.mem_singleton.mp this

theorem rowFiber_eq_singleton {B : Finset ι} {row : ι → LyonsRow} {R : LyonsRow} {χ : ι}
    (hχ : χ ∈ B) (hR : row χ = R) (huniq : ∀ ψ ∈ B, row ψ = R → ψ = χ) :
    rowFiber B row R = {χ} := by
  ext ψ
  rw [mem_rowFiber, Finset.mem_singleton]
  constructor
  · rintro ⟨hψ, hψR⟩
    exact huniq ψ hψ hψR
  · rintro rfl
    exact ⟨hχ, hR⟩

theorem rowFiber_eq_triple [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {R : LyonsRow}
    {p : ι}
    (hp : p ∈ B) (hpR : row p = R) (h : (B.val.map row).count R = 3) :
    ∃ χ₁ χ₂, χ₁ ≠ p ∧ χ₂ ≠ p ∧ χ₁ ≠ χ₂ ∧ rowFiber B row R = {p, χ₁, χ₂} := by
  rw [← card_rowFiber] at h
  have hpmem : p ∈ rowFiber B row R := mem_rowFiber.mpr ⟨hp, hpR⟩
  have herase : ((rowFiber B row R).erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hpmem, h]
  obtain ⟨χ₁, χ₂, hne, heq⟩ := Finset.card_eq_two.mp herase
  have h1 : χ₁ ∈ (rowFiber B row R).erase p := by rw [heq]; simp
  have h2 : χ₂ ∈ (rowFiber B row R).erase p := by rw [heq]; simp
  refine ⟨χ₁, χ₂, Finset.ne_of_mem_erase h1, Finset.ne_of_mem_erase h2, hne, ?_⟩
  rw [← Finset.insert_erase hpmem, heq]

theorem rowFiber_eq_pair_principal [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow}
    {R : LyonsRow} {p : ι}
    (hp : p ∈ B) (hpR : row p = R) (h : (B.val.map row).count R = 2) :
    ∃ χ₁, χ₁ ≠ p ∧ rowFiber B row R = {p, χ₁} := by
  rw [← card_rowFiber] at h
  have hpmem : p ∈ rowFiber B row R := mem_rowFiber.mpr ⟨hp, hpR⟩
  have herase : ((rowFiber B row R).erase p).card = 1 := by
    rw [Finset.card_erase_of_mem hpmem, h]
  obtain ⟨χ₁, heq⟩ := Finset.card_eq_one.mp herase
  have h1 : χ₁ ∈ (rowFiber B row R).erase p := by rw [heq]; simp
  refine ⟨χ₁, Finset.ne_of_mem_erase h1, ?_⟩
  rw [← Finset.insert_erase hpmem, heq]

theorem rowFiber_eq_pair [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {R : LyonsRow}
    (h : (B.val.map row).count R = 2) :
    ∃ χ₁ χ₂, χ₁ ≠ χ₂ ∧ rowFiber B row R = {χ₁, χ₂} := by
  rw [← card_rowFiber] at h
  exact Finset.card_eq_two.mp h

theorem degree_rotate_eq {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ}
    (τ : ι → ι) (hτ : Set.BijOn τ B B) (hτrow : ∀ χ ∈ B, row (τ χ) = (row χ).rotate ∧
      f (τ χ) = f χ) {χ ψ : ι} (hχ : χ ∈ B) (hrot : row ψ = (row χ).rotate)
    (huniq : ∀ φ ∈ B, row φ = row ψ → φ = ψ) : f ψ = f χ := by
  have hτχ : τ χ = ψ := huniq (τ χ) (hτ.mapsTo hχ) ((hτrow χ hχ).1.trans hrot.symm)
  rw [← hτχ, (hτrow χ hχ).2]

theorem toFinset_lyonsConfiguration (c : LyonsLabel) :
    (lyonsConfiguration c).toFinset = (c.rows.map Prod.fst).toFinset := by
  cases c <;> decide

theorem nodup_rows (c : LyonsLabel) : (c.rows.map Prod.fst).Nodup := by
  cases c <;> decide

theorem sum_mul_row_eq {β : Type*} [CommSemiring β] {B : Finset ι} {row : ι → LyonsRow}
    {c : LyonsLabel} (hM : B.val.map row = lyonsConfiguration c) (G : LyonsRow → β)
    (H : ι → β) :
    ∑ χ ∈ B, G (row χ) * H χ =
      ((c.rows.map Prod.fst).map fun R => G R * ∑ χ ∈ rowFiber B row R, H χ).sum := by
  rw [sum_eq_sum_rowFiber B row, hM, toFinset_lyonsConfiguration,
    List.sum_toFinset _ (nodup_rows c)]
  congr 1
  refine List.map_congr_left fun R _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [(mem_rowFiber.mp hχ).2]

theorem sum_rowFiber_rotate {β : Type*} [AddCommMonoid β] {B : Finset ι} {row : ι → LyonsRow}
    {f : ι → ℤ} (τ : ι → ι) (hτ : Set.BijOn τ B B)
    (hτrow : ∀ χ ∈ B, row (τ χ) = (row χ).rotate ∧ f (τ χ) = f χ) (R : LyonsRow)
    (g : ℤ → β) :
    ∑ ψ ∈ rowFiber B row R.rotate, g (f ψ) = ∑ χ ∈ rowFiber B row R, g (f χ) := by
  symm
  refine Finset.sum_nbij τ (fun χ hχ => ?_) (fun χ₁ h₁ χ₂ h₂ h => ?_) (fun ψ hψ => ?_)
    (fun χ hχ => ?_)
  · obtain ⟨hχB, hχR⟩ := mem_rowFiber.mp hχ
    exact mem_rowFiber.mpr ⟨hτ.mapsTo hχB, by rw [(hτrow χ hχB).1, hχR]⟩
  · exact hτ.injOn (mem_rowFiber.mp h₁).1 (mem_rowFiber.mp h₂).1 h
  · obtain ⟨hψB, hψR⟩ := mem_rowFiber.mp hψ
    obtain ⟨χ, hχB, rfl⟩ := hτ.surjOn hψB
    refine ⟨χ, mem_rowFiber.mpr ⟨hχB, ?_⟩, rfl⟩
    rw [(hτrow χ hχB).1] at hψR
    exact LyonsRow.rotate_injective hψR
  · rw [(hτrow χ (mem_rowFiber.mp hχ).1).2]

end CFSG.LyonsUnitaryFour
