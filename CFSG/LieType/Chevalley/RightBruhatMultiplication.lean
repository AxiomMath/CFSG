module

public import CFSG.LieType.Chevalley.SimpleBruhatMultiplication
public import CFSG.LieType.Chevalley.BorelWeylIntersection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem canonicalRep_inv_eq
    (w : WeylGroup τ) :
    ∃ k ∈ torusGroup τ K, (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      k * canonicalRep (coxeterSystem τ) K w⁻¹ := by
  obtain ⟨k₀, hk₀, h₀⟩ := canonicalRep_mul_mem (R := K) w⁻¹ w
  rw [inv_mul_cancel, canonicalRep_one, mul_one] at h₀
  refine ⟨k₀⁻¹, inv_mem hk₀, ?_⟩
  rw [eq_inv_mul_iff_mul_eq, ← h₀, mul_assoc, mul_inv_cancel, mul_one]

theorem bruhatCell_inv_subset
    (w : WeylGroup τ) :
    (bruhatCell τ K w)⁻¹ ⊆ bruhatCell τ K w⁻¹ := fun x hx => by
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 (Set.mem_inv.1 hx)
  obtain ⟨k, hk, hkn⟩ := canonicalRep_inv_eq (K := K) w
  refine mem_bruhatCell.2 ⟨b'⁻¹ * k, mul_mem (inv_mem hb') (torusGroup_le_borelGroup hk), b⁻¹,
    inv_mem hb, ?_⟩
  rw [← inv_inv x, ← hbb, mul_inv_rev, mul_inv_rev, hkn]
  group

theorem bruhatCell_inv
    (w : WeylGroup τ) : (bruhatCell τ K w)⁻¹ = bruhatCell τ K w⁻¹ := by
  refine Set.Subset.antisymm (bruhatCell_inv_subset w) (Set.inv_subset.1 ?_)
  simpa using bruhatCell_inv_subset (K := K) w⁻¹

theorem length_simple_mul_inv
    (i : Fin τ.rank) (w : WeylGroup τ) :
    (coxeterSystem τ).length (simple τ i * w⁻¹) = (coxeterSystem τ).length (w * simple τ i) := by
  rw [← (coxeterSystem τ).length_inv (simple τ i * w⁻¹), mul_inv_rev, inv_inv, simple_inv]

theorem bruhatCell_mul_simple_eq_inv
    (i : Fin τ.rank) (w : WeylGroup τ) :
    bruhatCell τ K w * bruhatCell τ K (simple τ i) =
      (bruhatCell τ K (simple τ i) * bruhatCell τ K w⁻¹)⁻¹ := by
  rw [mul_inv_rev, bruhatCell_inv, bruhatCell_inv, inv_inv, simple_inv]

theorem bruhatCell_mul_simple_of_length_eq_add_one
    {i : Fin τ.rank} {w : WeylGroup τ}
    (h : (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w + 1) :
    bruhatCell τ K w * bruhatCell τ K (simple τ i) = bruhatCell τ K (w * simple τ i) := by
  have h' : (coxeterSystem τ).length (simple τ i * w⁻¹) = (coxeterSystem τ).length w⁻¹ + 1 := by
    rw [length_simple_mul_inv, (coxeterSystem τ).length_inv, h]
  rw [bruhatCell_mul_simple_eq_inv, bruhatCell_simple_mul_of_length_eq_add_one h', bruhatCell_inv,
    mul_inv_rev, inv_inv, simple_inv]

theorem bruhatCell_mul_simple_of_length_eq_sub_one
    {i : Fin τ.rank} {w : WeylGroup τ}
    (h : (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w - 1) :
    bruhatCell τ K w * bruhatCell τ K (simple τ i) =
      bruhatCell τ K (w * simple τ i) ∪ bruhatCell τ K w := by
  have h' : (coxeterSystem τ).length (simple τ i * w⁻¹) = (coxeterSystem τ).length w⁻¹ - 1 := by
    rw [length_simple_mul_inv, (coxeterSystem τ).length_inv, h]
  rw [bruhatCell_mul_simple_eq_inv, bruhatCell_simple_mul_of_length_eq_sub_one h', Set.union_inv,
    bruhatCell_inv, bruhatCell_inv, mul_inv_rev, inv_inv, simple_inv]

variable (τ K) in
theorem right_bruhat_multiplication :
    (∀ w : WeylGroup τ, (bruhatCell τ K w)⁻¹ = bruhatCell τ K w⁻¹) ∧
    (∀ (i : Fin τ.rank) (w : WeylGroup τ),
      (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w + 1 →
        bruhatCell τ K w * bruhatCell τ K (simple τ i) = bruhatCell τ K (w * simple τ i)) ∧
    ∀ (i : Fin τ.rank) (w : WeylGroup τ),
      (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w - 1 →
        bruhatCell τ K w * bruhatCell τ K (simple τ i) =
          bruhatCell τ K (w * simple τ i) ∪ bruhatCell τ K w :=
  ⟨bruhatCell_inv, fun _ _ h => bruhatCell_mul_simple_of_length_eq_add_one h,
    fun _ _ h => bruhatCell_mul_simple_of_length_eq_sub_one h⟩

end CFSG.LieType.Chevalley
