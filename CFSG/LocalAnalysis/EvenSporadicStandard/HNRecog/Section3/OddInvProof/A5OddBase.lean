module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem a5ob_coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem a5ob_sigma_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide

private abbrev a5ob_swapW : A5WrTwo := ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩

private theorem a5ob_swapW_right :
    a5ob_swapW.right = Multiplicative.ofAdd (1 : ZMod 2) := rfl

private theorem a5ob_swapW_sq : a5ob_swapW * a5ob_swapW = 1 := by
  apply RegularWreathProduct.ext
  · funext i
    simp [a5ob_swapW, RegularWreathProduct.mul_def, a5ob_sigma_mul_self]
  · simp [a5ob_swapW, RegularWreathProduct.mul_def, a5ob_sigma_mul_self]

private theorem a5ob_swapW_mul_baseEmb_mul_inv (x y : alternatingGroup (Fin 5)) :
    a5ob_swapW * A5WrTwo.baseEmb (x, y) * a5ob_swapW⁻¹ = A5WrTwo.baseEmb (y, x) :=
  A5WrTwo.swap_mul_baseEmb_mul_inv x y

private theorem a5ob_baseEmb_mul_swapW_mul_baseEmb_mul_swapW
    (x y x' y' : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (x, y) * a5ob_swapW) * (A5WrTwo.baseEmb (x', y') * a5ob_swapW)
      = A5WrTwo.baseEmb (x * y', y * x') := by
  calc (A5WrTwo.baseEmb (x, y) * a5ob_swapW) * (A5WrTwo.baseEmb (x', y') * a5ob_swapW)
      = A5WrTwo.baseEmb (x, y) * (a5ob_swapW * A5WrTwo.baseEmb (x', y') * a5ob_swapW⁻¹) *
          (a5ob_swapW * a5ob_swapW) := by group
    _ = A5WrTwo.baseEmb (x, y) * A5WrTwo.baseEmb (y', x') * 1 := by
          rw [a5ob_swapW_mul_baseEmb_mul_inv, a5ob_swapW_sq]
    _ = A5WrTwo.baseEmb (x * y', y * x') := by
          rw [mul_one, ← A5WrTwo.baseEmb.map_mul, Prod.mk_mul_mk]

private theorem a5ob_baseEmb_mul_swapW_sq (x y : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (x, y) * a5ob_swapW) ^ 2 = A5WrTwo.baseEmb (x * y, y * x) := by
  rw [pow_two, a5ob_baseEmb_mul_swapW_mul_baseEmb_mul_swapW]

private theorem a5ob_conj_inv (k : alternatingGroup (Fin 5)) :
    ∃ c : alternatingGroup (Fin 5), c * k * c⁻¹ = k⁻¹ := by
  decide +kernel +revert

theorem oddInv_wr_outer_eq {u : A5WrTwo} (hu : u ∉ _root_.commutator A5WrTwo)
    (hu2 : u ^ 2 = 1) :
    ∃ g : alternatingGroup (Fin 5),
      u = A5WrTwo.baseEmb (g, g⁻¹) * (⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩ : A5WrTwo) := by
  have hu_right_ne : u.right ≠ 1 := by
    intro h1
    exact hu (by rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]; exact h1)
  have hu_right : u.right = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases a5ob_coord_cases u.right with h | h
    · exact absurd h hu_right_ne
    · exact h
  obtain ⟨⟨p, q⟩, hpq_eq⟩ : ∃ pq : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      A5WrTwo.baseEmb pq = u * a5ob_swapW⁻¹ := by
    refine MonoidHom.mem_range.mp ?_
    rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
    change (u * a5ob_swapW⁻¹).right = 1
    rw [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hu_right,
      a5ob_swapW_right, mul_inv_cancel]
  have hu_eq : u = A5WrTwo.baseEmb (p, q) * a5ob_swapW := by
    rw [hpq_eq]
    group
  have hsq : A5WrTwo.baseEmb (p * q, q * p) = 1 := by
    have h := hu2
    rw [hu_eq, a5ob_baseEmb_mul_swapW_sq] at h
    exact h
  have hpq : (p * q, q * p) = 1 :=
    A5WrTwo.baseEmb_injective (by rw [hsq]; exact (A5WrTwo.baseEmb.map_one).symm)
  have hpq1 : p * q = 1 := congrArg Prod.fst hpq
  have hq : q = p⁻¹ := eq_inv_of_mul_eq_one_right hpq1
  exact ⟨p, by rw [hu_eq, hq]⟩

theorem oddInv_wr_outer_mul {u v : A5WrTwo} (hu : u ∉ _root_.commutator A5WrTwo)
    (hv : v ∉ _root_.commutator A5WrTwo) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) :
    ∃ k k' : alternatingGroup (Fin 5), u * v = A5WrTwo.baseEmb (k, k') ∧ IsConj k k' := by
  obtain ⟨g, hg⟩ := oddInv_wr_outer_eq hu hu2
  obtain ⟨h, hh⟩ := oddInv_wr_outer_eq hv hv2
  refine ⟨g * h⁻¹, g⁻¹ * h, ?_, ?_⟩
  · rw [hg, hh, a5ob_baseEmb_mul_swapW_mul_baseEmb_mul_swapW]
  · have h1 : IsConj (g * h⁻¹) (g * h⁻¹)⁻¹ :=
      isConj_iff.mpr (a5ob_conj_inv (g * h⁻¹))
    refine IsConj.trans h1 ?_
    exact isConj_iff.mpr ⟨g⁻¹, by group⟩

theorem oddInv_wr_orderOf_baseEmb {k k' : alternatingGroup (Fin 5)} (h : IsConj k k') :
    orderOf (A5WrTwo.baseEmb (k, k')) = orderOf k := by
  rw [orderOf_injective A5WrTwo.baseEmb A5WrTwo.baseEmb_injective (k, k'), Prod.orderOf_mk]
  obtain ⟨c, hc⟩ := h
  have hkk' : orderOf k = orderOf k' := SemiconjBy.orderOf_eq (c : alternatingGroup (Fin 5)) hc
  rw [← hkk', Nat.lcm_self]

end CFSG.EvenSporadicStandard.HNRecog.Section3
