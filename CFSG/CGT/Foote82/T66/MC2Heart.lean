module

public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv

abbrev d0 : Perm (Fin 6) := c[0, 1, 2] * c[3, 4, 5]

theorem const_of_d0 : ∀ (y : Fin 6 → ZMod 2) (ε : ZMod 2),
    y 0 + y 1 + y 2 + y 3 + y 4 + y 5 = 0 → (∀ j, y (d0⁻¹ j) = y j + ε) → ∀ j, y j = y 0 := by
  decide

theorem heart6_fpf {σ k : Perm (Fin 6)} (hk : k * σ * k⁻¹ = d0) (x : evenWeight 6)
    (hx : ((evenWeightPerm σ x : evenWeight 6) : altHeart 6) = (x : altHeart 6)) :
    (x : altHeart 6) = 0 := by
  rw [QuotientAddGroup.eq, evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_zmultiples_iff] at hx
  obtain ⟨z, hz⟩ := hx
  have hxi : ∀ i, (x : Fin 6 → ZMod 2) (σ⁻¹ i) = (x : Fin 6 → ZMod 2) i + (z : ZMod 2) := by
    intro i
    have h := congrFun hz i
    simp only [allOnes, Pi.smul_apply, zsmul_eq_mul, mul_one, AddSubgroup.coe_add,
      AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply] at h
    change (z : ZMod 2) = -(x : Fin 6 → ZMod 2) (σ⁻¹ i) + (x : Fin 6 → ZMod 2) i at h
    exact (by decide : ∀ a b c : ZMod 2, c = -a + b → a = b + c) _ _ _ h
  set y : Fin 6 → ZMod 2 := fun j => (x : Fin 6 → ZMod 2) (k⁻¹ j) with hy
  have hd : ∀ j, y (d0⁻¹ j) = y j + (z : ZMod 2) := by
    intro j
    have e : k⁻¹ (d0⁻¹ j) = σ⁻¹ (k⁻¹ j) := by
      rw [← hk]
      simp [mul_inv_rev, mul_assoc]
    simp only [hy, e, hxi]
  have hsum : y 0 + y 1 + y 2 + y 3 + y 4 + y 5 = 0 := by
    have h0 : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := x.2
    have h1 : ∑ j, y j = ∑ i, (x : Fin 6 → ZMod 2) i :=
      Equiv.sum_comp k⁻¹ (fun i => (x : Fin 6 → ZMod 2) i)
    rw [Fin.sum_univ_six] at h1
    rw [h1, h0]
  have hc := const_of_d0 y _ hsum hd
  have hconst : ∀ i, (x : Fin 6 → ZMod 2) i = y 0 := by
    intro i
    have := hc (k i)
    simpa [hy] using this
  rw [QuotientAddGroup.eq_zero_iff, evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_zmultiples_iff]
  refine ⟨((y 0).val : ℤ), funext fun i => ?_⟩
  simp only [allOnes, Pi.smul_apply, zsmul_eq_mul, mul_one, hconst i]
  simp

end MC2

end CFSG.CGT.Foote82
