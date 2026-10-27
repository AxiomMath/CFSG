module

public import CFSG.CharacterTheory.Wreathed.QuaternionEmbedding

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def quaternionQuotientProjection (h : ℕ) :
    Wreath (2 * h) →* Multiplicative (ZMod (2 * h)) where
  toFun g :=
    let c := coordinateEquiv (2 * h) g
    Multiplicative.ofAdd (c.1 + c.2.1 + if c.2.2 = 0 then 0 else (h : ZMod (2 * h)))
  map_one' := by
    change Multiplicative.ofAdd
      ((0 : ZMod (2 * h)) + 0 + if (0 : ZMod 2) = 0 then 0 else (h : ZMod (2 * h))) = 1
    simp
  map_mul' g k := by
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 * h)).symm.surjective g
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (2 * h)).symm.surjective k
    change (let x := coordinateEquiv (2 * h) (element (2 * h) a b e * element (2 * h) c d f)
      ; Multiplicative.ofAdd (x.1 + x.2.1 + if x.2.2 = 0 then 0 else (h : ZMod (2 * h)))) =
      Multiplicative.ofAdd (a + b + if e = 0 then 0 else (h : ZMod (2 * h))) *
        Multiplicative.ofAdd (c + d + if f = 0 then 0 else (h : ZMod (2 * h)))
    rcases swap_exponent_cases e with rfl | rfl <;>
      rcases swap_exponent_cases f with rfl | rfl
    · rw [element_base_mul]
      apply Multiplicative.toAdd.injective
      change a + c + (b + d) + 0 = (a + b + 0) + (c + d + 0)
      abel
    · rw [element_base_mul]
      apply Multiplicative.toAdd.injective
      change a + c + (b + d) + h = (a + b + 0) + (c + d + h)
      abel
    · rw [element_swap_mul, add_zero]
      apply Multiplicative.toAdd.injective
      change a + d + (b + c) + h = (a + b + h) + (c + d + 0)
      abel
    · rw [element_swap_mul, show (1 + 1 : ZMod 2) = 0 by decide]
      apply Multiplicative.toAdd.injective
      change a + d + (b + c) + 0 = (a + b + h) + (c + d + h)
      linear_combination -(half_modulus_add_self h)

theorem quaternionQuotientProjection_surjective (h : ℕ) :
    Function.Surjective (quaternionQuotientProjection h) := by
  intro a
  refine ⟨element (2 * h) (Multiplicative.toAdd a) 0 0, ?_⟩
  change Multiplicative.ofAdd (Multiplicative.toAdd a + 0 + 0) = a
  simp

theorem quaternionQuotientProjection_ker (h : ℕ) :
    (quaternionQuotientProjection h).ker = quaternionSubgroup h := by
  ext g
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 * h)).symm.surjective g
  change element (2 * h) a b e ∈ (quaternionQuotientProjection h).ker ↔
    element (2 * h) a b e ∈ quaternionSubgroup h
  constructor
  · intro hg
    rcases swap_exponent_cases e with rfl | rfl
    · change Multiplicative.ofAdd (a + b + 0) = 1 at hg
      have hs : a + b + 0 = 0 := congrArg Multiplicative.toAdd hg
      have hb : b = -a := by linear_combination hs
      rw [hb]
      exact ⟨QuaternionGroup.a a, rfl⟩
    · change Multiplicative.ofAdd (a + b + h) = 1 at hg
      have hs : a + b + h = 0 := congrArg Multiplicative.toAdd hg
      have ha : a = h - b := by
        linear_combination hs - half_modulus_add_self h
      rw [ha]
      exact ⟨QuaternionGroup.xa b, rfl⟩
  · rintro ⟨c, hc⟩
    rw [← hc]
    cases c with
    | a i =>
      change Multiplicative.ofAdd (i + -i + 0) = 1
      simp
    | xa i =>
      change Multiplicative.ofAdd (h - i + i + h) = 1
      apply Multiplicative.toAdd.injective
      change h - i + i + h = 0
      linear_combination half_modulus_add_self h

instance quaternionSubgroup_normal (h : ℕ) : (quaternionSubgroup h).Normal := by
  rw [← quaternionQuotientProjection_ker]
  infer_instance

@[expose] def quaternionQuotientEquivCyclic (h : ℕ) :
    Wreath (2 * h) ⧸ quaternionSubgroup h ≃* Multiplicative (ZMod (2 * h)) := by
  exact (QuotientGroup.quotientMulEquivOfEq (quaternionQuotientProjection_ker h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quaternionQuotientProjection h)
      (quaternionQuotientProjection_surjective h))

theorem card_quaternion_quotient (h : ℕ) :
    Nat.card (Wreath (2 * h) ⧸ quaternionSubgroup h) = 2 * h := by
  rw [Nat.card_congr (quaternionQuotientEquivCyclic h).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem quaternion_quotient_isCyclic (h : ℕ) :
    IsCyclic (Wreath (2 * h) ⧸ quaternionSubgroup h) :=
  (quaternionQuotientEquivCyclic h).isCyclic.mpr inferInstance

theorem normalClosure_d_eq_quaternionSubgroup (h : ℕ) :
    Subgroup.normalClosure {element (2 * h) h 0 1} = quaternionSubgroup h := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    refine ⟨QuaternionGroup.xa 0, ?_⟩
    change element (2 * h) (h - 0) 0 1 = element (2 * h) h 0 1
    rw [sub_zero]
  · let H := Subgroup.normalClosure {element (2 * h) h 0 1}
    change quaternionSubgroup h ≤ H
    have hN : H.Normal := inferInstance
    have hd : element (2 * h) h 0 1 ∈ H := Subgroup.subset_normalClosure (by simp)
    have hc : element (2 * h) (h + 1) (-1) 1 ∈ H := by
      have hconj := hN.conj_mem _ hd (element (2 * h) 1 0 0)
      rw [conjugate_swap_by_base] at hconj
      simpa only [sub_zero, zero_add, zero_sub] using hconj
    have hr : element (2 * h) 1 (-1) 0 ∈ H := by
      have hp := H.mul_mem hc (H.inv_mem hd)
      rw [element_swap_inv, element_swap_mul,
        show (1 + 1 : ZMod 2) = 0 by decide] at hp
      have heq : element (2 * h) (h + 1 + -h) (-1 + -0) 0 = element (2 * h) 1 (-1) 0 := by
        rw [element_eq_iff]
        refine ⟨?_, ?_, rfl⟩ <;> abel
      simpa only [heq] using hp
    rw [quaternion_range_eq_generated, Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg1 | hg2
    · exact hg1 ▸ hr
    · exact Set.mem_singleton_iff.mp hg2 ▸ hd

end CFSG.Wreathed
