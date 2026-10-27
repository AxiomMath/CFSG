module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type*} [Group G]

private instance : IsAddKleinFour (Fin 2 → ZMod 2) where
  card_four := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  exponent_two := by
    rw [AddMonoid.exponent_eq_prime_iff Nat.prime_two]
    intro x hx
    exact addOrderOf_eq_prime (by
      rw [two_nsmul]
      funext i
      exact ZModModule.add_self (x i)) hx

theorem mem_closure_pair_iff_of_involutions {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) {g : G} :
    g ∈ Subgroup.closure ({x, y} : Set G) ↔ g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have hyx : y * x = x * y := hxy.symm
  have hxxy : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have hyxy : y * (x * y) = x := by rw [← mul_assoc, hyx, mul_assoc, hy, mul_one]
  have hxyx : (x * y) * x = y := by rw [mul_assoc, hyx, ← mul_assoc, hx, one_mul]
  have hxyy : (x * y) * y = x := by rw [mul_assoc, hy, mul_one]
  have hxy2 : (x * y) * (x * y) = 1 := by
    rw [mul_assoc, ← mul_assoc y x y, hyx, mul_assoc, hy, mul_one, hx]
  constructor
  · intro hg
    refine Subgroup.closure_induction (p := fun g _ => g = 1 ∨ g = x ∨ g = y ∨ g = x * y)
      ?_ ?_ ?_ ?_ hg
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro a b _ _ iha ihb
      rcases iha with rfl | rfl | rfl | rfl <;> rcases ihb with rfl | rfl | rfl | rfl <;>
        simp [one_mul, mul_one, hx, hy, hyx, hxxy, hyxy, hxyx, hxyy, hxy2]
    · intro a _ iha
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
      have hxyinv : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy2
      rcases iha with rfl | rfl | rfl | rfl <;> simp [hxinv, hyinv, hxyinv]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem card_closure_pair_of_involutions {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card ↥(Subgroup.closure ({x, y} : Set G)) = 4 := by
  classical
  have hxy_ne_one : x * y ≠ 1 := by
    intro h
    apply hne
    have key : x * (x * y) = x * 1 := by rw [h]
    rw [← mul_assoc, hx, one_mul, mul_one] at key
    exact key.symm
  have hx_ne_xy : x ≠ x * y := by
    intro h
    apply hy1
    have key : x * x = x * (x * y) := by rw [← h]
    rw [hx, ← mul_assoc, hx, one_mul] at key
    exact key.symm
  have hy_ne_xy : y ≠ x * y := by
    intro h
    apply hx1
    have key : y * y = y * (x * y) := by rw [← h]
    rw [hy, ← mul_assoc, hxy.symm, mul_assoc, hy, mul_one] at key
    exact key.symm
  have hne' : y ≠ x := fun h => hne h.symm
  have hx_ne_xy' : x * y ≠ x := fun h => hx_ne_xy h.symm
  have hy_ne_xy' : x * y ≠ y := fun h => hy_ne_xy h.symm
  let z1 : ↥(Subgroup.closure ({x, y} : Set G)) := ⟨1, Subgroup.one_mem _⟩
  let zx : ↥(Subgroup.closure ({x, y} : Set G)) :=
    ⟨x, Subgroup.subset_closure (by simp)⟩
  let zy : ↥(Subgroup.closure ({x, y} : Set G)) :=
    ⟨y, Subgroup.subset_closure (by simp)⟩
  let zxy : ↥(Subgroup.closure ({x, y} : Set G)) :=
    ⟨x * y, Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))⟩
  let f : Fin 4 → ↥(Subgroup.closure ({x, y} : Set G)) := ![z1, zx, zy, zxy]
  let ginv : ↥(Subgroup.closure ({x, y} : Set G)) → Fin 4 := fun t =>
    if t.val = 1 then 0 else if t.val = x then 1 else if t.val = y then 2 else 3
  have hleft : Function.LeftInverse ginv f := by
    intro i
    fin_cases i <;>
      simp [f, ginv, z1, zx, zy, zxy, hx1, hy1, hne', hxy_ne_one, hx_ne_xy', hy_ne_xy']
  have hsurj : Function.Surjective f := by
    intro t
    rcases (mem_closure_pair_iff_of_involutions hx hy hxy).mp t.2 with h | h | h | h
    · exact ⟨0, by apply Subtype.ext; simpa [f, z1] using h.symm⟩
    · exact ⟨1, by apply Subtype.ext; simpa [f, zx] using h.symm⟩
    · exact ⟨2, by apply Subtype.ext; simpa [f, zy] using h.symm⟩
    · exact ⟨3, by apply Subtype.ext; simpa [f, zxy] using h.symm⟩
  have hf : Function.Bijective f := ⟨hleft.injective, hsurj⟩
  have e : Fin 4 ≃ ↥(Subgroup.closure ({x, y} : Set G)) := Equiv.ofBijective f hf
  have hc := Nat.card_congr e
  rw [show Nat.card (Fin 4) = 4 by simp [Nat.card_eq_fintype_card]] at hc
  exact hc.symm

theorem nonempty_mulEquiv_elem_two_of_involutions {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nonempty (↥(Subgroup.closure ({x, y} : Set G)) ≃* Multiplicative (Fin 2 → ZMod 2)) := by
  haveI : IsKleinFour ↥(Subgroup.closure ({x, y} : Set G)) :=
    { card_four := card_closure_pair_of_involutions hx hy hxy hx1 hy1 hne
      exponent_two := by
        haveI : Nontrivial ↥(Subgroup.closure ({x, y} : Set G)) :=
          ⟨⟨x, Subgroup.subset_closure (by simp)⟩, ⟨1, Subgroup.one_mem _⟩,
            fun h => hx1 (congrArg Subtype.val h)⟩
        rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
        intro g hg
        apply orderOf_eq_prime
        · have hxy2 : (x * y) * (x * y) = 1 := by
            rw [mul_assoc, ← mul_assoc y x y, hxy.symm, mul_assoc, hy, mul_one, hx]
          rw [pow_two]
          rcases (mem_closure_pair_iff_of_involutions hx hy hxy).mp g.2 with h | h | h | h
          · exact absurd (Subtype.ext h) hg
          · apply Subtype.ext; show g.val * g.val = 1; rw [h, hx]
          · apply Subtype.ext; show g.val * g.val = 1; rw [h, hy]
          · apply Subtype.ext; show g.val * g.val = 1; rw [h, hxy2]
        · exact hg }
  exact IsKleinFour.nonempty_mulEquiv

end CFSG.EvenSporadicStandard.HNRecog.Section3
