module

public import CFSG.GH74.Generic.S1.FrameLift

public section

namespace CFSG.GH74.Generic.S1

open Subgroup

variable {G : Type*} [Group G]

@[expose, instance_reducible] def closureCommGroup (s : Set G) (hsc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommGroup ↥(Subgroup.closure s) :=
  { (inferInstance : Group ↥(Subgroup.closure s)) with
    mul_comm := fun a b => Subtype.ext (closure_comm_of_comm s hsc a a.2 b b.2) }

theorem five_prod_succAbove (X : Fin 5 → G) (hc : ∀ i j, X i * X j = X j * X i)
    (h2 : ∀ i, X i * X i = 1) (h1 : X 0 * X 1 * X 2 * X 3 * X 4 = 1) (i : Fin 5) :
    X (i.succAbove 0) * X (i.succAbove 1) * X (i.succAbove 2) * X (i.succAbove 3) = X i := by
  let _ : CommGroup ↥(Subgroup.closure (Set.range X)) :=
    closureCommGroup _ (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact hc a b)
  let Y : Fin 5 → ↥(Subgroup.closure (Set.range X)) := fun k => ⟨X k, Subgroup.subset_closure ⟨k, rfl⟩⟩
  have hY2 : ∀ k, Y k * Y k = 1 := fun k => Subtype.ext (h2 k)
  have hY1 : Y 0 * Y 1 * Y 2 * Y 3 * Y 4 = 1 := Subtype.ext h1
  have hprod := Fin.prod_univ_succAbove Y i
  rw [Fin.prod_univ_five, hY1, Fin.prod_univ_four] at hprod
  have hinv : (Y i)⁻¹ = Y i := inv_eq_of_mul_eq_one_right (hY2 i)
  have h3 : Y (i.succAbove 0) * Y (i.succAbove 1) * Y (i.succAbove 2) * Y (i.succAbove 3) = Y i := by
    have := eq_inv_of_mul_eq_one_right hprod.symm
    rw [this, hinv]
  exact congrArg Subtype.val h3

theorem five_triple_ne_one (X : Fin 5 → G) (hc : ∀ i j, X i * X j = X j * X i)
    (h2 : ∀ i, X i * X i = 1) (h1 : X 0 * X 1 * X 2 * X 3 * X 4 = 1)
    (hd : ∀ a b, a ≠ b → X a ≠ X b) {a b c : Fin 5} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X a * X b * X c ≠ 1 := by
  classical
  let _ : CommGroup ↥(Subgroup.closure (Set.range X)) :=
    closureCommGroup _ (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact hc a b)
  let Y : Fin 5 → ↥(Subgroup.closure (Set.range X)) := fun k => ⟨X k, Subgroup.subset_closure ⟨k, rfl⟩⟩
  have hY1 : ∏ k, Y k = 1 := by
    rw [Fin.prod_univ_five]
    exact Subtype.ext h1
  intro htrip
  have hT : (Finset.univ \ ({a, b, c} : Finset (Fin 5))).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have : ({a, b, c} : Finset (Fin 5)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    omega
  obtain ⟨d, e, hde, hset⟩ := Finset.card_eq_two.1 hT
  have hsplit := Finset.prod_sdiff (f := Y) (Finset.subset_univ ({a, b, c} : Finset (Fin 5)))
  rw [hY1, hset, Finset.prod_pair hde, Finset.prod_insert (by simp [hab, hac]),
    Finset.prod_pair hbc] at hsplit
  have hABC : Y a * (Y b * Y c) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    simpa [mul_assoc] using htrip
  rw [hABC, mul_one] at hsplit
  have hDE : X d * X e = 1 := congrArg Subtype.val hsplit
  have hde' : d ≠ e := hde
  apply hd d e hde'
  calc X d = X d * (X e * X e) := by rw [h2 e, mul_one]
    _ = (X d * X e) * X e := (mul_assoc _ _ _).symm
    _ = X e := by rw [hDE, one_mul]

end CFSG.GH74.Generic.S1
