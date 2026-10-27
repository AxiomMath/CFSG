module

public import CFSG.GH74.KGroups.U33Tables
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.GH74.KGroups.U33 (QP QS_closure QS_le equiv_of_lieModel one_class sy2)

private theorem orderOf_eq_two_of_mul_self {G : Type} [Group G] {x : G} (hx : x * x = 1)
    (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime_iff.2 ⟨by rwa [pow_two], hx1⟩

private theorem sy2_sq_ne_one : sy2 * sy2 ≠ 1 := by decide +kernel

private theorem sy2_sq_sq : sy2 * sy2 * (sy2 * sy2) = 1 := by decide +kernel

private theorem sy2_mem :
    sy2 ∈ QP.originalSubgroup :=
  QS_le (by
    rw [QS_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert _ _))))

private theorem exists_order_four :
    ∃ k : Equiv.Perm (Fin 28), k ∈ QP.originalSubgroup ∧ k * k ≠ 1 ∧ k * k * (k * k) = 1 :=
  ⟨sy2, sy2_mem, sy2_sq_ne_one, sy2_sq_sq⟩

private theorem exists_order_four_of_equiv
    {N : Type} [Group N] (e : N ≃* QP.originalSubgroup) :
    ∃ k₁ : N, k₁ * k₁ ≠ 1 ∧ k₁ * k₁ * (k₁ * k₁) = 1 := by
  obtain ⟨k, hk, hk1, hk4⟩ := exists_order_four
  refine ⟨e.symm ⟨k, hk⟩, fun h => hk1 ?_, ?_⟩
  · have h' := congrArg (fun z => (e z : Equiv.Perm (Fin 28))) h
    simpa using h'
  · apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, map_one]
    exact Subtype.ext hk4

theorem u33_involutions_conj
    {N : Type} [Group N]
    (hN : CFSG.Blueprint.LieModel N .PSU 3 3 1)
    (x y : N) (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ h : N, h * x * h⁻¹ = y := by
  obtain ⟨e⟩ := equiv_of_lieModel hN
  exact one_class e x y (orderOf_eq_two_of_mul_self hx hx1) (orderOf_eq_two_of_mul_self hy hy1)

theorem u33_involution_eq_sq
    {N : Type} [Group N]
    (hN : CFSG.Blueprint.LieModel N .PSU 3 3 1)
    (x : N) (hx : x * x = 1) (hx1 : x ≠ 1) : ∃ k : N, k * k = x ∧ k ^ 4 = 1 := by
  obtain ⟨e⟩ := equiv_of_lieModel hN
  obtain ⟨k₁, hk₁1, hk₁4⟩ := exists_order_four_of_equiv e
  obtain ⟨g, hg⟩ := one_class e (k₁ * k₁) x (orderOf_eq_two_of_mul_self hk₁4 hk₁1)
    (orderOf_eq_two_of_mul_self hx hx1)
  have hkk : g * k₁ * g⁻¹ * (g * k₁ * g⁻¹) = x := by
    rw [← hg]
    group
  have key : ∀ a : N, a * a = x → a ^ 4 = 1 := fun a ha =>
    calc a ^ 4 = a * a * (a * a) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [ha, hx]
  exact ⟨g * k₁ * g⁻¹, hkk, key _ hkk⟩

theorem u33_isSimpleGroup {N : Type} [Group N] (hN : CFSG.Blueprint.LieModel N .PSU 3 3 1) :
    IsSimpleGroup N ∧ ∃ a b : N, a * b ≠ b * a := by
  have hm := hN.statedClassicalModel_of_ne_zero (n := 3) (by decide)
  have hs : IsSimpleGroup N := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity N 3 3 1 hm).2
  refine ⟨hs, ?_⟩
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative N := ⟨⟨fun a b => hcon a b⟩⟩
  have hp : (Nat.card N).Prime := Group.is_simple_iff_prime_card.mp hs
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm] at hp
  norm_num at hp

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
