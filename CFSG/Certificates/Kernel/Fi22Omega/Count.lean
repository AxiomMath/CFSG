module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.KC.Fi22Omega

theorem card_mul_le_of_cosets {G : Type*} [Group G] {D M : Subgroup G} [Finite M] (hDM : D ≤ M)
    {k : ℕ} (g : Fin k → G) (hg : ∀ j, g j ∈ M)
    (hd : ∀ i j, (g i)⁻¹ * g j ∈ D → i = j) : k * Nat.card D ≤ Nat.card M := by
  have hinj : Function.Injective fun p : Fin k × D => (⟨g p.1 * p.2, M.mul_mem (hg p.1)
      (hDM p.2.2)⟩ : M) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ e
    simp only [Subtype.mk.injEq] at e
    have hij : (g i)⁻¹ * g j = (a : G) * (b : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, e, mul_assoc, mul_inv_cancel, mul_one]
    have hi : i = j := hd i j (hij ▸ D.mul_mem a.2 (D.inv_mem b.2))
    subst hi
    have hab : (a : G) = b := mul_left_cancel e
    rw [Subtype.ext hab]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem orbit_eq_of_card {G X : Type*} [Group G] [Finite G] [MulAction G X] (x : X) {n : ℕ}
    (f : ℕ → X) (hf : ∀ i < n, f i ∈ MulAction.orbit G x)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hG : Nat.card G ≤ n * Nat.card (MulAction.stabilizer G x)) :
    MulAction.orbit G x = f '' {i | i < n} ∧ (MulAction.stabilizer G x).index = n := by
  have hfin : (MulAction.orbit G x).Finite := Set.finite_range _
  have himg : f '' {i | i < n} ⊆ MulAction.orbit G x := by
    rintro _ ⟨i, hi, rfl⟩
    exact hf i hi
  have hcard : (f '' {i | i < n}).ncard = n := by
    have hinj' : Set.InjOn f {i | i < n} := fun i hi j hj e => hinj i hi j hj e
    rw [hinj'.ncard_image]
    have e : {i : ℕ | i < n} = ↑(Finset.range n) := by
      ext i
      simp
    rw [e, Set.ncard_coe_finset, Finset.card_range]
  have hle : n ≤ (MulAction.orbit G x).ncard := hcard ▸ Set.ncard_le_ncard himg hfin
  have hidx := MulAction.index_stabilizer G x
  have hmul := (MulAction.stabilizer G x).card_mul_index
  have hpos : 0 < Nat.card (MulAction.stabilizer G x) := Nat.card_pos
  have hge : (MulAction.orbit G x).ncard ≤ n := by
    rw [← hidx]
    by_contra hlt
    have : n * Nat.card (MulAction.stabilizer G x) <
        (MulAction.stabilizer G x).index * Nat.card (MulAction.stabilizer G x) :=
      Nat.mul_lt_mul_of_pos_right (by omega) hpos
    rw [Nat.mul_comm (MulAction.stabilizer G x).index, hmul] at this
    omega
  have heq : (MulAction.orbit G x).ncard = n := le_antisymm hge hle
  refine ⟨(Set.eq_of_subset_of_ncard_le himg (by rw [heq, hcard]) hfin).symm, ?_⟩
  rw [hidx, heq]

end CFSG.KC.Fi22Omega

end
