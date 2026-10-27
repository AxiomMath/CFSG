module

public import CFSG.GroupTheory.HuppertProduct.Mho

public section

open scoped commutatorElement

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem commutator_mho_le {H K : Subgroup G} (hK : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (h : ∀ x ∈ H, ∀ g ∈ H, ⁅x ^ n, g⁆ ∈ K) : ⁅mho H n, H⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro m hm g hg
  have hnorm : ∀ a ∈ H, ∀ k ∈ K, a * k * a⁻¹ ∈ K := Subgroup.le_normalizer_iff.1 hK
  let S : Subgroup G :=
    { carrier := {m | m ∈ H ∧ ⁅m, g⁆ ∈ K}
      one_mem' := ⟨H.one_mem, by simpa using K.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨H.mul_mem haH hbH, ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact K.mul_mem (hnorm a haH _ hb) ha
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨H.inv_mem haH, ?_⟩
        rw [commutatorElement_inv_left, ← commutatorElement_inv]
        simpa using hnorm a⁻¹ (H.inv_mem haH) _ (K.inv_mem ha) }
  have hle : mho H n ≤ S := mho_le_of_forall fun x hx => ⟨H.pow_mem hx n, h x hx g hg⟩
  exact (hle hm).2

end CFSG.GroupTheory.HuppertProduct
