module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
public import CFSG.Certificates.Kernel.PCentSound

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup MulAction

theorem card_le_card_fix_mul_stabilizer {n : ℕ} {x : Equiv.Perm (Fin n)}
    (C : Subgroup (Equiv.Perm (Fin n))) (hC : C ≤ centralizer ({x} : Set _)) {p : Fin n}
    (hp : x p = p) :
    Nat.card C ≤ (Finset.univ.filter fun i => x i = i).card * Nat.card (stabilizer C p) := by
  rw [← Nat.card_congr (orbitProdStabilizerEquivGroup C p), Nat.card_prod]
  refine Nat.mul_le_mul_right _ ?_
  have hsub : orbit C p ⊆ ↑(Finset.univ.filter fun i => x i = i) := by
    rintro _ ⟨c, rfl⟩
    have hc : c.1 * x = x * c.1 := mem_centralizer_singleton_iff.1 (hC c.2)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    change x (c.1 p) = c.1 p
    rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hp]
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub

theorem card_centralizer_mul_le_fix_mul {n : ℕ} (R : Subgroup (Equiv.Perm (Fin n)))
    {x : Equiv.Perm (Fin n)} {p : Fin n} (hp : x p = p) (S : Finset (Equiv.Perm (Fin n)))
    (hS : ∀ s ∈ S, ∃ h ∈ R ⊓ stabilizer (Equiv.Perm (Fin n)) p, h * x * h⁻¹ = s) :
    Nat.card ↥(R ⊓ centralizer ({x} : Set _)) * S.card ≤
      (Finset.univ.filter fun i => x i = i).card * Nat.card ↥(R ⊓ stabilizer _ p) := by
  set C := R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n)))
  set H := R ⊓ stabilizer (Equiv.Perm (Fin n)) p
  have h1 := card_le_card_fix_mul_stabilizer C inf_le_right hp
  have h2 := CFSG.KC.PCent.card_mul_card_centralizer_le (H := H) S hS
  let F : ↥(stabilizer C p) → ↥(H ⊓ centralizer ({x} : Set _)) := fun c =>
    ⟨c.1.1, ⟨c.1.2.1, c.2⟩, c.1.2.2⟩
  have hF : Function.Injective F := fun c d h =>
    Subtype.ext (Subtype.ext (by simpa [F] using congrArg Subtype.val h))
  have h3 := Nat.card_le_card_of_injective F hF
  calc Nat.card C * S.card
      ≤ (Finset.univ.filter fun i => x i = i).card * Nat.card (stabilizer C p) * S.card :=
        Nat.mul_le_mul_right _ h1
    _ ≤ (Finset.univ.filter fun i => x i = i).card *
          (S.card * Nat.card ↥(H ⊓ centralizer ({x} : Set _))) := by
        rw [mul_assoc, mul_comm (Nat.card _)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ ≤ (Finset.univ.filter fun i => x i = i).card * Nat.card H := Nat.mul_le_mul_left _ h2

end CFSG.EvenSporadicStandard.HSStd.FiveY
