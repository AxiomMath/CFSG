module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem relIndex_inf_le_relIndex_of_card_sup_le {A B C : Subgroup G}
    (hBA : B ≤ A) (hC : C ≤ Subgroup.normalizer (B : Set G))
    (hcard : Nat.card ↥(B ⊔ C) ≤ Nat.card A) :
    (B ⊓ C).relIndex C ≤ B.relIndex A := by
  have hsup : Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C) = Nat.card B * Nat.card C := by
    have h := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := C) (K := B) hC
    rwa [sup_comm C B, inf_comm C B, mul_comm (Nat.card C) (Nat.card B)] at h
  have h1 : (B ⊓ C).relIndex C * Nat.card ↥(B ⊓ C) = Nat.card C := by
    have := Subgroup.relIndex_mul_card (H := B ⊓ C) (K := C)
    simpa [inf_idem] using this
  have h2 : B.relIndex A * Nat.card B = Nat.card A := by
    have := Subgroup.relIndex_mul_card (H := B) (K := A)
    simpa [inf_eq_left.mpr hBA] using this
  apply Nat.le_of_mul_le_mul_right (c := Nat.card B) _ Nat.card_pos
  apply Nat.le_of_mul_le_mul_right (c := Nat.card ↥(B ⊓ C)) _ Nat.card_pos
  calc (B ⊓ C).relIndex C * Nat.card B * Nat.card ↥(B ⊓ C)
      = Nat.card B * ((B ⊓ C).relIndex C * Nat.card ↥(B ⊓ C)) := by ring
    _ = Nat.card B * Nat.card C := by rw [h1]
    _ = Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C) := by rw [← hsup]
    _ ≤ Nat.card A * Nat.card ↥(B ⊓ C) := Nat.mul_le_mul_right _ hcard
    _ = (B.relIndex A * Nat.card B) * Nat.card ↥(B ⊓ C) := by rw [← h2]

theorem card_sup_eq_card_of_relIndex_eq {A B C : Subgroup G}
    (hBA : B ≤ A) (hC : C ≤ Subgroup.normalizer (B : Set G))
    (h : (B ⊓ C).relIndex C = B.relIndex A) :
    Nat.card ↥(B ⊔ C) = Nat.card A := by
  have hsup : Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C) = Nat.card B * Nat.card C := by
    have h := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := C) (K := B) hC
    rwa [sup_comm C B, inf_comm C B, mul_comm (Nat.card C) (Nat.card B)] at h
  have h1 : (B ⊓ C).relIndex C * Nat.card ↥(B ⊓ C) = Nat.card C := by
    have := Subgroup.relIndex_mul_card (H := B ⊓ C) (K := C)
    simpa [inf_idem] using this
  have h2 : B.relIndex A * Nat.card B = Nat.card A := by
    have := Subgroup.relIndex_mul_card (H := B) (K := A)
    simpa [inf_eq_left.mpr hBA] using this
  apply Nat.mul_right_cancel (Nat.card_pos (α := ↥(B ⊓ C)))
  calc Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C)
      = Nat.card B * Nat.card C := hsup
    _ = Nat.card B * ((B ⊓ C).relIndex C * Nat.card ↥(B ⊓ C)) := by rw [← h1]
    _ = (B.relIndex A * Nat.card B) * Nat.card ↥(B ⊓ C) := by rw [h]; ring
    _ = Nat.card A * Nat.card ↥(B ⊓ C) := by rw [h2]

theorem eq_sup_of_relIndex_eq {H M B : Subgroup G} (hMH : M ≤ H) (hBH : B ≤ H)
    (hidx : B.relIndex M = B.relIndex H) : M ⊔ B = H := by
  have hne : B.relIndex (M ⊔ B) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : B.relIndex M ≤ B.relIndex (M ⊔ B) :=
    Subgroup.relIndex_le_of_le_right le_sup_left hne
  have h2 := Subgroup.relIndex_mul_relIndex B (M ⊔ B) H le_sup_right (sup_le hMH hBH)
  have hx : (M ⊔ B).relIndex H ≤ 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.pos_of_ne_zero hne)
    rw [mul_one, h2, ← hidx]
    exact h1
  have hx1 : (M ⊔ B).relIndex H = 1 :=
    le_antisymm hx (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  exact le_antisymm (sup_le hMH hBH) (Subgroup.relIndex_eq_one.mp hx1)


theorem not_dvd_card_sup_of_not_dvd {p : ℕ} (hp : p.Prime) {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hH : ¬ p ∣ Nat.card H) (hK : ¬ p ∣ Nat.card K) :
    ¬ p ∣ Nat.card ↥(H ⊔ K) := by
  intro h
  have hprod := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := H) (K := K) hHK
  have hdvd : p ∣ Nat.card H * Nat.card K := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left h _
  rcases hp.dvd_mul.mp hdvd with h' | h'
  · exact hH h'
  · exact hK h'

end CFSG.GroupTheory
