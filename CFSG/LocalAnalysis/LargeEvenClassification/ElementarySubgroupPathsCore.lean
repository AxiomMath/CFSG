module

public import CFSG.LocalAnalysis.LargeEvenClassification.NormalElementary

public section

namespace CFSG.LargeEvenClassification.Helpers

open CFSG.Open

universe u

theorem elementary_path_inf_sup_of_le {D : Type u} [CommGroup D]
    (X H T : Subgroup D) (hHX : H ≤ X) :
    X ⊓ (H ⊔ T) = H ⊔ (X ⊓ T) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h, hh, t, ht, hproduct⟩ := Subgroup.mem_sup.mp hx.2
    have htX : t ∈ X := by
      have hmem := X.mul_mem (X.inv_mem (hHX hh)) hx.1
      simpa only [← hproduct, inv_mul_cancel_left] using hmem
    exact Subgroup.mem_sup.mpr ⟨h, hh, t, ⟨htX, ht⟩, hproduct⟩
  · exact sup_le (le_inf hHX le_sup_left)
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))

theorem elementary_path_zpowers_disjoint {D : Type u} [Group D] [Finite D]
    {p : ℕ} (hprime : p.Prime) (X : Subgroup D) (y : D)
    (horder : orderOf y = p) (hyX : y ∉ X) :
    Disjoint X (Subgroup.zpowers y) := by
  have hTcard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, horder]
  have hdiv : Nat.card (X ⊓ Subgroup.zpowers y : Subgroup D) ∣ p := by
    simpa only [hTcard] using Subgroup.card_dvd_of_le
      (inf_le_right : X ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y)
  have hcard : Nat.card (X ⊓ Subgroup.zpowers y : Subgroup D) = 1 := by
    rcases (Nat.dvd_prime hprime).mp hdiv with hone | hequal
    · exact hone
    · have heq : X ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hequal, hTcard])
      have hmem : y ∈ X ⊓ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact False.elim (hyX hmem.1)
  exact disjoint_iff.mpr (Subgroup.card_eq_one.mp hcard)

theorem elementary_path_disjoint_sup_card {D : Type u} [CommGroup D] [Finite D]
    {p a b : ℕ} (X Y : Subgroup D) (hXcard : Nat.card X = p ^ a)
    (hYcard : Nat.card Y = p ^ b) (hdisjoint : Disjoint X Y) :
    Nat.card (X ⊔ Y : Subgroup D) = p ^ (a + b) := by
  let product := X.subtype.noncommCoprod Y.subtype (fun x y => mul_comm _ _)
  have hinjective : Function.Injective product := Subgroup.mul_injective_of_disjoint hdisjoint
  have hrange : product.range = X ⊔ Y := by
    simpa only [Subgroup.subtype_range] using
      MonoidHom.noncommCoprod_range X.subtype Y.subtype (fun x y => mul_comm _ _)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinjective).toEquiv,
    Nat.card_prod, hXcard, hYcard, pow_add]

end CFSG.LargeEvenClassification.Helpers
