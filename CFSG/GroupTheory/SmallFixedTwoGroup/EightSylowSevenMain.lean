module

public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowOrbit
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowSeven

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem false_of_relIndex_normalizer_eq_seven {E : Type*} [Group E] [Finite E] (P : Sylow 2 E)
    (hab : ∀ a ∈ (P : Subgroup E), ∀ b ∈ (P : Subgroup E), a * b = b * a)
    (hcard : Nat.card (P : Subgroup E) = 8) {t : E} (ht1 : t ≠ 1)
    (hCt : centralizer ({t} : Set E) = (P : Subgroup E))
    (h7 : (P : Subgroup E).relIndex (normalizer ((P : Subgroup E) : Set E)) = 7)
    {a x : E} (ha : a * a = 1) (ha1 : a ≠ 1) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hcomm : (x * a * x⁻¹) * a = a * (x * a * x⁻¹)) : False := by
  have htT : t ∈ (P : Subgroup E) := by
    rw [← hCt]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hC : centralizer ({t} : Set E) ≤ (P : Subgroup E) := hCt.le
  have hrel : (P : Subgroup E).relIndex (normalizer ((P : Subgroup E) : Set E)) =
      Nat.card (P : Subgroup E) - 1 := by
    rw [h7, hcard]
  have hconjT : ∀ y ∈ (P : Subgroup E), y ≠ 1 →
      ∃ n ∈ normalizer ((P : Subgroup E) : Set E), n * t * n⁻¹ = y :=
    fun y hy hy1 => exists_conj_eq_of_relIndex_eq htT ht1 hC hrel hy hy1
  have hconj : ∀ u : E, u * u = 1 → u ≠ 1 →
      ∃ g, ∀ y, y * u = u * y ↔ g⁻¹ * y * g ∈ (P : Subgroup E) :=
    fun u hu hu1 => exists_conj_centralizer_of_involution P hCt hconjT hu hu1
  have hN3 : ∀ y ∈ normalizer ((P : Subgroup E) : Set E), y ^ 3 = 1 →
      y ∈ (P : Subgroup E) :=
    fun y hy hy3 => pow_three_mem_of_relIndex_eq_seven h7 hy hy3
  exact false_of_conj_centralizers hab hcard hN3 hconj ha ha1 hx hx1 hcomm

end CFSG.GroupTheory.SmallFixedTwoGroup
