module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G]

theorem orderOf_mul_of_comm_invol {t z : G} (ht : t * t = 1) (hz : z * z = 1) (hc : t * z = z * t)
    (hne : t ≠ z) : orderOf (t * z) = 2 := by
  apply orderOf_eq_prime
  · calc (t * z) ^ 2 = t * z * (t * z) := by rw [pow_two]
      _ = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [hc]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [ht, hz, one_mul]
  · intro h
    apply hne
    have h' := mul_eq_one_iff_eq_inv.1 h
    rw [h', inv_eq_of_mul_eq_one_right hz]

theorem RC_conj_mem [Finite G] {z : G} {S : Subgroup G} (hSC : S ≤ Cen z) :
    ∀ s ∈ S, ∀ r ∈ RC S z, s * r * s⁻¹ ∈ RC S z := by
  intro s hs r hr
  refine ⟨S.mul_mem (S.mul_mem hs hr.1) (S.inv_mem hs), ?_⟩
  exact (CFSG.GH74.GLS.Stage1.Thm6.Prod.LC_normal z).conj_mem ⟨r, hSC hr.1⟩ hr.2 ⟨s, hSC hs⟩

end CFSG.GH74.GLS.Stage2.Local.P27
