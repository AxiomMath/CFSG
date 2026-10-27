module

public import CFSG.ClassicalInvolution.Asc77.AscSteps185
public import CFSG.ClassicalInvolution.Asc77.AscSix63

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_of_sq_mem {K L : Subgroup G} (hK : Group.IsPerfect ↥K)
    (h : ∀ x ∈ K, x * x ∈ L) : K ≤ L := by
  have hcomm : commutator ↥K ≤ L.subgroupOf K := by
    rw [commutator_eq_closure]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨u, v, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have e : ((⁅u, v⁆ : ↥K) : G) =
        ((u : G) * u) * ((u⁻¹ * v : ↥K) * (u⁻¹ * v : ↥K) : ↥K) *
          ((v⁻¹ : ↥K) * (v⁻¹ : ↥K) : ↥K) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    refine L.mul_mem (L.mul_mem (h _ u.2) ?_) (h _ (K.inv_mem v.2))
    exact h _ (K.mul_mem (K.inv_mem u.2) v.2)
  rw [hK.commutator_eq_top, top_le_iff, eq_top_iff] at hcomm
  intro x hx
  exact (Subgroup.mem_subgroupOf.mp (hcomm (Subgroup.mem_top ⟨x, hx⟩)))

variable {p f : ℕ} [Fact p.Prime]

theorem four_le_natCard_galoisField (hq : 5 ≤ p ^ f) : 4 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  omega

variable {Ω : Set (Subgroup G)}

theorem HypOmegaMod.exists_orderOf_four_of_mem [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω) : ∃ u ∈ K, orderOf u = 4 := by
  obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
  obtain ⟨u, huR, hu⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp hR
  exact ⟨u, hRK.1 huR, hu⟩

end CFSG.ClassicalInvolution.Asc77
