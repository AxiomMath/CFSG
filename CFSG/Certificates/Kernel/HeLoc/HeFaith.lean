module

public import CFSG.Sporadic.HeldB.OuterArith

public section

namespace CFSG.KC.HeLoc

open CFSG.Sporadic.HeldB

theorem he_mul_mem_iff
    {a b : Equiv.Perm (Fin 8330)} (ha : a ∈ heAutGroup) (hb : b ∈ heAutGroup) :
    a * b ∈ heP ↔ (a ∈ heP ↔ b ∈ heP) := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := heP.subgroupOf heAutGroup)
    heP_relIndex_heAutGroup (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
  exact h

theorem he_sq_mem
    {a : Equiv.Perm (Fin 8330)} (ha : a ∈ heAutGroup) : a * a ∈ heP :=
  (he_mul_mem_iff ha ha).2 Iff.rfl

theorem he_eq_of_base
    {x y : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup) (hy : y ∈ heAutGroup)
    (hxy : x ∈ heP ↔ y ∈ heP) (hb : ∀ b : Fin 8330, (b : Nat) < 5 → x b = y b) : x = y := by
  have hm : y⁻¹ * x ∈ heP := by
    rw [he_mul_mem_iff (heAutGroup.inv_mem hy) hx, inv_mem_iff]
    exact hxy.symm
  have h1 := eq_one_of_fix_base hm fun b hb' => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, hb b hb']
  exact (inv_mul_eq_one.1 h1).symm

end CFSG.KC.HeLoc

end
