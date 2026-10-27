module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Ladder

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3


@[expose] noncomputable def B : Subgroup J := Subgroup.centralizer (A : Set J)

theorem mem_B_iff (x : J) : x ∈ B ↔ ∀ a ∈ A, x * a = a * x := by
  rw [B, Subgroup.mem_centralizer_iff]
  exact ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩

theorem thLocalWitness_of_facts (hJ : Nat.card J = 90745943887872000)
    (hB : Nat.card B = 2 ^ 9)
    (htrans : ∀ a ∈ A, a ≠ 1 → ∃ n : J, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ n * z * n⁻¹ = a)
    (hsurj : ∀ f : J → J, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
      (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n : J, ∀ a ∈ A, n * a * n⁻¹ = f a) :
    ThLocalWitness S A B z where
  pgroup := pgroup_S
  index_odd := not_dvd_index_S hJ
  z_sq := by rw [sq]; exact z_mul_self
  z_ne_one := z_ne_one
  z_mem := z_mem_S
  center_le := center_le_S
  mem_A_iff := mem_A_iff
  A_comm := A_comm
  A_sq := A_sq
  A_card := A_card
  z_mem_A := z_mem_A
  mem_B_iff := mem_B_iff
  B_card := hB
  trans := htrans
  surj := hsurj

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
