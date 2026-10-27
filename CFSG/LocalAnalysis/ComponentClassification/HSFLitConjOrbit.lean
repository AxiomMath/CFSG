module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ComponentClassification.HSFLit

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

theorem relIndex_inf_centralizer_eq_ncard (G' : Subgroup X) (x : X) :
    (G' ⊓ centralizer ({x} : Set X)).relIndex G' = {y | ∃ g ∈ G', g * x * g⁻¹ = y}.ncard := by
  let _ : MulAction G' X := MulAction.compHom X (MulAut.conj.comp G'.subtype)
  have hsmul : ∀ (g : G') (y : X), g • y = (g : X) * y * (g : X)⁻¹ := fun g y => by
    change MulAut.conj (g : X) y = _
    rw [MulAut.conj_apply]
  have hstab : MulAction.stabilizer G' x = (G' ⊓ centralizer ({x} : Set X)).subgroupOf G' := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    refine ⟨fun h => ⟨g.2, ?_⟩, fun h => ?_⟩
    · calc (g : X) * x = (g : X) * x * (g : X)⁻¹ * g := by group
        _ = x * g := by rw [h]
    · rw [h.2]
      group
  have horbit : MulAction.orbit G' x = {y | ∃ g ∈ G', g * x * g⁻¹ = y} := by
    ext y
    simp only [MulAction.mem_orbit_iff, hsmul, Set.mem_ofPred_eq]
    exact ⟨fun ⟨g, hg⟩ => ⟨g, g.2, hg⟩, fun ⟨g, hg, hgy⟩ => ⟨⟨g, hg⟩, hgy⟩⟩
  rw [relIndex, ← hstab, MulAction.index_stabilizer, horbit]

theorem exists_conj_eq_of_card_eq [Finite X] {H P Q : Subgroup X} (hPH : P ≤ H) (hQH : Q ≤ H)
    (hP : Nat.card P = 2 ^ (Nat.card H).factorization 2)
    (hQ : Nat.card Q = 2 ^ (Nat.card H).factorization 2) :
    ∃ h ∈ H, P.map (MulAut.conj h).toMonoidHom = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₁ : Nat.card (P.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv, hP]
  have hQ₁ : Nat.card (Q.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv, hQ]
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (Sylow.ofCard _ hP₁) (Sylow.ofCard _ hQ₁)
  refine ⟨h, h.2, ?_⟩
  have key : ((h • Sylow.ofCard _ hP₁ : Sylow 2 H) : Subgroup H) = Q.subgroupOf H := by
    rw [hh, Sylow.coe_ofCard]
  rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at key
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have : MulAut.conj h • (⟨p, hPH hp⟩ : H) ∈ MulAut.conj h • P.subgroupOf H :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hp
    rw [key] at this
    simpa [MulAut.smul_def, MulAut.conj_apply, mem_subgroupOf] using this
  · intro q hq
    have hq' : (⟨q, hQH hq⟩ : H) ∈ MulAut.conj h • P.subgroupOf H := by rw [key]; exact hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq'
    refine ⟨(h : X)⁻¹ * q * h, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc, mem_subgroupOf] using hq'

theorem card_eq_mul_two_pow [Finite X] {H N P Q : Subgroup X} (hHN : H ≤ N)
    (hP : Nat.card P = 2 ^ (Nat.card N).factorization 2)
    (hQ : Nat.card Q = 2 ^ (Nat.card H).factorization 2) :
    Nat.card P = Nat.card Q * 2 ^ (H.relIndex N).factorization 2 := by
  have h1 : Nat.card N = Nat.card H * H.relIndex N := by
    rw [← relIndex_mul_card, inf_of_le_left hHN, mul_comm]
  have h2 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h3 : H.relIndex N ≠ 0 := by
    intro h0
    have := relIndex_mul_card (H := H) (K := N)
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  rw [hP, hQ, h1, Nat.factorization_mul h2 h3, Finsupp.add_apply, pow_add]

end CFSG.ComponentClassification.HSFLit
