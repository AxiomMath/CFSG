module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E7a

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

theorem exists_of_mem_conjugate {g x : X} (hx : x ∈ CFSG.conjugate V g) :
    ∃ a ∈ V, x = g⁻¹ * a * g := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simp⟩

theorem PlaneSys.conjugate_comm (hS : PlaneSys V W) {g a b : X} (ha : a ∈ CFSG.conjugate V g)
    (hb : b ∈ CFSG.conjugate V g) : a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := exists_of_mem_conjugate ha
  obtain ⟨b', hb', rfl⟩ := exists_of_mem_conjugate hb
  have h := hS.comm a' ha' b' hb'
  calc g⁻¹ * a' * g * (g⁻¹ * b' * g) = g⁻¹ * (a' * b') * g := by group
    _ = g⁻¹ * (b' * a') * g := by rw [h]
    _ = g⁻¹ * b' * g * (g⁻¹ * a' * g) := by group

theorem PlaneSys.conjugate_sq (hS : PlaneSys V W) {g a : X} (ha : a ∈ CFSG.conjugate V g) :
    a * a = 1 := by
  obtain ⟨a', ha', rfl⟩ := exists_of_mem_conjugate ha
  have h := hS.sq a' ha'
  calc g⁻¹ * a' * g * (g⁻¹ * a' * g) = g⁻¹ * (a' * a') * g := by group
    _ = 1 := by rw [h]; group

theorem conjugate_eq_of_le_normalizer [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W)
    (hC : ∀ y ∈ normalizer (V : Set X), y * y = 1 → y ∈ centralizer (V : Set X) → y ∈ V)
    {k : X} (hk : CFSG.conjugate V k ≤ normalizer (V : Set X)) : CFSG.conjugate V k = V := by
  refine eq_of_card_le hS hpar hC hk (fun a ha b hb => hS.conjugate_comm ha hb)
    (fun a ha => hS.conjugate_sq ha) ?_
  have hinj : Function.Injective (MulAut.conj k⁻¹).toMonoidHom :=
    (MulAut.conj k⁻¹).injective
  have hc : Nat.card (CFSG.conjugate V k) = Nat.card V :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective V (MulAut.conj k⁻¹).toMonoidHom hinj).toEquiv.symm
  rw [hc, hS.card_D]

end CFSG.OddStandard.SmallF3.Omega
