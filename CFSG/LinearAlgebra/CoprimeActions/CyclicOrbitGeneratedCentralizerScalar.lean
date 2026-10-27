module


public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.LinearAlgebra.CoprimeActions.CyclicOrbitGeneratedCentralizerScalar

theorem scalar {A : Type} [CommGroup A] [Finite A] (H : Subgroup (MulAut A)) (Q : Subgroup A)
    [IsCyclic Q]
    (hgen : Subgroup.closure {x : A | ∃ h ∈ H, x ∈ Q.map h.toMonoidHom} = ⊤)
    (φ : MulAut A) (hφH : ∀ h ∈ H, φ * h = h * φ)
    (hφQ : Q.map φ.toMonoidHom = Q) :
    ∃ k : ℤ, ∀ x : A, φ x = x ^ k := by
  have hmem : ∀ q ∈ Q, φ q ∈ Q := by
    intro q hq
    rw [← hφQ]; exact ⟨q, hq, rfl⟩
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic
    (MonoidHom.mk' (fun q : Q => (⟨φ q, hmem q q.2⟩ : Q)) (fun a b => by
      ext; simp))
  refine ⟨k, ?_⟩
  have hQk : ∀ q ∈ Q, φ q = q ^ k := by
    intro q hq
    have := congrArg Subtype.val (hk ⟨q, hq⟩)
    simpa using this
  let S : Subgroup A :=
    { carrier := {x | φ x = x ^ k}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, ha, hb, mul_zpow]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_inv, ha, inv_zpow] }
  have hle : Subgroup.closure {x : A | ∃ h ∈ H, x ∈ Q.map h.toMonoidHom} ≤ S := by
    rw [Subgroup.closure_le]
    rintro x ⟨h, hh, q, hq, rfl⟩
    show φ (h q) = (h q) ^ k
    have hc : φ (h q) = h (φ q) := by
      have := congrArg (fun f : MulAut A => f q) (hφH h hh)
      simpa using this
    show φ (h.toMonoidHom q) = _
    simp only [MulEquiv.coe_toMonoidHom] at *
    rw [hc, hQk q hq, map_zpow]
  intro x
  have : x ∈ S := hle (hgen ▸ Subgroup.mem_top x)
  exact this

end CFSG.LinearAlgebra.CoprimeActions.CyclicOrbitGeneratedCentralizerScalar
