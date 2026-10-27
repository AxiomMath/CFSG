module


public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleNormalFixedSpace

public section

namespace CFSG.LinearAlgebra.CoprimeActions.PrimeOrderComplementFixedSpaceFaithfulness

theorem faithful {F V H : Type*} [Field F] [Group H] [Finite H] [AddCommGroup V] [Module F V]
    (σ : Representation F H V) (hinj : Function.Injective σ) (hirr : σ.IsIrreducible)
    (P : Subgroup H) [P.Normal] (hP : P ≠ ⊥) (E R : Subgroup H) (hE : E ≤ P) (hR : R ≤ P)
    (hER : E ⊔ R = P) {p : ℕ} (hp : p.Prime) (hRp : Nat.card R = p)
    (hfix : Representation.invariants (σ.comp E.subtype) ≠ ⊥) :
    ∀ r ∈ R, (∀ w ∈ Representation.invariants (σ.comp E.subtype), σ r w = w) → r = 1 := by
  intro r hr hrw
  by_contra hr1
  set W := Representation.invariants (σ.comp E.subtype) with hW
  let K : Subgroup H :=
    { carrier := {g | ∀ w ∈ W, σ g w = w}
      mul_mem' := fun {a b} ha hb w hw => by
        rw [map_mul, Module.End.mul_apply, hb w hw, ha w hw]
      one_mem' := fun w _ => by simp
      inv_mem' := fun {a} ha w hw => by
        have h := ha w hw
        have h2 : σ a⁻¹ (σ a w) = w := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rw [h] at h2; exact h2 }
  have hEK : E ≤ K := fun g hg w hw => by
    have := (Representation.mem_invariants _ _).1 hw ⟨g, hg⟩
    simpa using this
  have hzR : Subgroup.zpowers r ≤ K := by
    rw [Subgroup.zpowers_le]; exact hrw
  haveI : Fact (Nat.card R).Prime := ⟨hRp ▸ hp⟩
  have hRK : R ≤ K := by
    have hz : (Subgroup.zpowers r).subgroupOf R = ⊤ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Subgroup.zpowers r).subgroupOf R) with h | h
      · exfalso
        apply hr1
        have : (⟨r, hr⟩ : R) ∈ (Subgroup.zpowers r).subgroupOf R :=
          Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers r)
        rw [h, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      · exact h
    intro g hg
    have : (⟨g, hg⟩ : R) ∈ (Subgroup.zpowers r).subgroupOf R := by rw [hz]; trivial
    exact hzR (Subgroup.mem_subgroupOf.1 this)
  have hPK : P ≤ K := by rw [← hER]; exact sup_le hEK hRK
  apply hfix
  have hbot := IrreducibleNormalFixedSpace.fixedSpace_eq_bot σ hinj hirr P hP
  rw [eq_bot_iff]
  intro w hw
  have : w ∈ Representation.invariants (σ.comp P.subtype) := by
    rw [Representation.mem_invariants]
    intro g
    exact hPK g.2 w hw
  rw [hbot] at this
  exact this

end CFSG.LinearAlgebra.CoprimeActions.PrimeOrderComplementFixedSpaceFaithfulness

end
