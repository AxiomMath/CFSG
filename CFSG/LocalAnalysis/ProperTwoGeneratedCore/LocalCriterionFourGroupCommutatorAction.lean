module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG
open scoped IsMulCommutative

universe u v

variable {A : Type u} [Group A] {I : Type v} [Group I]
variable [MulDistribMulAction A I]

def actorFixedSubgroup (a : A) : Subgroup I :=
  (MulDistribMulAction.toMulAut A I a).toMonoidHom.eqLocus (MonoidHom.id I)

@[simp] theorem mem_actorFixedSubgroup (a : A) (x : I) :
    x ∈ actorFixedSubgroup (I := I) a ↔ a • x = x := Iff.rfl

def actorCommutatorSubgroup (b : A) (J : Subgroup I) : Subgroup I :=
  Subgroup.closure {x : I | ∃ y ∈ J, x = y⁻¹ * (b • y)}

theorem actorCommutatorSubgroup_le (b : A) (J K : Subgroup I) :
    actorCommutatorSubgroup b J ≤ K ↔ ∀ x ∈ J, x⁻¹ * (b • x) ∈ K := by
  rw [actorCommutatorSubgroup, Subgroup.closure_le]
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h x hx

theorem actorCommutatorSubgroup_generator_mem (b : A) {J : Subgroup I}
    {x : I} (hx : x ∈ J) : x⁻¹ * (b • x) ∈ actorCommutatorSubgroup b J :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

theorem actorCommutatorSubgroup_mono (b : A) {J K : Subgroup I} (hJK : J ≤ K) :
    actorCommutatorSubgroup b J ≤ actorCommutatorSubgroup b K := by
  apply (actorCommutatorSubgroup_le b J _).2
  intro x hx
  exact actorCommutatorSubgroup_generator_mem b (hJK hx)

theorem actorCommutatorSubgroup_le_self (b : A) (J : Subgroup I)
    [IsInvariant A I J] : actorCommutatorSubgroup b J ≤ J := by
  apply (actorCommutatorSubgroup_le b J J).2
  intro x hx
  exact J.mul_mem (J.inv_mem hx)
    ((IsInvariant.invariant (A := A) (G := I) (H := J) b x).1 hx)

theorem actorCommutatorSubgroup_eq_bot_of_fixed (b : A) (J : Subgroup I)
    (hfixed : ∀ x ∈ J, b • x = x) : actorCommutatorSubgroup b J = ⊥ := by
  apply le_antisymm _ bot_le
  apply (actorCommutatorSubgroup_le b J ⊥).2
  intro x hx
  simp [hfixed x hx]

theorem actor_smul_comm [IsMulCommutative A] (a b : A) (x : I) :
    a • (b • x) = b • (a • x) := by
  rw [← mul_smul, ← mul_smul, mul_comm a b]

theorem actorFixedSubgroup_invariant [IsMulCommutative A] (b : A) :
    IsInvariant A I (actorFixedSubgroup (I := I) b) := by
  refine ⟨?_⟩
  intro a x
  simp only [mem_actorFixedSubgroup]
  constructor
  · intro hx
    rw [actor_smul_comm b a, hx]
  · intro hx
    have h := congrArg (fun y : I => a⁻¹ • y) hx
    simpa only [actor_smul_comm b a, inv_smul_smul] using h

theorem actorCommutatorSubgroup_invariant [IsMulCommutative A] (b : A)
    (J : Subgroup I) [IsInvariant A I J] :
    IsInvariant A I (actorCommutatorSubgroup b J) := by
  have hforward (a : A) (x : I) (hx : x ∈ actorCommutatorSubgroup b J) :
      a • x ∈ actorCommutatorSubgroup b J := by
    refine Subgroup.closure_induction (p := fun y _ =>
      a • y ∈ actorCommutatorSubgroup b J) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨y, hy, rfl⟩
      have hay : a • y ∈ J :=
        (IsInvariant.invariant (A := A) (G := I) (H := J) a y).1 hy
      simpa only [smul_mul', smul_inv', actor_smul_comm a b] using
        actorCommutatorSubgroup_generator_mem b hay
    · simp [actorCommutatorSubgroup]
    · intro y z _ _ hy hz
      simpa only [smul_mul'] using (actorCommutatorSubgroup b J).mul_mem hy hz
    · intro y _ hy
      simpa only [smul_inv'] using (actorCommutatorSubgroup b J).inv_mem hy
  refine ⟨?_⟩
  intro a x
  constructor
  · exact hforward a x
  · intro hx
    simpa only [inv_smul_smul] using hforward a⁻¹ (a • x) hx

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
