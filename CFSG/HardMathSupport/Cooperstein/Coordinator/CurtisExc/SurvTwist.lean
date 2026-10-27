module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Twist
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.SmithCurtisChevAmb

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

section Dim

variable {k : Type} [Field k]

theorem finrank_frobTwist (θ : k ≃+* k) (V : Type) [AddCommGroup V] [Module k V] :
    Module.finrank k (FrobTwist θ V) = Module.finrank k V := by
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv θ (AddEquiv.refl V) θ.bijective (fun r v => rfl)

theorem finrank_invariants_twist (θ : k ≃+* k) {G V : Type} [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Module.finrank k ↥(Representation.invariants (twistRep θ ρ)) =
      Module.finrank k ↥(Representation.invariants ρ) := by
  unfold Module.finrank
  congr 1
  refine rank_eq_of_equiv_equiv θ
    { toFun := fun v => ⟨(show V from v.1), fun g => v.2 g⟩
      invFun := fun v => ⟨(show FrobTwist θ V from v.1), fun g => v.2 g⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl
      map_add' := fun v w => rfl } θ.bijective (fun r v => rfl)

end Dim

section Frob

variable {k : Type} [Field k] [Finite k] [CharP k 2]

@[expose] def frobAut (k : Type) [Field k] [Finite k] [CharP k 2] (b : ℕ) : k ≃+* k :=
  have : ExpChar k 2 := ExpChar.prime Nat.prime_two
  iterateFrobeniusEquiv k 2 b

theorem frobAut_apply (b : ℕ) (c : k) : frobAut k b c = c ^ (2 ^ b) := by
  have : ExpChar k 2 := ExpChar.prime Nat.prime_two
  show iterateFrobenius k 2 b c = _
  rw [iterateFrobenius_def]

theorem frobAut_symm_pow (b : ℕ) (c : k) : (frobAut k b).symm (c ^ (2 ^ b)) = c := by
  rw [RingEquiv.symm_apply_eq, frobAut_apply]

end Frob

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
