module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.QuasithinUnique

theorem frattini_eq_bot_of_exponent_two {Y : Type*} [Group Y] [Finite Y] [Fact (IsPGroup 2 Y)]
    (hcomm : ∀ a b : Y, a * b = b * a) (hsq : ∀ y : Y, y ^ 2 = 1) : frattini Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), eq_bot_iff, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | ⟨y, rfl⟩
  · have : (commutator Y : Subgroup Y) ≤ ⊥ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      simp [commutatorElement_def, hcomm a b]
    exact this hx
  · simpa using hsq y

theorem comm_of_exponent_two {Y : Type*} [Group Y] (hsq : ∀ y : Y, y * y = 1) (a b : Y) :
    a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq (a * b))
  rw [mul_inv_rev, ha, hb] at hab
  exact hab.symm

theorem sq_eq_one_of_frattini_eq_bot {Y : Type*} [Group Y] [Finite Y] [Fact (IsPGroup 2 Y)]
    (hfr : frattini Y = ⊥) (y : Y) : y * y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.frattini_eq_closure_commutator_union_powers (p := 2) (R := Y)
  have hy : y ^ 2 ∈ frattini Y := by
    rw [h]
    exact Subgroup.subset_closure (Or.inr ⟨y, rfl⟩)
  rw [hfr, Subgroup.mem_bot] at hy
  simpa [sq] using hy

end CFSG.QuasithinUnique
