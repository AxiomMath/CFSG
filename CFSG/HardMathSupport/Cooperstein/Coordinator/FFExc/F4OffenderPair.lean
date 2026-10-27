module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4Offender26
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinPair

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem posU6_eq_posUnip : posU6 K = posUnip e6Data_valid K := by
  simp only [posU6, posUnip, one_mul]

theorem comm_of_sq_eq_one {G : Type*} [Group G] {A : Subgroup G} (hel : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h1 := hel _ (A.mul_mem ha hb)
  have h2 := hel a ha
  have h3 := hel b hb
  have e : a * b = (a * b)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← sq]; exact h1
  have ia : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact h2
  have ib : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact h3
  rw [e, _root_.mul_inv_rev, ia, ib]

theorem f4_26_twist_offender_bound_of_fixedSub
    (hfix : ∀ A : Subgroup (e6Data_valid.minGroup K),
      fixedSub (hV := e6Data_valid) (k := K) A = fixSub e6Data_valid A) (k : ℕ)
    {A : Subgroup (adjointGroup Tag.F4 K)} (hne : A ≠ ⊥) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card (fix26 K k A) ≤ Nat.card K ^ 25 ∧
      Nat.card A ^ 2 * Nat.card (fix26 K k A) ≤ Nat.card K ^ 41 := by
  refine f4_26_twist_offender_bound K k (fun B hB hBne hBel => ?_) hne hel
  have := e6_27_pair_bound K (A := B) (by rwa [← posU6_eq_posUnip]) (comm_of_sq_eq_one hBel) hBne
  simpa only [hfix] using this

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
