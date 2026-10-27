module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.Finite

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.SemiregularFiniteSetCardDivisibility

theorem card_dvd_pred {B : Type*} [Group B] [Finite B] {X : Type*} [Finite X] [MulAction B X]
    (x0 : X) (hfix : ∀ b : B, b • x0 = x0)
    (hfree : ∀ b : B, b ≠ 1 → ∀ x : X, x ≠ x0 → b • x ≠ x) :
    Nat.card B ∣ Nat.card X - 1 := by
  classical
  let Y := {x : X // x ≠ x0}
  letI : MulAction B Y :=
    { smul := fun b y => ⟨b • y.1, fun h => y.2 (by
        have := congrArg (fun z => b⁻¹ • z) h
        simpa [hfix] using this)⟩
      one_smul := fun y => Subtype.ext (one_smul _ _)
      mul_smul := fun a b y => Subtype.ext (mul_smul _ _ _) }
  have hY : Nat.card Y = Nat.card X - 1 := by
    have h := Nat.card_congr (Equiv.sumCompl (fun x : X => x = x0))
    rw [Nat.card_sum] at h
    have h1 : Nat.card {x : X // x = x0} = 1 := by simp
    have h2 : Nat.card {x : X // ¬ x = x0} = Nat.card Y := rfl
    omega
  have hstab : ∀ y : Y, MulAction.stabilizer B y = ⊥ := by
    intro y
    rw [eq_bot_iff]
    intro b hb
    by_contra hne
    exact hfree b hne y.1 y.2 (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hb))
  have : Nat.card B ∣ Nat.card Y := by
    haveI : Finite Y := Subtype.finite
    haveI : Fintype (MulAction.orbitRel.Quotient B Y) := Fintype.ofFinite _
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits B Y), Nat.card_sigma]
    apply Finset.dvd_sum
    intro ω _
    generalize ω.out = y
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup B y)
    rw [Nat.card_prod] at h
    have h1 : Nat.card (MulAction.stabilizer B y) = 1 := by
      rw [hstab y]; simp
    rw [h1, mul_one] at h
    exact h ▸ dvd_rfl
  rwa [hY] at this

end CFSG.GroupTheory.CoprimeActionSupport.SemiregularFiniteSetCardDivisibility
