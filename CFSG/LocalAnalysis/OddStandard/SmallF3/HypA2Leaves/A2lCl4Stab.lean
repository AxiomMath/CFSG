module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Eps

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {X : Type*} [MulAction (elementaryGroup Q) X]

@[expose] def cl24_D (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1) (P : HypPair Q) (y : X) :
    Submodule K P.perp where
  carrier := {w | cl24_eps P w • y = y}
  zero_mem' := by
    show cl24_eps P 0 • y = y
    rw [cl24_eps_zero, one_smul]
  add_mem' := by
    intro a b ha hb
    show cl24_eps P (a + b) • y = y
    rw [cl24_eps_add, mul_smul]
    exact (congrArg (cl24_eps P a • ·) hb).trans ha
  smul_mem' := by
    intro c w hw
    show cl24_eps P (c • w) • y = y
    rcases hK c with rfl | rfl | rfl
    · rw [zero_smul, cl24_eps_zero, one_smul]
    · rw [one_smul]
      exact hw
    · rw [neg_one_smul, cl24_eps_neg]
      exact inv_smul_eq_iff.mpr hw.symm

theorem cl24_mem_D (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1) (P : HypPair Q) (y : X)
    (w : P.perp) : w ∈ cl24_D hK P y ↔ cl24_eps P w • y = y :=
  Iff.rfl

@[expose] def cl24_Rorb (P : HypPair Q) (y : X) : Set X :=
  Set.range fun w : P.perp => cl24_eps P w • y

theorem cl24_card_Rorb_mul_card_D (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1)
    (P : HypPair Q) [Finite P.perp] (y : X) :
    Nat.card (cl24_Rorb P y) * Nat.card (cl24_D hK P y) = Nat.card P.perp := by
  letI : MulAction (Multiplicative P.perp) X := MulAction.compHom X (cl24_epsHom P)
  have horb : MulAction.orbit (Multiplicative P.perp) y = cl24_Rorb P y := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Multiplicative.toAdd a, MulAction.compHom_smul_def (cl24_epsHom P) a y⟩
    · rintro ⟨w, rfl⟩
      exact ⟨Multiplicative.ofAdd w,
        MulAction.compHom_smul_def (cl24_epsHom P) (Multiplicative.ofAdd w) y⟩
  have hstab : Nat.card (MulAction.stabilizer (Multiplicative P.perp) y)
      = Nat.card (cl24_D hK P y) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun a => ?_)
    rw [MulAction.mem_stabilizer_iff, cl24_mem_D, MulAction.compHom_smul_def]
    rfl
  have hcard : Nat.card (Multiplicative P.perp) = Nat.card P.perp :=
    Nat.card_congr Multiplicative.toAdd
  rw [← horb, ← hstab, ← hcard, mul_comm,
    ← Subgroup.card_mul_index (MulAction.stabilizer (Multiplicative P.perp) y),
    MulAction.index_stabilizer, Nat.card_coe_set_eq]

theorem cl24_D_of_mem_Rorb (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1) (P : HypPair Q) {y z : X}
    (hz : z ∈ cl24_Rorb P y) : cl24_D hK P z = cl24_D hK P y := by
  obtain ⟨v, rfl⟩ := hz
  refine Submodule.ext fun w => ?_
  rw [cl24_mem_D, cl24_mem_D]
  constructor
  · intro h
    have h2 : cl24_eps P v • (cl24_eps P w • y) = cl24_eps P v • y := by
      rw [← mul_smul, ← cl24_eps_add, add_comm, cl24_eps_add, mul_smul]
      exact h
    exact smul_left_cancel (cl24_eps P v) h2
  · intro h
    rw [← mul_smul, ← cl24_eps_add, add_comm, cl24_eps_add, mul_smul, h]

end CFSG.OddStandard.SmallF3.HypA2Leaves
