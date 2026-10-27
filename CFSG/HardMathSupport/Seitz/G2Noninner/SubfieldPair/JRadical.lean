module

public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.FormOdd
public import CFSG.RankThree.PartOne.SEITZ6.G2Span
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6

variable {K : Type} [Field K]

@[expose] def jTriv (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) where
  carrier := {h | ∀ x y : RootModule .G2 K, jFormO K x (h • y) = jFormO K x y}
  one_mem' := by
    intro x y
    simp
  mul_mem' := by
    intro a b ha hb x y
    rw [mul_smul, ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha x (a⁻¹ • y)
    rw [smul_inv_smul] at this
    exact this.symm

section Certs


theorem jFormO_smul_right (g : adjointGroup .G2 K) (x y : RootModule .G2 K) :
    jFormO K x (g • y) = jFormO K (g⁻¹ • x) y := by
  have := jFormO_invariant g (g⁻¹ • x) y
  rwa [smul_inv_smul] at this

instance : (jTriv K).Normal where
  conj_mem := by
    intro n hn g x y
    show jFormO K x ((g * n * g⁻¹) • y) = jFormO K x y
    rw [mul_smul, mul_smul, jFormO_smul_right g, hn, ← jFormO_smul_right g, smul_inv_smul]

theorem jFormO_xp0_diff :
    jFormO K (Finsupp.single (toLabel (Tag.rootCertificate_check .G2)
        (Sum.inr ⟨2, by decide⟩ : GIdx)) 1)
      ((xp 0 (1 : K) : adjointGroup .G2 K) •
        Finsupp.single (toLabel (Tag.rootCertificate_check .G2) (Sum.inl e0 : GIdx)) 1) -
    jFormO K (Finsupp.single (toLabel (Tag.rootCertificate_check .G2)
        (Sum.inr ⟨2, by decide⟩ : GIdx)) 1)
      (Finsupp.single (toLabel (Tag.rootCertificate_check .G2) (Sum.inl e0 : GIdx)) 1) = 2 := by
  set a : GIdx := Sum.inr ⟨2, by decide⟩ with ha
  set b : GIdx := Sum.inl e0 with hb
  set y : RootModule .G2 K := Finsupp.single (toLabel (Tag.rootCertificate_check .G2) b) 1
    with hy
  have hsum : xOp .G2 K e0 1 y = y + xCoeff .G2 K e0 1 y + xCoeff .G2 K e0 2 y +
      xCoeff .G2 K e0 3 y := by
    rw [xOp_eq_sum_xCoeff]
    simp [Finset.sum_range_succ, xCoeff_zero]
  have hk : ∀ k : ℕ, xCoeff .G2 K e0 k y =
      toVec (Tag.rootCertificate_check .G2) K
        (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) e0 k b) := fun k =>
    xCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) e0 k b
  have e1 : jColRO a (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) e0 1 b) = 2 := by
    decide +kernel
  have e2 : jColRO a (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) e0 2 b) = 0 := by
    decide +kernel
  have e3 : jColRO a (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) e0 3 b) = 0 := by
    decide +kernel
  rw [xp0_smul, hsum, map_add, map_add, map_add, hk 1, hk 2, hk 3, jFormO_single_toVec,
    jFormO_single_toVec, jFormO_single_toVec, e1, e2, e3]
  push_cast
  ring

theorem xp0_not_mem_jTriv (h2 : (2 : K) ≠ 0) : (xp 0 (1 : K) : adjointGroup .G2 K) ∉ jTriv K := by
  intro h
  have := h (Finsupp.single (toLabel (Tag.rootCertificate_check .G2)
        (Sum.inr ⟨2, by decide⟩ : GIdx)) 1)
    (Finsupp.single (toLabel (Tag.rootCertificate_check .G2) (Sum.inl e0 : GIdx)) 1)
  have h0 := jFormO_xp0_diff (K := K)
  rw [this, sub_self] at h0
  exact h2 h0.symm

theorem jTriv_eq_bot [Finite K]
    (h2 : (2 : K) ≠ 0) : jTriv K = ⊥ := by
  have hK3 : 3 ≤ Nat.card K := by
    have hinj : Function.Injective (fun i : Fin 3 => (![0, 1, -1] : Fin 3 → K) i) := by
      have h1 : (1 : K) ≠ -1 := fun e => h2 (by linear_combination e)
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
        first | exact absurd hij h1 | exact absurd hij.symm h1
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hsimple : IsSimpleGroup (adjointGroup .G2 K) :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (jTriv K) with h | h
  · exact h
  · exact absurd (h ▸ Subgroup.mem_top _) (xp0_not_mem_jTriv h2)

end Certs

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
