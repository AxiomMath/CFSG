module

public import CFSG.Blueprint.ChevalleyPinned
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


theorem entryDegreeBound_of_ne_G2 {τ : Tag} (hτ : τ ≠ .G2) : entryDegreeBound τ = 2 := by
  simp [entryDegreeBound, hτ]

theorem pinnedData_sign (τ : Tag) (α : Fin τ.rank → ℤ) :
    (pinnedData τ α).2.2 = 1 ∨ (pinnedData τ α).2.2 = -1 := by
  unfold pinnedData
  split_ifs <;> simp

theorem xCoeff_zero_eq_one {τ : Tag} {L : Type} [Field L] (hτ : τ ≠ .G2) (j : Fin τ.rank) :
    xCoeff τ L j 0 = 1 := by
  have h := xOp_eq_sum_xCoeff_entryDegreeBound (R := L) τ j 0
  rw [xOp_zero, entryDegreeBound_of_ne_G2 hτ] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  simpa using h.symm

theorem xCoeff_one_ne_zero {τ : Tag} {L : Type} [Field L] (j : Fin τ.rank) :
    xCoeff τ L j 1 ≠ 0 := by
  intro h
  have h1 := xCoeff_rootVec_neg_single (R := L) (τ := τ) j 1
  rw [h] at h1
  simp only [LinearMap.zero_apply, one_ne_zero, ↓reduceIte] at h1
  have : (hVec τ L j : RootModule τ L) = Finsupp.single (Sum.inl j) 1 := rfl
  rw [this] at h1
  exact one_ne_zero (Finsupp.single_eq_zero.1 h1.symm)

theorem pinnedX_expand {τ : Tag} {L : Type} [Field L] (hτ : τ ≠ .G2) (α : Fin τ.rank → ℤ) :
    ∃ A B : Module.End L (RootModule τ L), A ≠ 0 ∧
      (SimplyLacedTag τ → 2 ≤ Module.finrank L (LinearMap.range A) ∧
        Module.finrank L (LinearMap.range B) ≤ 1) ∧ ∀ c : L,
      ((pinnedX τ L α c : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) =
        1 + c • A + c ^ 2 • B := by
  set j := (pinnedData τ α).1 with hj
  set ε := (pinnedData τ α).2.2 with hε
  set W := pinnedWeyl τ L α with hW
  set e : L := (ε : L) with he
  have hεs : ε = 1 ∨ ε = -1 := pinnedData_sign τ α
  have he0 : e ≠ 0 := by
    rcases hεs with h | h <;> simp [he, h]
  have hx : ∀ c : L, xOp τ L j c = 1 + c • xCoeff τ L j 1 + c ^ 2 • xCoeff τ L j 2 := by
    intro c
    rw [xOp_eq_sum_xCoeff_entryDegreeBound, entryDegreeBound_of_ne_G2 hτ]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul,
      xCoeff_zero_eq_one hτ, pow_one]
  refine ⟨e • ((W : Module.End L (RootModule τ L)) * xCoeff τ L j 1 *
      ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L))),
    e ^ 2 • ((W : Module.End L (RootModule τ L)) * xCoeff τ L j 2 *
      ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L))), ?_, ?_,
    fun c => ?_⟩
  · intro h0
    have h1 : ((W : Module.End L (RootModule τ L)) * xCoeff τ L j 1 *
        ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L))) = 0 := by
      rcases smul_eq_zero.1 h0 with h | h
      · exact absurd h he0
      · exact h
    have h2 : xCoeff τ L j 1 = 0 := by
      have := congrArg (fun m => ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) :
        Module.End L (RootModule τ L)) * m * (W : Module.End L (RootModule τ L))) h1
      simpa [mul_assoc] using this
    exact xCoeff_one_ne_zero j h2
  · intro hsl
    constructor
    · rw [finrank_range_smul_eq he0, finrank_range_conj_eq]
      exact xCoeff_one_range_ge hsl j
    · refine (finrank_range_smul_le _ _).trans ?_
      refine (finrank_range_conj_le W _).trans ?_
      exact xCoeff_two_range_le hsl j
  · have hp : ((pinnedX τ L α c : (Module.End L (RootModule τ L))ˣ) :
        Module.End L (RootModule τ L)) =
        (W : Module.End L (RootModule τ L)) * xOp τ L j (e * c) *
          ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) := by
      change ((W * xUnit τ L j (ε • c) * W⁻¹ : (Module.End L (RootModule τ L))ˣ) :
        Module.End L (RootModule τ L)) = _
      rw [Units.val_mul, Units.val_mul, coe_xUnit]
      congr 3
      simp [he, mul_comm]
    rw [hp, hx (e * c)]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul, mul_one]
    have hWW : (W : Module.End L (RootModule τ L)) *
        ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hWW]
    congr 2 <;> congr 1 <;> ring

end CFSG.HardMathSupport.Timmesfeld.LangTorus
