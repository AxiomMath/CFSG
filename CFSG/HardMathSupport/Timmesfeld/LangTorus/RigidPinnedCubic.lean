module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidPinned

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Conj

variable {L V : Type*} [Field L] [AddCommGroup V] [Module L V]

theorem unit_conj_cubic (W : (Module.End L V)ˣ) (s₁ s₂ s₃ : L) (a b d : Module.End L V) :
    (W : Module.End L V) * (1 + s₁ • a + s₂ • b + s₃ • d) * (↑W⁻¹ : Module.End L V) =
      1 + s₁ • ((W : Module.End L V) * a * (↑W⁻¹ : Module.End L V)) +
        s₂ • ((W : Module.End L V) * b * (↑W⁻¹ : Module.End L V)) +
        s₃ • ((W : Module.End L V) * d * (↑W⁻¹ : Module.End L V)) := by
  have hWW : (W : Module.End L V) * (↑W⁻¹ : Module.End L V) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hWW]

end Conj

section Pinned


theorem xOp_eq_cubic {τ : Tag} {L : Type} [Field L] (j : Fin τ.rank) (c : L) :
    xOp τ L j c = 1 + c • xCoeff τ L j 1 + c ^ 2 • xCoeff τ L j 2 + c ^ 3 • xCoeff τ L j 3 := by
  rw [xOp_eq_sum_xCoeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul,
    xCoeff_zero, pow_one]

theorem pinnedX_expand_cubic {τ : Tag} {L : Type} [Field L] (α : Fin τ.rank → ℤ) :
    ∃ A B C : Module.End L (RootModule τ L), A ≠ 0 ∧ ∀ c : L,
      ((pinnedX τ L α c : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) =
        1 + c • A + c ^ 2 • B + c ^ 3 • C := by
  set j := (pinnedData τ α).1 with hj
  set ε := (pinnedData τ α).2.2 with hε
  set W := pinnedWeyl τ L α with hW
  set e : L := (ε : L) with he
  have hεs : ε = 1 ∨ ε = -1 := pinnedData_sign τ α
  have he0 : e ≠ 0 := by
    rcases hεs with h | h <;> simp [he, h]
  refine ⟨e • ((W : Module.End L (RootModule τ L)) * xCoeff τ L j 1 *
      ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L))),
    e ^ 2 • ((W : Module.End L (RootModule τ L)) * xCoeff τ L j 2 *
      ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L))),
    e ^ 3 • ((W : Module.End L (RootModule τ L)) * xCoeff τ L j 3 *
      ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L))), ?_,
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
  · have hp : ((pinnedX τ L α c : (Module.End L (RootModule τ L))ˣ) :
        Module.End L (RootModule τ L)) =
        (W : Module.End L (RootModule τ L)) * xOp τ L j (e * c) *
          ((W⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) := by
      change ((W * xUnit τ L j (ε • c) * W⁻¹ : (Module.End L (RootModule τ L))ˣ) :
        Module.End L (RootModule τ L)) = _
      rw [Units.val_mul, Units.val_mul, coe_xUnit]
      congr 3
      simp [he, mul_comm]
    rw [hp, xOp_eq_cubic, unit_conj_cubic]
    module

end Pinned

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end
