module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Basic
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Weyl
public import CFSG.LieType.Steinberg.PartB

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CliffordAlgebra QuadraticMap

section Short

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

theorem shortSL2_injective (F : OddFrame Q n) (i : Fin n) (s : Bool) :
    Function.Injective (F.shortSL2 i s) := by
  intro M N h
  have hX : (F.shortPair i s).X ≠ 0 := ι_mul_ι_ne_zero Q (F.linearIndependent_z_vec i s)
  have hY : (F.shortPair i s).Y ≠ 0 := fun h0 => hX (by
    rw [← (F.shortPair i s).X_mul_Y_mul_X, h0, zero_mul, mul_zero])
  have h' := congrArg (fun g : spinGroup Q => (g : CliffordAlgebra Q)) h
  simp only [OddFrame.coe_shortSL2] at h'
  exact Subtype.ext (SpinFrame.sl2Pair_toFun_injective _ hX hY h')

end Short

variable {n : ℕ} {K : Type} [Field K]

theorem rankOneB_injective (k : Fin n) : Function.Injective (rankOneB K k) := by
  by_cases hk : k.val + 1 < n
  · rw [rankOneB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp))]
    exact SpinFrame.longSL2_injective _ _ _ _
  · rw [rankOneB_of_not_lt K hk]
    exact shortSL2_injective _ _ _

theorem rankOne (i : Fin n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* spinGroup (quadOdd n K), Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = x n K (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = x n K (-Pi.single i 1) c :=
  ⟨rankOneB K i, rankOneB_injective i,
    fun c => (rankOneB_upperSL2 K i c).trans (x_single i c).symm,
    fun c => (rankOneB_lowerSL2 K i c).trans (x_neg_single i c).symm⟩

end CFSG.LieType.Steinberg.SpinOdd
