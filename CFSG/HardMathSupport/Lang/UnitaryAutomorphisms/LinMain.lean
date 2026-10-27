module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinOrderThree
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinField
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinDiag
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinNonCube
public import CFSG.LieType.SeitzGeneration.OuterLinearLift

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] {n : ℕ}

theorem hasFixedThreePair_or_irred_lin {ℓ f : ℕ} [Finite K] [hℓ : Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (h3 : 3 ∣ Nat.card K - 1) (hn : 3 ≤ n)
    (hn3 : 3 ∣ n) (β : MulAut (projectiveSL n K)) (hβ3 : β ^ 3 = 1)
    (hβi : β ∉ inner (projectiveSL n K)) :
    HasFixedThreePair β ∨
      (n = 3 ∧ ∃ B : GL (Fin n) K, β = conjAut n K B ∧
        ∃ l : K, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
            l • (1 : Matrix (Fin n) (Fin n) K) ∧ ∀ x : K, x ^ 3 ≠ l) := by
  classical
  obtain ⟨A, σ, hAσ⟩ := exists_conjAut_fieldAut_of_pow_three hn β hβ3
  by_cases hσ : σ = 1
  swap
  · exact Or.inl (hasFixedThreePair_conjAut_fieldAut hK hf h3 hn A σ hσ β hAσ hβ3)
  have hβA : β = conjAut n K A := by rw [hAσ, hσ, map_one, mul_one]
  have hA3 : conjAut n K (A ^ 3) = 1 := by
    rw [map_pow, ← hβA]; exact hβ3
  obtain ⟨c, hcA⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff hn (A ^ 3)).mp hA3
  have hM3 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
      (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    have e := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hcA
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at e
    rw [e]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hcube : ∃ x : K, x ^ 3 = (c : K)
  · obtain ⟨x, hx3⟩ := hcube
    have hx0 : x ≠ 0 := by
      rintro rfl
      have : (c : K) = 0 := by rw [← hx3]; norm_num
      exact c.ne_zero this
    set S : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 x⁻¹ (inv_ne_zero hx0))
      with hS
    have hS1 : conjAut n K S = 1 :=
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff hn S).2 ⟨_, rfl⟩
    have hA'm : ((S * A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        x⁻¹ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [Units.val_mul, hS, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    have hA'3 : (S * A) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hA'm, smul_pow, hM3, ← hx3, smul_smul, Units.val_one]
      have : x⁻¹ ^ 3 * x ^ 3 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow]
      rw [this, one_smul]
    have hβA' : β = conjAut n K (S * A) := by
      rw [map_mul, hS1, one_mul, hβA]
    have hdet : n = 3 → ((S * A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 1 := by
      intro _ hd1
      apply hβi
      let X : Matrix.SpecialLinearGroup (Fin n) K := ⟨((S * A : GL (Fin n) K) : Matrix _ _ K), hd1⟩
      have hX : Matrix.SpecialLinearGroup.toGL X = S * A := Units.ext rfl
      have : β = MulAut.conj (proj n K X) := by
        rw [← CFSG.LieType.SeitzGeneration.conjAut_toGL, hX]; exact hβA'
      rw [this]
      exact ⟨proj n K X, rfl⟩
    refine Or.inl ?_
    rw [hβA']
    exact hasFixedThreePair_conjAut_of_pow_three hK hf h3 hn (S * A) hA'3 hdet
  · have hnc : ∀ x : K, x ^ 3 ≠ (c : K) := fun x hx => hcube ⟨x, hx⟩
    by_cases hn6 : 6 ≤ n
    · exact Or.inl (by
        rw [hβA]
        exact hasFixedThreePair_conjAut_of_nonCube hK hf h3 hn6 A hM3 hnc)
    · have hn3' : n = 3 := by
        obtain ⟨k, hk⟩ := hn3
        omega
      exact Or.inr ⟨hn3', A, hβA, (c : K), hM3, hnc⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
