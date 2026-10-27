module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem mem_matrixDerived_of_pow_eq_one_of_odd
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q) {n : ℕ} (hn : Odd n) (hAn : A ^ n = 1) :
    A ∈ matrixDerived Q := by
  obtain ⟨m, hm⟩ := hab
  have hfin : Finite (Abelianization (matrixIsometries Q)) :=
    Nat.finite_of_card_ne_zero (by rw [hm]; exact (pow_pos two_pos m).ne')
  set x := Abelianization.of (⟨A, hA⟩ : matrixIsometries Q) with hx
  have hxn : x ^ n = 1 := by
    rw [hx, ← map_pow]
    have : (⟨A, hA⟩ : matrixIsometries Q) ^ n = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hAn)
    rw [this, map_one]
  have h1 : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hxn
  have h2 : orderOf x ∣ 2 ^ m := hm ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime n (2 ^ m) := Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hn)
  have hx1 : x = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hmem : (⟨A, hA⟩ : matrixIsometries Q) ∈ commutator (matrixIsometries Q) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hx1
  rw [matrixDerived_eq_map_commutator]
  exact ⟨_, hmem, rfl⟩

theorem matrixDerived_le_isomGL : matrixDerived Q ≤ Cls.isomGL (polarBilin Q) := by
  intro A hA
  have hQ := (mem_matrixIsometries_iff Q A).1 (matrixDerived_le_isometries Q hA)
  rw [Cls.mem_isomGL]
  intro x y
  have hx : ∀ v, Q ((A : Matrix (Fin d) (Fin d) K) *ᵥ v) = Q v := fun v => by
    rw [← matrixLinearEquiv_apply]
    exact hQ v
  simp only [polarBilin_apply_apply, polar, ← Matrix.mulVec_add, hx]

theorem mem_matrixIsometries_of_mem_isomGL (h2 : (2 : K) ≠ 0) {g : GL (Fin d) K}
    (hg : g ∈ Cls.isomGL (polarBilin Q)) : g ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff]
  intro v
  have h1 := Cls.mem_isomGL.1 hg v v
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_self, polar_self, two_smul,
    two_smul, ← two_mul, ← two_mul] at h1
  rw [matrixLinearEquiv_apply]
  exact mul_left_cancel₀ h2 h1

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
