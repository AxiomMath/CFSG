module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ISetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

structure Sec4IFrame (Q : QuadraticForm (ZMod 3) V) where
  b : Module.Basis (Fin 7) (ZMod 3) V
  neg : ∀ i, Q (b i) = -1
  orth : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0

theorem Sec4IFrame.map_eq (fr : Sec4IFrame Q) (x : V) : Q x = -∑ i, (fr.b.repr x i) ^ 2 := by
  have hortho : (QuadraticMap.associated (R := ZMod 3) Q).IsOrthoᵢ fr.b := by
    intro i j hij
    show QuadraticMap.associated (R := ZMod 3) Q (fr.b i) (fr.b j) = 0
    rw [QuadraticMap.associated_apply]
    have h := fr.orth i j hij
    rw [QuadraticMap.polar] at h
    rw [h, smul_zero]
  have h := congrArg (fun R => R (fr.b.equivFun x))
    (QuadraticMap.basisRepr_eq_of_iIsOrtho Q fr.b hortho)
  simp only [QuadraticMap.basisRepr_apply, Module.Basis.sum_equivFun,
    QuadraticMap.weightedSumSquares_apply] at h
  rw [h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fr.neg i, smul_eq_mul, Module.Basis.equivFun_apply, _root_.sq]
  ring

private theorem linearIndependent_of_polar {ι : Type} [Fintype ι] (v : ι → V)
    (h0 : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i) (v j) = 0)
    (h1 : ∀ i, QuadraticMap.polar Q (v i) (v i) ≠ 0) : LinearIndependent (ZMod 3) v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun x => QuadraticMap.polar Q x (v j)) hg
  simp only [QuadraticMap.polar_zero_left] at h
  have hsum : QuadraticMap.polar Q (∑ i, g i • v i) (v j) =
      g j * QuadraticMap.polar Q (v j) (v j) := by
    rw [← QuadraticMap.polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · intro i _ hij
      rw [h0 i j hij, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hsum] at h
  exact (mul_eq_zero.mp h).resolve_right (h1 j)

private def eV (i : Fin 3) : Sec4IV := Pi.single (Sum.inl i) 1

private def fV (i : Fin 3) : Sec4IV := Pi.single (Sum.inr (Sum.inl i)) 1

private def wV : Sec4IV := Pi.single (Sum.inr (Sum.inr ())) 1

private def frameVec : Fin 7 → Sec4IV :=
  ![eV 0 - fV 0, eV 1 - fV 1, eV 2 - fV 2, (eV 0 + fV 0) + (eV 1 + fV 1),
    (eV 0 + fV 0) - (eV 1 + fV 1), (eV 2 + fV 2) + wV, (eV 2 + fV 2) - wV]

private theorem frameVec_neg : ∀ i, Sec4IQ (frameVec i) = -1 := by
  intro i
  simp only [Sec4IQ, CFSG.LieType.Universal.Spin.quadOdd_apply]
  revert i
  decide

private theorem frameVec_orth : ∀ i j, i ≠ j →
    QuadraticMap.polar Sec4IQ (frameVec i) (frameVec j) = 0 := by
  intro i j
  simp only [QuadraticMap.polar, Sec4IQ, CFSG.LieType.Universal.Spin.quadOdd_apply]
  revert i j
  decide

theorem sec4I_exists_frame : Nonempty (Sec4IFrame Sec4IQ) := by
  have hli : LinearIndependent (ZMod 3) frameVec := by
    refine linearIndependent_of_polar frameVec frameVec_orth fun i => ?_
    intro h
    have h2 : QuadraticMap.polar Sec4IQ (frameVec i) (frameVec i) = 2 * Sec4IQ (frameVec i) := by
      rw [QuadraticMap.polar_self, two_smul, two_mul]
    rw [h2, frameVec_neg] at h
    revert h
    decide
  exact ⟨⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [sec4IQ_finrank]; rfl),
    by simpa using frameVec_neg, by simpa using frameVec_orth⟩⟩

end CFSG.OddStandard.SmallF3.Omega
