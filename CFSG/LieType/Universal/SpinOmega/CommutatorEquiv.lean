module

public import CFSG.ClassicalGroups.Orthogonal.IsometryConj
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {n : ℕ} {K : Type} [Field K]

noncomputable def spinEquivCommutatorQuadPlus (hn : 3 ≤ n) (h2 : (2 : K) = 0) :
    spinGroup (quadPlus n K) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆ := by
  haveI : Algebra.IsCentral K (CliffordAlgebra (quadPlus n K)) :=
    isCentral_cliffordAlgebra_quadPlus (K := K) (n := n)
  have hf : Function.Injective (spinAction (quadPlus n K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinAction_eq_bot_of_isCentral (quadPlus n K) h2)
  exact (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (range_spinAction_quadPlus_eq_commutator hn))

@[simp]
theorem coe_spinEquivCommutatorQuadPlus_apply (hn : 3 ≤ n) (h2 : (2 : K) = 0)
    (x : spinGroup (quadPlus n K)) :
    ((spinEquivCommutatorQuadPlus hn h2 x :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆) :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) =
      spinAction (quadPlus n K) x := by
  rw [spinEquivCommutatorQuadPlus, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

variable {b c : K}

noncomputable def spinEquivCommutatorQuadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0) :
    spinGroup (quadMinus n K b c) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ := by
  haveI : Algebra.IsCentral K (CliffordAlgebra (quadMinus n K b c)) :=
    isCentral_cliffordAlgebra_quadMinus n b c hirr
  have hf : Function.Injective (spinAction (quadMinus n K b c)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinAction_eq_bot_of_isCentral (quadMinus n K b c) h2)
  exact (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (range_spinAction_quadMinus_eq_commutator hn hirr))

@[simp]
theorem coe_spinEquivCommutatorQuadMinus_apply [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0)
    (x : spinGroup (quadMinus n K b c)) :
    ((spinEquivCommutatorQuadMinus hn hirr h2 x :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆) :
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) =
      spinAction (quadMinus n K b c) x := by
  rw [spinEquivCommutatorQuadMinus, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

section Isometry

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

noncomputable def commutatorEquivSpinPlusOfIsometry (e : Q.IsometryEquiv (quadPlus n K))
    (hn : 3 ≤ n) (h2 : (2 : K) = 0) :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≃* spinGroup (quadPlus n K) :=
  (commutatorOrthogonalGroupCongr e).trans (spinEquivCommutatorQuadPlus hn h2).symm

@[simp]
theorem spinAction_commutatorEquivSpinPlusOfIsometry_apply
    (e : Q.IsometryEquiv (quadPlus n K)) (hn : 3 ≤ n) (h2 : (2 : K) = 0)
    (g : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    spinAction (quadPlus n K) (commutatorEquivSpinPlusOfIsometry e hn h2 g) =
      LinearEquiv.autCongr e.toLinearEquiv (g : V ≃ₗ[K] V) := by
  rw [commutatorEquivSpinPlusOfIsometry, MulEquiv.trans_apply,
    ← coe_spinEquivCommutatorQuadPlus_apply hn h2, MulEquiv.apply_symm_apply,
    coe_commutatorOrthogonalGroupCongr_apply, LinearEquiv.autCongr_apply]

noncomputable def commutatorEquivSpinMinusOfIsometry [Finite K]
    (e : Q.IsometryEquiv (quadMinus n K b c)) (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0) :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≃* spinGroup (quadMinus n K b c) :=
  (commutatorOrthogonalGroupCongr e).trans
    (spinEquivCommutatorQuadMinus hn hirr h2).symm

@[simp]
theorem spinAction_commutatorEquivSpinMinusOfIsometry_apply [Finite K]
    (e : Q.IsometryEquiv (quadMinus n K b c)) (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0)
    (g : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    spinAction (quadMinus n K b c) (commutatorEquivSpinMinusOfIsometry e hn hirr h2 g) =
      LinearEquiv.autCongr e.toLinearEquiv (g : V ≃ₗ[K] V) := by
  rw [commutatorEquivSpinMinusOfIsometry, MulEquiv.trans_apply,
    ← coe_spinEquivCommutatorQuadMinus_apply hn hirr h2, MulEquiv.apply_symm_apply,
    coe_commutatorOrthogonalGroupCongr_apply, LinearEquiv.autCongr_apply]

end Isometry

end CFSG.LieType.Universal.Spin
