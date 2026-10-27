module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusMat
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinFrame

section Eps

variable (n : ℕ)

@[expose] def epsFun (hn : 1 ≤ n) : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → Fin (n + n)
  | .inl i => ⟨i.val, by have := i.isLt; omega⟩
  | .inr (.inl i) => ⟨n + n - 1 - i.val, by have := i.isLt; omega⟩
  | .inr (.inr t) => ⟨n - 1 + t.val, by have := t.isLt; omega⟩

theorem epsFun_injective (hn : 1 ≤ n) : Function.Injective (epsFun n hn) := by
  rintro (i | i | t) (j | j | u) h <;> simp only [epsFun, Fin.mk.injEq] at h <;>
    first | (have := i.isLt; have := j.isLt; simp [Fin.ext_iff]; omega) |
      (have := i.isLt; have := u.isLt; omega) | (have := t.isLt; have := j.isLt; omega) |
      (have := t.isLt; have := u.isLt; simp [Fin.ext_iff]; omega) |
      (have := i.isLt; have := t.isLt; omega) | (have := i.isLt; have := j.isLt; omega)

@[expose] noncomputable def epsM (hn : 1 ≤ n) :
    (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) ≃ Fin (n + n) :=
  Equiv.ofBijective (epsFun n hn)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨epsFun_injective n hn, by
      simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩)

theorem epsM_apply (hn : 1 ≤ n) (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    epsM n hn x = epsFun n hn x := rfl

theorem epsM_not (hn : 1 ≤ n) (i : Fin (n - 1)) (r : Bool) :
    epsM n hn (minusPos n i (!r)) = Fin.rev (epsM n hn (minusPos n i r)) := by
  apply Fin.ext
  have := i.isLt
  cases r <;> simp [epsM_apply, epsFun, minusPos, Fin.val_rev] <;> omega

end Eps


section MatM

variable {n : ℕ} {K : Type} [Field K] {b c : K}

@[expose] noncomputable def matM (hn : 1 ≤ n) :
    spinGroup (quadMinus n K b c) →* Matrix (Fin (n + n)) (Fin (n + n)) K :=
  (Matrix.reindexAlgEquiv K K (epsM n hn)).toAlgHom.toMonoidHom.comp (matHom n)

theorem matM_apply (hn : 1 ≤ n) (g : spinGroup (quadMinus n K b c))
    (x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    matM hn g (epsM n hn x) (epsM n hn y) = mat n g x y := by
  simp [matM, Matrix.reindexAlgEquiv_apply, matHom]

theorem matM_injective [Finite K] [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hn : 1 ≤ n) : Function.Injective (matM (b := b) (c := c) hn) := by
  intro g h hgh
  apply mat_injective hirr
  ext x y
  have := congrFun (congrFun hgh (epsM n hn x)) (epsM n hn y)
  rwa [matM_apply, matM_apply] at this

theorem matM_longRoot (hn : 1 ≤ n) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K) :
    matM hn ((minusFrame n b c).longRoot hij s t (.ofAdd a)) =
      rootMatrix (RingEquiv.refl K) (epsM n hn (minusPos n i s)) (epsM n hn (minusPos n j (!t))) a := by
  ext x y
  obtain ⟨x, rfl⟩ := (epsM n hn).surjective x
  obtain ⟨y, rfl⟩ := (epsM n hn).surjective y
  rw [matM_apply, mat_longRoot_eq hij s t a]
  have h1 : Fin.rev (epsM n hn (minusPos n j (!t))) = epsM n hn (minusPos n j t) := by
    rw [epsM_not n hn j t, Fin.rev_rev]
  have h2 : Fin.rev (epsM n hn (minusPos n i s)) = epsM n hn (minusPos n i (!s)) := by
    rw [epsM_not n hn i s]
  simp only [rootMatrix, longMat, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.single_apply, h1, h2, (epsM n hn).injective.eq_iff,
    RingEquiv.refl_apply, smul_eq_mul, mul_sub, mul_one, mul_ite, mul_zero]
  split_ifs <;> simp <;> ring

end MatM

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
