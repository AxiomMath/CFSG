module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesDecomp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sec9u_associated_isOrtho {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0) :
    (QuadraticMap.associated Q).IsOrthoᵢ b := by
  rw [LinearMap.isOrthoᵢ_def]
  intro i j hij
  rw [QuadraticMap.associated_isOrtho, ← QuadraticMap.isOrtho_polarBilin,
    QuadraticMap.polarBilin_apply_apply]
  exact hpol i j hij

private lemma sec9u_quad_sum {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (c : Fin n → ZMod 3) :
    Q (∑ i, c i • b i) = ∑ i, c i ^ 2 * Q (b i) := by
  have horth := sec9u_associated_isOrtho (Q := Q) hpol
  have h := QuadraticMap.basisRepr_eq_of_iIsOrtho (Q := Q) (v := b) horth
  have hc := congrArg
    (fun F : QuadraticMap (ZMod 3) (Fin n → ZMod 3) (ZMod 3) => F c) h
  rw [QuadraticMap.basisRepr_apply, QuadraticMap.weightedSumSquares_apply] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, pow_two]
  ring

theorem sec9u_exists_diag {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0) (T : Finset (Fin n)) :
    ∃ g : OGroup Q, ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) =
      (if i ∈ T then (-1 : ZMod 3) else 1) • b i := by
  classical
  let w : Fin n → (ZMod 3)ˣ := fun i => if i ∈ T then -1 else 1
  let f : V ≃ₗ[ZMod 3] V := b.equiv (b.unitsSMul w) (Equiv.refl _)
  have hf : ∀ i, f (b i) = (w i : ZMod 3) • b i := by
    intro i
    change b.equiv (b.unitsSMul w) (Equiv.refl (Fin n)) (b i) = (w i : ZMod 3) • b i
    rw [Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply]
    rfl
  have hw : ∀ i, (w i : ZMod 3) = if i ∈ T then (-1 : ZMod 3) else 1 := by
    intro i
    by_cases hi : i ∈ T <;> simp [w, hi]
  have hw_sq : ∀ i, (w i : ZMod 3) * (w i : ZMod 3) = 1 := by
    intro i
    rw [hw i]
    by_cases hi : i ∈ T <;> simp [hi]
  have hfv : ∀ v, f v = ∑ i, ((w i : ZMod 3) * b.repr v i) • b i := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hf i, smul_smul]
    congr 1
    ring
  have hisom : f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hfv v, sec9u_quad_sum hpol (fun i => (w i : ZMod 3) * b.repr v i)]
    conv_rhs => rw [← b.sum_repr v]
    rw [sec9u_quad_sum hpol (b.repr v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, pow_two, hw_sq i, one_mul]
  refine ⟨⟨f, hisom⟩, fun i => ?_⟩
  change f (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i
  rw [hf i]
  change (w i : ZMod 3) • b i = (if i ∈ T then (-1 : ZMod 3) else 1) • b i
  rw [hw i]

end CFSG.OddStandard.SmallF3.Omega
