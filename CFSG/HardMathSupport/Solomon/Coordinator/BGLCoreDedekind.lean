module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreBasic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def trace3 (σ : F ≃+* F) (z : F) : F := z + σ z + σ (σ z)

theorem trace3_fixed (h3 : orderOf σ = 3) (z : F) : σ (trace3 σ z) = trace3 σ z := by
  simp only [trace3, map_add, sigma_cube h3]
  ring

theorem sigma_ne_one (h3 : orderOf σ = 3) : σ ≠ 1 := by
  intro h
  rw [h, orderOf_one] at h3
  exact absurd h3 (by norm_num)

theorem sigma_sq_ne_one (h3 : orderOf σ = 3) : σ * σ ≠ 1 := by
  intro h
  have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rw [h3] at h2
  exact absurd h2 (by norm_num)

theorem exists_trace_ne_zero (h3 : orderOf σ = 3) : ∃ z : F, trace3 σ z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let f : Fin 3 → (F →* F) := ![MonoidHom.id F, σ.toMonoidHom, (σ * σ).toMonoidHom]
  have hinj : Function.Injective f := by
    have e1 : (MonoidHom.id F) ≠ σ.toMonoidHom := fun h => sigma_ne_one h3
      (RingEquiv.ext fun x => (congrArg (fun g : F →* F => g x) h).symm)
    have e2 : (MonoidHom.id F) ≠ (σ * σ).toMonoidHom := fun h => sigma_sq_ne_one h3
      (RingEquiv.ext fun x => (congrArg (fun g : F →* F => g x) h).symm)
    have e3 : σ.toMonoidHom ≠ (σ * σ).toMonoidHom := by
      intro h
      apply sigma_ne_one h3
      refine RingEquiv.ext fun x => ?_
      have hx := congrArg (fun g : F →* F => g x) h
      change σ x = σ (σ x) at hx
      rw [RingAut.one_apply]
      exact (σ.injective hx).symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hli := (linearIndependent_monoidHom F F).comp f hinj
  have h0 := (Fintype.linearIndependent_iff.mp hli) (fun _ => 1) (by
    funext z
    simp only [Fin.sum_univ_three, one_smul, Function.comp_apply, f, Finset.sum_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply]
    have := hcon z
    simpa [trace3, RingAut.mul_apply] using this) 0
  exact one_ne_zero h0

@[expose] def frobMat (σ : F ≃+* F) (u : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i k => ![u i, σ (u i), σ (σ (u i))] k

theorem det_frobMat_ne_zero (h3 : orderOf σ = 3) {u : Fin 3 → F}
    (hu : ∀ b : Fin 3 → F, IsRat σ b → b ⬝ᵥ u = 0 → b = 0) : (frobMat σ u).det ≠ 0 := by
  intro hdet
  obtain ⟨y, hy0, hy⟩ := (Matrix.exists_vecMul_eq_zero_iff).mpr hdet
  have hcol : ∀ k : Fin 3, ∑ i, y i * frobMat σ u i k = 0 := fun k => by
    have := congrFun hy k
    simpa [Matrix.vecMul, dotProduct] using this
  have r0 : ∑ i, y i * u i = 0 := by simpa [frobMat] using hcol 0
  have r1 : ∑ i, y i * σ (u i) = 0 := by simpa [frobMat] using hcol 1
  have r2 : ∑ i, y i * σ (σ (u i)) = 0 := by simpa [frobMat] using hcol 2
  have s1 : ∑ i, σ (y i) * u i = 0 := by
    have := congrArg σ r2
    simpa [map_sum, map_mul, sigma_cube h3] using this
  have s2 : ∑ i, σ (σ (y i)) * u i = 0 := by
    have := congrArg (fun z => σ (σ z)) r1
    simpa [map_sum, map_mul, sigma_cube h3] using this
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (funext hcon)
  obtain ⟨z, hz⟩ := exists_trace_ne_zero h3
  set l := z / y j
  let b : Fin 3 → F := fun i => trace3 σ (l * y i)
  have hbr : IsRat σ b := fun i => trace3_fixed h3 _
  have hbu : b ⬝ᵥ u = 0 := by
    have e : b ⬝ᵥ u = l * ∑ i, y i * u i + σ l * ∑ i, σ (y i) * u i +
        σ (σ l) * ∑ i, σ (σ (y i)) * u i := by
      simp only [b, trace3, dotProduct, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, r0, s1, s2]
    ring
  have hb0 := hu b hbr hbu
  have := congrFun hb0 j
  apply hz
  simpa [b, l, div_mul_cancel₀ z hj] using this

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
