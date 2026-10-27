module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LWit

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

@[expose] def slPerm (h2 : (2 : K) = 0) : Equiv.Perm (Fin n) →* SpecialLinearGroup (Fin n) K where
  toFun π := ⟨permMatrixHom (n := Fin n) (R := K) π, by
    rw [permMatrixHom_apply, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π⁻¹) with h | h
    · rw [h]; simp
    · rw [h]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]⟩
  map_one' := Subtype.ext (map_one (permMatrixHom (n := Fin n) (R := K)))
  map_mul' π τ := Subtype.ext (map_mul (permMatrixHom (n := Fin n) (R := K)) π τ)

theorem coe_slPerm (h2 : (2 : K) = 0) (π : Equiv.Perm (Fin n)) :
    (slPerm h2 π : Matrix (Fin n) (Fin n) K) = (π⁻¹).permMatrix K := rfl

theorem hasWit_fieldAut_mul_dualAut (h2 : (2 : K) = 0) (hn : 4 ≤ n) (σ : K ≃+* K) :
    HasWit (fieldAut n K σ * dualAut n K) := by
  classical
  let f : Fin 4 ≃ {x : Fin n // x ∈ Set.range (Fin.castLE hn)} :=
    Equiv.ofInjective _ (Fin.castLE_injective hn)
  let ι := Equiv.Perm.extendDomainHom f
  have hι : Function.Injective ι := Equiv.Perm.extendDomainHom_injective f
  set x₀ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 with hx₀
  set y₀ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3 with hy₀
  have hx3 : x₀ ^ 3 = 1 := by decide
  have hc2 : (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) * (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) = 1 := by decide
  have hc1 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ≠ 1 := by decide
  have hT : ∀ π : Equiv.Perm (Fin n), (slPerm h2 π)⁻¹.transpose = slPerm h2 π := by
    intro π
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_transpose, ← map_inv, coe_slPerm, coe_slPerm, inv_inv,
      transpose_permMatrix]
  have hM : ∀ π : Equiv.Perm (Fin n),
      SpecialLinearGroup.map σ.toRingHom (slPerm h2 π) = slPerm h2 π := by
    intro π
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_slPerm]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  have hfix : ∀ π : Equiv.Perm (Fin n), (fieldAut n K σ * dualAut n K) (proj n K (slPerm h2 π)) =
      proj n K (slPerm h2 π) := by
    intro π
    rw [MulAut.mul_apply, dualAut_proj, hT, fieldAut_proj, hM]
  have hinj : ∀ π : Equiv.Perm (Fin n), slPerm h2 π = 1 → π = 1 := by
    intro π hπ
    rw [← inv_eq_one]
    ext i
    have hM' := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K)
      i (π⁻¹ i)) hπ
    simp only [coe_slPerm, Matrix.SpecialLinearGroup.coe_one, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, ite_true] at hM'
    by_contra hne
    rw [Matrix.one_apply_ne (fun h => hne (by rw [← h]; rfl))] at hM'
    exact one_ne_zero hM'
  set c := x₀ * y₀ * x₀⁻¹ * y₀⁻¹ with hc
  set g := slPerm h2 (ι c) with hg
  have hgg : g * g = 1 := by rw [hg, ← map_mul, ← map_mul, hc2, map_one, map_one]
  have hg1 : g ≠ 1 := fun h1 => hc1 (hι (by rw [hinj _ h1, map_one]))
  refine ⟨proj n K (slPerm h2 (ι x₀)), proj n K (slPerm h2 (ι y₀)), hfix _, hfix _, ?_, ?_⟩
  · refine Odd.of_dvd_nat (n := 3) ⟨1, rfl⟩ (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow, ← map_pow, ← map_pow, hx3, map_one, map_one, map_one]
  · have e : proj n K (slPerm h2 (ι x₀)) * proj n K (slPerm h2 (ι y₀)) *
        (proj n K (slPerm h2 (ι x₀)))⁻¹ * (proj n K (slPerm h2 (ι y₀)))⁻¹ = proj n K g := by
      rw [hg, hc]
      simp only [map_mul, map_inv]
    rw [e, orderOf_proj_eq_two h2 hgg hg1]

theorem hasWit_graphField [Finite K] (h2 : (2 : K) = 0) (hn : 4 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {A : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    HasWit (conjAut n K A * fieldAut n K σ * dualAut n K) := by
  obtain ⟨-, -, H, hH⟩ := odd_linear_graph_field_involution_conjugacy Nat.prime_two hf hK
    (by omega) A σ hσ hα
  rw [hH]
  exact (hasWit_fieldAut_mul_dualAut h2 hn σ).conj (conjAut n K H)

end CFSG.ComponentClassification.HarrisLit.L33.C2
