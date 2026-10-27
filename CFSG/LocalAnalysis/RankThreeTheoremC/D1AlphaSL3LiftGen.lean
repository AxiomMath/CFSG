module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix

private theorem cube_dichotomy {k : Type*} [Field k] {x y z w : k} (hy : y ≠ 0) (hw : w ≠ 0)
    (hx : x ^ 3 = y ^ 3) (hz : z ^ 3 = w ^ 3) :
    x = y ∨ z = w ∨ x * z = y * w ∨ x * z ^ 2 = y * w ^ 2 := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, x = ρ * y := ⟨x / y, by field_simp⟩
  obtain ⟨τ, rfl⟩ : ∃ τ, z = τ * w := ⟨z / w, by field_simp⟩
  have hρ : ρ ^ 3 = 1 := by
    have h : (ρ ^ 3 - 1) * y ^ 3 = 0 := by linear_combination hx
    rcases mul_eq_zero.mp h with h | h
    · linear_combination h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hy
  have hτ : τ ^ 3 = 1 := by
    have h : (τ ^ 3 - 1) * w ^ 3 = 0 := by linear_combination hz
    rcases mul_eq_zero.mp h with h | h
    · linear_combination h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hw
  have h1 : (ρ - 1) * (ρ ^ 2 + ρ + 1) = 0 := by linear_combination hρ
  have h2 : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
  rcases mul_eq_zero.mp h1 with h | h
  · left
    rw [sub_eq_zero.mp h, one_mul]
  rcases mul_eq_zero.mp h2 with h' | h'
  · right; left
    rw [sub_eq_zero.mp h', one_mul]
  have h3 : (ρ - τ) * (ρ + τ + 1) = 0 := by linear_combination h - h'
  rcases mul_eq_zero.mp h3 with h4 | h4
  · right; right; right
    obtain rfl : ρ = τ := sub_eq_zero.mp h4
    linear_combination (y * w ^ 2) * hρ
  · right; right; left
    have hρτ : ρ * τ = 1 := by linear_combination ρ * h4 - h
    linear_combination (y * w) * hρτ

private theorem diagonal_commute_single {n : Type*} [Fintype n] [DecidableEq n] {k : Type*}
    [CommRing k] {a b : n} (d : n → k) (hab : d a = d b) (t : k) :
    Matrix.diagonal d * Matrix.single a b t = Matrix.single a b t * Matrix.diagonal d := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same, hab, mul_comm]
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h, mul_zero, zero_mul]

private theorem diagonal_commute_transvection {n : Type*} [Fintype n] [DecidableEq n] {k : Type*}
    [CommRing k] {a b : n} (d : n → k) (hab : d a = d b) (t : k) :
    Matrix.diagonal d * (1 + Matrix.single a b t) =
      (1 + Matrix.single a b t) * Matrix.diagonal d := by
  rw [mul_add, add_mul, mul_one, one_mul, diagonal_commute_single d hab t]

private theorem commute_conj_of_commute {R : Type*} [Ring R] {P Q M D T : R} (h1 : P * Q = 1)
    (h2 : Q * P = 1) (hD : Q * M * P = D) (hDT : D * T = T * D) :
    M * (P * T * Q) = (P * T * Q) * M := by
  have hM : M = P * D * Q := by
    rw [← hD]
    calc M = (P * Q) * M * (P * Q) := by rw [h1]; simp
      _ = P * (Q * M * P) * Q := by simp only [mul_assoc]
  have e1 : P * D * Q * (P * T * Q) = P * (D * T) * Q := by
    calc _ = P * D * (Q * P) * T * Q := by simp only [mul_assoc]
      _ = _ := by rw [h2, mul_one]; simp only [mul_assoc]
  have e2 : P * T * Q * (P * D * Q) = P * (T * D) * Q := by
    calc _ = P * T * (Q * P) * D * Q := by simp only [mul_assoc]
      _ = _ := by rw [h2, mul_one]; simp only [mul_assoc]
  rw [hM, e1, e2, hDT]

private theorem conj_mul_aux {R : Type*} [Ring R] {P Q : R} (h1 : P * Q = 1) (X Y : R) :
    Q * (X * Y) * P = (Q * X * P) * (Q * Y * P) := by
  calc Q * (X * Y) * P = Q * X * (P * Q) * Y * P := by rw [h1, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

private theorem diag_entry_ne_zero {k : Type*} [Field k] (P M : GL (Fin 3) k) (u : Fin 3 → k)
    (h : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k) *
      (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal u) (i : Fin 3) : u i ≠ 0 := by
  have hu : IsUnit (Matrix.diagonal u) := h ▸ (((P⁻¹).isUnit.mul M.isUnit).mul P.isUnit)
  exact (Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hu) i).ne_zero

theorem closure_fixed_eq_top {k : Type*} [Field k] (P s g : GL (Fin 3) k) (u v : Fin 3 → k)
    (hs : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
      (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal u)
    (hg : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) *
      (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal v)
    (hu : ∀ a b, u a ^ 3 = u b ^ 3) (hv : ∀ a b, v a ^ 3 = v b ^ 3) :
    Subgroup.closure {x : SpecialLinearGroup (Fin 3) k |
      (∃ M ∈ ({s, g, s * g, s * g ^ 2} : Set (GL (Fin 3) k)),
        (M : Matrix (Fin 3) (Fin 3) k) * (x : Matrix (Fin 3) (Fin 3) k) =
          (x : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k))} = ⊤ := by
  have hPQ : (P : Matrix (Fin 3) (Fin 3) k) *
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := Units.mul_inv P
  have hQP : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      (P : Matrix (Fin 3) (Fin 3) k) = 1 := Units.inv_mul P
  have hsg : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      ((s * g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal (u * v) := by
    rw [Units.val_mul, conj_mul_aux hPQ, hs, hg, Matrix.diagonal_mul_diagonal]
    rfl
  have hsg2 : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      ((s * g ^ 2 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal (u * (v * v)) := by
    rw [pow_two, Units.val_mul, conj_mul_aux hPQ, Units.val_mul, conj_mul_aux hPQ, hs, hg,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rfl
  have hne : ∀ i, u i ≠ 0 := diag_entry_ne_zero P s u hs
  have hne' : ∀ i, v i ≠ 0 := diag_entry_ne_zero P g v hg
  have hmem : ∀ x ∈ CFSG.LinearGroups.elementarySet 3 k,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k P x ∈
        {x : SpecialLinearGroup (Fin 3) k |
          (∃ M ∈ ({s, g, s * g, s * g ^ 2} : Set (GL (Fin 3) k)),
            (M : Matrix (Fin 3) (Fin 3) k) * (x : Matrix (Fin 3) (Fin 3) k) =
              (x : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k))} := by
    rintro x ⟨a, b, hab, t, rfl⟩
    have hmat : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k P
        (SpecialLinearGroup.transvection hab t) : SpecialLinearGroup (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) = (P : Matrix (Fin 3) (Fin 3) k) * (1 + Matrix.single a b t) *
            ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix 3 k P _
    show ∃ M ∈ ({s, g, s * g, s * g ^ 2} : Set (GL (Fin 3) k)), _
    rw [hmat]
    rcases cube_dichotomy (hne b) (hne' b) (hu a b) (hv a b) with h | h | h | h
    · exact ⟨s, by simp, commute_conj_of_commute hPQ hQP hs (diagonal_commute_transvection u h t)⟩
    · exact ⟨g, by simp, commute_conj_of_commute hPQ hQP hg (diagonal_commute_transvection v h t)⟩
    · exact ⟨s * g, by simp, commute_conj_of_commute hPQ hQP hsg
        (diagonal_commute_transvection (u * v) h t)⟩
    · exact ⟨s * g ^ 2, by simp, commute_conj_of_commute hPQ hQP hsg2
        (diagonal_commute_transvection (u * (v * v)) (by simpa [sq, mul_assoc] using h) t)⟩
  have hgen : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 k) = ⊤ :=
    CFSG.LinearGroups.special_linear_elementary_generation
  set φ := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k P
  rw [eq_top_iff]
  calc (⊤ : Subgroup (SpecialLinearGroup (Fin 3) k))
      = (Subgroup.closure (CFSG.LinearGroups.elementarySet 3 k)).map φ.toMonoidHom := by
        rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective]
    _ = Subgroup.closure (φ.toMonoidHom '' CFSG.LinearGroups.elementarySet 3 k) :=
        MonoidHom.map_closure _ _
    _ ≤ _ := Subgroup.closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hmem x hx)

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
