module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeGen

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def FixSL (g : Matrix (Fin n) (Fin n) F) : Set (SpecialLinearGroup (Fin n) F) :=
  {k | ∃ ζ : F, g * (k : Matrix (Fin n) (Fin n) F) = ζ • ((k : Matrix (Fin n) (Fin n) F) * g)}

theorem mem_FixSL_of_mul_comm {g : Matrix (Fin n) (Fin n) F} {k : SpecialLinearGroup (Fin n) F}
    (h : g * (k : Matrix (Fin n) (Fin n) F) = (k : Matrix (Fin n) (Fin n) F) * g) :
    k ∈ FixSL g :=
  ⟨1, by rw [one_smul]; exact h⟩

theorem mem_FixSL_smul {g : Matrix (Fin n) (Fin n) F} {c : F} (hc : c ≠ 0)
    {k : SpecialLinearGroup (Fin n) F} : k ∈ FixSL (c • g) ↔ k ∈ FixSL g := by
  constructor
  · rintro ⟨ζ, h⟩
    refine ⟨ζ, ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_comm ζ c] at h
    exact smul_right_injective _ hc h
  · rintro ⟨ζ, h⟩
    refine ⟨ζ, ?_⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_comm ζ c, h]

theorem eq_top_of_conj_transvections {K : Subgroup (SpecialLinearGroup (Fin n) F)}
    (P : GL (Fin n) F)
    (h : ∀ (i j : Fin n) (hij : i ≠ j) (c : F),
      conjUnit P (SpecialLinearGroup.transvection hij c) ∈ K) : K = ⊤ := by
  have htop : (Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup
      (ι := Fin n) (F := F)))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  have hK' : K.comap (conjUnit P) = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact h t.i t.j t.hij t.c
  rw [eq_top_iff]
  intro g _
  rw [← conjUnit_conjUnit_inv P g]
  exact Subgroup.mem_comap.1 (hK' ▸ Subgroup.mem_top (conjUnit P⁻¹ g))

theorem diagonal_commute_one_add_single {D : Fin n → F} {i j : Fin n} (hD : D i = D j) (c : F) :
    diagonal D * (1 + Matrix.single i j c) = (1 + Matrix.single i j c) * diagonal D := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hab
    simp [hD, mul_comm]
  · have h' : ¬(i = a ∧ j = b) := fun h => hab ⟨h.1.symm, h.2.symm⟩
    simp [h']

theorem mem_FixSL_conj_transvection {P g : GL (Fin n) F} {D : Fin n → F}
    (hPg : (P : Matrix (Fin n) (Fin n) F) * g = diagonal D * P) {i j : Fin n} (hij : i ≠ j)
    (hD : D i = D j) (c : F) :
    conjUnit P⁻¹ (SpecialLinearGroup.transvection hij c) ∈
      FixSL (g : Matrix (Fin n) (Fin n) F) := by
  apply mem_FixSL_of_mul_comm
  have hPi : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * P = 1 := Units.inv_mul P
  have hiP : (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 := Units.mul_inv P
  have hg : (g : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal D := by
    calc (g : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((P : Matrix (Fin n) (Fin n) F) * g) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [← Matrix.mul_assoc, hPi, Matrix.one_mul]
      _ = _ := by rw [hPg, Matrix.mul_assoc, Matrix.mul_assoc, hiP, Matrix.mul_one]
  rw [conjUnit_coe, inv_inv, SpecialLinearGroup.transvection_coe]
  have hT := diagonal_commute_one_add_single hD c
  calc (g : Matrix (Fin n) (Fin n) F) *
        (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 + Matrix.single i j c) * P)
      = (g * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (1 + Matrix.single i j c) *
          P := by
        simp only [Matrix.mul_assoc]
    _ = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (diagonal D * (1 + Matrix.single i j c)) * P := by
        rw [hg]; simp only [Matrix.mul_assoc]
    _ = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((1 + Matrix.single i j c) * diagonal D) * P := by rw [hT]
    _ = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 + Matrix.single i j c) *
          (diagonal D * P) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hPg]; simp only [Matrix.mul_assoc]

theorem cube_roots_cases {r u : F} (hr : r ^ 3 = 1) (hu : u ^ 3 = 1) :
    r = 1 ∨ u = 1 ∨ r * u = 1 ∨ r * u ^ 2 = 1 := by
  by_cases hr1 : r = 1
  · exact Or.inl hr1
  by_cases hu1 : u = 1
  · exact Or.inr (Or.inl hu1)
  by_cases hru : r * u = 1
  · exact Or.inr (Or.inr (Or.inl hru))
  right; right; right
  have hr2 : r ^ 2 + r + 1 = 0 := by
    have h1 : (r - 1) * (r ^ 2 + r + 1) = 0 := by linear_combination hr
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hr1)
  have hu2 : u ^ 2 + u + 1 = 0 := by
    have h1 : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination hu
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hu1)
  have h1 : (r - u) * (r + u + 1) = 0 := by linear_combination hr2 - hu2
  rcases mul_eq_zero.1 h1 with h | h
  · have hru' : r = u := sub_eq_zero.1 h
    subst hru'
    linear_combination hr
  · exfalso
    apply hru
    linear_combination (-1 : F) * hr2 + r * h

end CFSG.LieType.SeitzGeneration
