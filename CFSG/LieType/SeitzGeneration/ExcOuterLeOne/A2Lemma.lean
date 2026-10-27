module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Twist

open Matrix CFSG.RankThree.PartOne.CTP
open scoped commutatorElement MatrixGroups

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

section A2Basic

variable {K : Type} [Field K]

@[expose] def t12 (c : K) : SL(3, K) := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c

@[expose] def t13 (c : K) : SL(3, K) := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c

@[expose] def t23 (c : K) : SL(3, K) := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c

@[expose] def t31 (c : K) : SL(3, K) := SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c

@[expose] def t21 (c : K) : SL(3, K) := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c

@[expose] def t32 (c : K) : SL(3, K) := SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c

theorem t12_add (a b : K) : t12 (a + b) = t12 a * t12 b := SpecialLinearGroup.transvection_add _ a b
theorem t13_add (a b : K) : t13 (a + b) = t13 a * t13 b := SpecialLinearGroup.transvection_add _ a b
theorem t12_zero : t12 (0 : K) = 1 := SpecialLinearGroup.transvection_coeff_zero _
theorem t13_zero : t13 (0 : K) = 1 := SpecialLinearGroup.transvection_coeff_zero _
theorem t32_zero : t32 (0 : K) = 1 := SpecialLinearGroup.transvection_coeff_zero _

theorem t12_coe (a : K) : (t12 a : Matrix (Fin 3) (Fin 3) K) = !![1, a, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t12, SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem t13_coe (a : K) : (t13 a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, a; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t13, SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem t23_coe (a : K) : (t23 a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, a; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t23, SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem t31_coe (a : K) : (t31 a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; a, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t31, SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem t21_coe (a : K) : (t21 a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; a, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t21, SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem t32_coe (a : K) : (t32 a : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; 0, a, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t32, SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem t12_inv (a : K) : (t12 a)⁻¹ = t12 (-a) := SpecialLinearGroup.transvection_inv _ a
theorem t13_inv (a : K) : (t13 a)⁻¹ = t13 (-a) := SpecialLinearGroup.transvection_inv _ a
theorem t23_inv (a : K) : (t23 a)⁻¹ = t23 (-a) := SpecialLinearGroup.transvection_inv _ a
theorem t31_inv (a : K) : (t31 a)⁻¹ = t31 (-a) := SpecialLinearGroup.transvection_inv _ a
theorem t21_inv (a : K) : (t21 a)⁻¹ = t21 (-a) := SpecialLinearGroup.transvection_inv _ a
theorem t32_inv (a : K) : (t32 a)⁻¹ = t32 (-a) := SpecialLinearGroup.transvection_inv _ a

theorem comm_t12_t23 (a b : K) : ⁅t12 a, t23 b⁆ = t13 (a * b) := by
  rw [commutatorElement_def, t12_inv, t23_inv]
  apply Subtype.ext
  show (t12 a : Matrix (Fin 3) (Fin 3) K) * t23 b * t12 (-a) * t23 (-b) = t13 (a * b)
  rw [t12_coe, t23_coe, t12_coe, t23_coe, t13_coe]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem comm_t23_t31 (a b : K) : ⁅t23 a, t31 b⁆ = t21 (a * b) := by
  rw [commutatorElement_def, t23_inv, t31_inv]
  apply Subtype.ext
  show (t23 a : Matrix (Fin 3) (Fin 3) K) * t31 b * t23 (-a) * t31 (-b) = t21 (a * b)
  rw [t23_coe, t31_coe, t23_coe, t31_coe, t21_coe]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem comm_t31_t12 (a b : K) : ⁅t31 a, t12 b⁆ = t32 (a * b) := by
  rw [commutatorElement_def, t31_inv, t12_inv]
  apply Subtype.ext
  show (t31 a : Matrix (Fin 3) (Fin 3) K) * t12 b * t31 (-a) * t12 (-b) = t32 (a * b)
  rw [t31_coe, t12_coe, t31_coe, t12_coe, t32_coe]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem comm_t32_t21 (a b : K) : ⁅t32 a, t21 b⁆ = t31 (a * b) := by
  rw [commutatorElement_def, t32_inv, t21_inv]
  apply Subtype.ext
  show (t32 a : Matrix (Fin 3) (Fin 3) K) * t21 b * t32 (-a) * t21 (-b) = t31 (a * b)
  rw [t32_coe, t21_coe, t32_coe, t21_coe, t31_coe]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end A2Basic

section A2Gen

variable {K : Type} [Field K]

@[expose] def A2Gen (lam c₁ c₂ : K) : Subgroup SL(3, K) :=
  Subgroup.closure {t13 1, t31 lam, t12 1 * t13 c₁, t23 1 * t13 c₂}

theorem t13_one_mem_A2Gen (lam c₁ c₂ : K) : t13 1 ∈ A2Gen lam c₁ c₂ :=
  Subgroup.subset_closure (by simp)

theorem t31_mem_A2Gen (lam c₁ c₂ : K) : t31 lam ∈ A2Gen lam c₁ c₂ :=
  Subgroup.subset_closure (by simp)

theorem z1_mem_A2Gen (lam c₁ c₂ : K) : t12 1 * t13 c₁ ∈ A2Gen lam c₁ c₂ :=
  Subgroup.subset_closure (by simp)

theorem z2_mem_A2Gen (lam c₁ c₂ : K) : t23 1 * t13 c₂ ∈ A2Gen lam c₁ c₂ :=
  Subgroup.subset_closure (by simp)

@[expose] def u3 (x y z : K) : SL(3, K) :=
  ⟨!![1, x, z; 0, 1, y; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem u3_coe (x y z : K) :
    (u3 x y z : Matrix (Fin 3) (Fin 3) K) = !![1, x, z; 0, 1, y; 0, 0, 1] := rfl

theorem u3_mul (a b c a' b' c' : K) :
    u3 a b c * u3 a' b' c' = u3 (a + a') (b + b') (c + c' + a * b') := by
  apply Subtype.ext
  show (u3 a b c : Matrix (Fin 3) (Fin 3) K) * (u3 a' b' c' : Matrix (Fin 3) (Fin 3) K) =
    (u3 (a + a') (b + b') (c + c' + a * b') : Matrix (Fin 3) (Fin 3) K)
  rw [u3_coe, u3_coe, u3_coe]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem u3_zero : u3 (0 : K) 0 0 = 1 := by
  apply Subtype.ext
  show (u3 (0 : K) 0 0 : Matrix (Fin 3) (Fin 3) K) = 1
  rw [u3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem u3_inv (a b c : K) : (u3 a b c)⁻¹ = u3 (-a) (-b) (a * b - c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [u3_mul, ← u3_zero]
  congr 1 <;> ring

theorem comm_u3 (a b c a' b' c' : K) :
    ⁅u3 a b c, u3 a' b' c'⁆ = u3 0 0 (a * b' - a' * b) := by
  rw [commutatorElement_def, u3_inv, u3_inv, u3_mul, u3_mul, u3_mul]
  congr 1 <;> ring

theorem t12_eq_u3 (a : K) : t12 a = u3 a 0 0 := by
  apply Subtype.ext
  show (t12 a : Matrix (Fin 3) (Fin 3) K) = (u3 a 0 0 : Matrix (Fin 3) (Fin 3) K)
  rw [t12_coe, u3_coe]

theorem t13_eq_u3 (a : K) : t13 a = u3 0 0 a := by
  apply Subtype.ext
  show (t13 a : Matrix (Fin 3) (Fin 3) K) = (u3 0 0 a : Matrix (Fin 3) (Fin 3) K)
  rw [t13_coe, u3_coe]

theorem t23_eq_u3 (a : K) : t23 a = u3 0 a 0 := by
  apply Subtype.ext
  show (t23 a : Matrix (Fin 3) (Fin 3) K) = (u3 0 a 0 : Matrix (Fin 3) (Fin 3) K)
  rw [t23_coe, u3_coe]

theorem comm_z_aux (f s c : K) : ⁅t12 f * t13 s, t23 1 * t13 c⁆ = t13 f := by
  rw [t12_eq_u3, t13_eq_u3, t23_eq_u3, t13_eq_u3, t13_eq_u3, u3_mul, u3_mul, comm_u3]
  congr 1 <;> ring

theorem zero_or_one_of_mem_card_two {k : Subfield K} (hk : Nat.card k = 2) {c : K} (hc : c ∈ k) :
    c = 0 ∨ c = 1 := by
  by_contra h
  push Not at h
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
  have h1 : (⟨1, k.one_mem⟩ : k) = y := huniq _ (fun h' => one_ne_zero (congrArg Subtype.val h'))
  have h2 : (⟨c, hc⟩ : k) = y := huniq _ (fun h' => h.1 (congrArg Subtype.val h'))
  exact h.2 (congrArg Subtype.val (h2.trans h1.symm))

end A2Gen

section CaseIII

variable {K : Type} [Field K]

@[expose] def emb31 : SpecialLinearGroup (Fin 2) K →* SL(3, K) where
  toFun A := ⟨!![(A : Matrix (Fin 2) (Fin 2) K) 1 1, 0, (A : Matrix (Fin 2) (Fin 2) K) 1 0; 0, 1, 0;
      (A : Matrix (Fin 2) (Fin 2) K) 0 1, 0, (A : Matrix (Fin 2) (Fin 2) K) 0 0], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_three]
    simp
    linear_combination h⟩
  map_one' := by
    apply Subtype.ext
    show (!![_, 0, _; 0, 1, 0; _, 0, _] : Matrix (Fin 3) (Fin 3) K) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    apply Subtype.ext
    show (!![((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1, 0,
        ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0; 0, 1, 0;
        ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1, 0,
        ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0] :
          Matrix (Fin 3) (Fin 3) K) =
      !![(A : Matrix (Fin 2) (Fin 2) K) 1 1, 0, (A : Matrix (Fin 2) (Fin 2) K) 1 0; 0, 1, 0;
        (A : Matrix (Fin 2) (Fin 2) K) 0 1, 0, (A : Matrix (Fin 2) (Fin 2) K) 0 0] *
      !![(B : Matrix (Fin 2) (Fin 2) K) 1 1, 0, (B : Matrix (Fin 2) (Fin 2) K) 1 0; 0, 1, 0;
        (B : Matrix (Fin 2) (Fin 2) K) 0 1, 0, (B : Matrix (Fin 2) (Fin 2) K) 0 0]
    rw [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem emb31_coe (A : SpecialLinearGroup (Fin 2) K) :
    (emb31 A : Matrix (Fin 3) (Fin 3) K) =
      !![(A : Matrix (Fin 2) (Fin 2) K) 1 1, 0, (A : Matrix (Fin 2) (Fin 2) K) 1 0; 0, 1, 0;
        (A : Matrix (Fin 2) (Fin 2) K) 0 1, 0, (A : Matrix (Fin 2) (Fin 2) K) 0 0] := rfl

theorem emb31_u2 (c : K) : emb31 (u2 c) = t31 c := by
  apply Subtype.ext
  rw [emb31_coe, t31_coe, u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem emb31_l2 (c : K) : emb31 (l2 c) = t13 c := by
  apply Subtype.ext
  rw [emb31_coe, t13_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem a2_caseIII [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    {lam : K} (hlam : lam ∉ k) {c₁ c₂ : K} (hc₁ : c₁ ∈ k) (hc₂ : c₂ ∈ k) (s : K) :
    t13 s ∈ A2Gen lam c₁ c₂ := by
  have hlam0 : lam ≠ 0 := fun h => hlam (by rw [h]; exact k.zero_mem)
  have hT13 : ∀ c : K, c ∈ k → t13 c ∈ A2Gen lam c₁ c₂ := by
    intro c hc
    rcases zero_or_one_of_mem_card_two hk hc with h | h
    · rw [h, t13_zero]; exact (A2Gen lam c₁ c₂).one_mem
    · rw [h]; exact t13_one_mem_A2Gen lam c₁ c₂
  have hT12 : t12 1 ∈ A2Gen lam c₁ c₂ := by
    have h := (A2Gen lam c₁ c₂).mul_mem (z1_mem_A2Gen lam c₁ c₂)
      ((A2Gen lam c₁ c₂).inv_mem (hT13 c₁ hc₁))
    rwa [mul_inv_cancel_right] at h
  have hT23 : t23 1 ∈ A2Gen lam c₁ c₂ := by
    have h := (A2Gen lam c₁ c₂).mul_mem (z2_mem_A2Gen lam c₁ c₂)
      ((A2Gen lam c₁ c₂).inv_mem (hT13 c₂ hc₂))
    rwa [mul_inv_cancel_right] at h
  have hcomm : ∀ {g h : SL(3, K)}, g ∈ A2Gen lam c₁ c₂ → h ∈ A2Gen lam c₁ c₂ →
      ⁅g, h⁆ ∈ A2Gen lam c₁ c₂ := fun {g h} hg hh => by
    rw [commutatorElement_def]
    exact (A2Gen lam c₁ c₂).mul_mem ((A2Gen lam c₁ c₂).mul_mem ((A2Gen lam c₁ c₂).mul_mem hg hh)
      ((A2Gen lam c₁ c₂).inv_mem hg)) ((A2Gen lam c₁ c₂).inv_mem hh)
  have h21 : t21 lam ∈ A2Gen lam c₁ c₂ := by
    have h := hcomm hT23 (t31_mem_A2Gen lam c₁ c₂)
    rwa [comm_t23_t31, one_mul] at h
  have h32 : t32 lam ∈ A2Gen lam c₁ c₂ := by
    have h := hcomm (t31_mem_A2Gen lam c₁ c₂) hT12
    rwa [comm_t31_t12, mul_one] at h
  have h31 : t31 (lam * lam) ∈ A2Gen lam c₁ c₂ := by
    have h := hcomm h32 h21
    rwa [comm_t32_t21] at h
  have hu : ∀ x : K, t31 x ∈ A2Gen lam c₁ c₂ → u2 x ∈ (A2Gen lam c₁ c₂).comap emb31 := by
    intro x hx
    rw [Subgroup.mem_comap, emb31_u2]
    exact hx
  have hM : (A2Gen lam c₁ c₂).comap emb31 = ⊤ := by
    refine sl2_eq_top_of_root_groups hd hd2 hK (a₁ := lam) (a₂ := lam * lam) (b₀ := 1) hlam0 ?_
      one_ne_zero ?_ ?_
    · rw [mul_div_assoc, div_self hlam0, mul_one]
      exact hlam
    · intro c₁' hc₁' c₂' hc₂'
      rcases zero_or_one_of_mem_card_two hk hc₁' with h1 | h1 <;>
        rcases zero_or_one_of_mem_card_two hk hc₂' with h2 | h2 <;> rw [h1, h2]
      · simp only [zero_mul, add_zero, u2_zero]
        exact ((A2Gen lam c₁ c₂).comap emb31).one_mem
      · simp only [zero_mul, zero_add, one_mul]
        exact hu _ h31
      · simp only [one_mul, zero_mul, add_zero]
        exact hu _ (t31_mem_A2Gen lam c₁ c₂)
      · simp only [one_mul]
        rw [u2_add]
        exact ((A2Gen lam c₁ c₂).comap emb31).mul_mem (hu _ (t31_mem_A2Gen lam c₁ c₂)) (hu _ h31)
    · rw [Subgroup.mem_comap, emb31_l2]
      exact t13_one_mem_A2Gen lam c₁ c₂
  have hsl : l2 s ∈ (A2Gen lam c₁ c₂).comap emb31 := by
    rw [hM]
    exact Subgroup.mem_top _
  rwa [Subgroup.mem_comap, emb31_l2] at hsl

end CaseIII

section CaseI

variable {K : Type} [Field K]

@[expose] def RowTwoSet (K : Type) [Field K] : Set SL(3, K) :=
  {g | (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
    (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0}

theorem rowTwoSet_mul {g h : SL(3, K)} (hg : g ∈ RowTwoSet K) (hh : h ∈ RowTwoSet K) :
    g * h ∈ RowTwoSet K := by
  obtain ⟨hg0, hg1, hg2⟩ := hg
  obtain ⟨hh0, hh1, hh2⟩ := hh
  refine ⟨?_, ?_, ?_⟩ <;>
  · show ((g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K)) _ _ = _
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1, hg2, hh0, hh1, hh2]

theorem rowTwoSet_one : (1 : SL(3, K)) ∈ RowTwoSet K := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem rowTwoSet_inv {g : SL(3, K)} (hg : g ∈ RowTwoSet K) : g⁻¹ ∈ RowTwoSet K := by
  obtain ⟨hg0, hg1, hg2⟩ := hg
  have key : ∀ j, ((g : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) 1 j =
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 j := fun j => by
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1, hg2]
  have e : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [← key 0, e]; simp
  · rw [← key 1, e]; simp
  · rw [← key 2, e]; simp

@[expose] def rowTwo (K : Type) [Field K] : Subgroup SL(3, K) where
  carrier := RowTwoSet K
  mul_mem' := rowTwoSet_mul
  one_mem' := rowTwoSet_one
  inv_mem' := rowTwoSet_inv

theorem mem_rowTwo {g : SL(3, K)} :
    g ∈ rowTwo K ↔ (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := Iff.rfl

@[expose] def blockHom (K : Type) [Field K] : rowTwo K →* SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨!![((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2;
      ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2], by
    obtain ⟨h0, h1, h2⟩ := g.2
    have hd := (g : SL(3, K)).2
    rw [Matrix.det_fin_three] at hd
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    simp only [h0, h1, h2] at hd
    linear_combination hd⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    apply Subtype.ext
    obtain ⟨h0, h1, h2⟩ := h.2
    show (!![((g * h : rowTwo K) : SL(3, K)).1 0 0, ((g * h : rowTwo K) : SL(3, K)).1 0 2;
        ((g * h : rowTwo K) : SL(3, K)).1 2 0, ((g * h : rowTwo K) : SL(3, K)).1 2 2] :
          Matrix (Fin 2) (Fin 2) K) =
      !![((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2;
        ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2] *
      !![((h : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0, ((h : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2;
        ((h : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0, ((h : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2]

theorem blockHom_coe (g : rowTwo K) :
    (blockHom K g : Matrix (Fin 2) (Fin 2) K) =
      !![((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2;
        ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0, ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2] :=
  rfl

theorem t13_mem_rowTwo (c : K) : t13 c ∈ rowTwo K := by
  rw [mem_rowTwo, t13_coe]; simp

theorem t31_mem_rowTwo (c : K) : t31 c ∈ rowTwo K := by
  rw [mem_rowTwo, t31_coe]; simp

theorem z_mem_rowTwo (a c : K) : t12 a * t13 c ∈ rowTwo K :=
  (rowTwo K).mul_mem (by rw [mem_rowTwo, t12_coe]; simp) (t13_mem_rowTwo c)

theorem n2_coe (α β : K) :
    ((t12 α * t32 β : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = !![1, α, 0; 0, 1, 0; 0, β, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, t12_coe, t32_coe, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockHom_t13 (c : K) : blockHom K ⟨t13 c, t13_mem_rowTwo c⟩ = u2 c := by
  apply Subtype.ext
  rw [blockHom_coe, u2_coe]
  show (!![((t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0, ((t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2;
        ((t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0, ((t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2] :
          Matrix (Fin 2) (Fin 2) K) = _
  rw [t13_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockHom_t31 (c : K) : blockHom K ⟨t31 c, t31_mem_rowTwo c⟩ = l2 c := by
  apply Subtype.ext
  rw [blockHom_coe, l2_coe]
  show (!![((t31 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0, ((t31 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2;
        ((t31 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0, ((t31 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2] :
          Matrix (Fin 2) (Fin 2) K) = _
  rw [t31_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockHom_z (a c : K) : blockHom K ⟨t12 a * t13 c, z_mem_rowTwo a c⟩ = u2 c := by
  apply Subtype.ext
  rw [blockHom_coe, u2_coe]
  show (!![((t12 a * t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0,
        ((t12 a * t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2;
        ((t12 a * t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0,
        ((t12 a * t13 c : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2] : Matrix (Fin 2) (Fin 2) K) = _
  rw [t12_eq_u3, t13_eq_u3, u3_mul, u3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rowTwo_conj_n2 (g : rowTwo K) (α β : K) :
    (g : SL(3, K)) * (t12 α * t32 β) * (g : SL(3, K))⁻¹ =
      t12 ((blockHom K g : Matrix (Fin 2) (Fin 2) K) 0 0 * α +
          (blockHom K g : Matrix (Fin 2) (Fin 2) K) 0 1 * β) *
        t32 ((blockHom K g : Matrix (Fin 2) (Fin 2) K) 1 0 * α +
          (blockHom K g : Matrix (Fin 2) (Fin 2) K) 1 1 * β) := by
  obtain ⟨h0, h1, h2⟩ := g.2
  have key : (g : SL(3, K)) * (t12 α * t32 β) =
      (t12 ((blockHom K g : Matrix (Fin 2) (Fin 2) K) 0 0 * α +
          (blockHom K g : Matrix (Fin 2) (Fin 2) K) 0 1 * β) *
        t32 ((blockHom K g : Matrix (Fin 2) (Fin 2) K) 1 0 * α +
          (blockHom K g : Matrix (Fin 2) (Fin 2) K) 1 1 * β)) * (g : SL(3, K)) := by
    apply Subtype.ext
    rw [blockHom_coe]
    simp only [Matrix.SpecialLinearGroup.coe_mul, t12_coe, t32_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2] <;> ring
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

theorem eq_n2_of_blockHom_eq_one {g : rowTwo K} (hg : blockHom K g = 1) :
    ∃ α β : K, (g : SL(3, K)) = t12 α * t32 β := by
  obtain ⟨h0, h1, h2⟩ := g.2
  have hb : ((blockHom K g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hg, Matrix.SpecialLinearGroup.coe_one]
  rw [blockHom_coe] at hb
  have e00 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    simpa using congrFun (congrFun hb 0) 0
  have e02 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    simpa using congrFun (congrFun hb 0) 1
  have e20 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    simpa using congrFun (congrFun hb 1) 0
  have e22 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    simpa using congrFun (congrFun hb 1) 1
  refine ⟨((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1,
    ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 1, ?_⟩
  apply Subtype.ext
  rw [n2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, e00, e02, e20, e22]

@[expose] def Yc1 (lam c₁ : K) : Subgroup SL(3, K) :=
  Subgroup.closure {t13 1, t31 lam, t12 1 * t13 c₁}

theorem t13_mem_Yc1 (lam c₁ : K) : t13 1 ∈ Yc1 lam c₁ := Subgroup.subset_closure (by simp)

theorem t31_mem_Yc1 (lam c₁ : K) : t31 lam ∈ Yc1 lam c₁ := Subgroup.subset_closure (by simp)

theorem z1_mem_Yc1 (lam c₁ : K) : t12 1 * t13 c₁ ∈ Yc1 lam c₁ := Subgroup.subset_closure (by simp)

theorem Yc1_le_A2Gen (lam c₁ c₂ : K) : Yc1 lam c₁ ≤ A2Gen lam c₁ c₂ := by
  rw [Yc1, Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact t13_one_mem_A2Gen lam c₁ c₂
  · exact t31_mem_A2Gen lam c₁ c₂
  · exact z1_mem_A2Gen lam c₁ c₂

theorem a2_Y_lift [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    {lam c₁ : K} (hlam : lam ∉ k) (hc₁ : c₁ ∉ k) (A : SpecialLinearGroup (Fin 2) K) :
    ∃ y : rowTwo K, (y : SL(3, K)) ∈ Yc1 lam c₁ ∧ blockHom K y = A := by
  let M : Subgroup (SpecialLinearGroup (Fin 2) K) :=
    ((Yc1 lam c₁).subgroupOf (rowTwo K)).map (blockHom K)
  have hM : ∀ g : rowTwo K, (g : SL(3, K)) ∈ Yc1 lam c₁ → blockHom K g ∈ M := fun g hg =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg)
  have hu1 : u2 1 ∈ M := by
    rw [← blockHom_t13 1]
    exact hM _ (t13_mem_Yc1 lam c₁)
  have huc : u2 c₁ ∈ M := by
    rw [← blockHom_z 1 c₁]
    exact hM _ (z1_mem_Yc1 lam c₁)
  have hl : l2 lam ∈ M := by
    rw [← blockHom_t31 lam]
    exact hM _ (t31_mem_Yc1 lam c₁)
  have hMtop : M = ⊤ := by
    refine sl2_eq_top_of_root_groups hd hd2 hK (a₁ := 1) (a₂ := c₁) (b₀ := lam)
      one_ne_zero ?_ ?_ ?_ ?_
    · rw [div_one]
      exact hc₁
    · intro h
      exact hlam (h ▸ k.zero_mem)
    · intro p hp q hq
      rcases zero_or_one_of_mem_card_two hk hp with rfl | rfl <;>
        rcases zero_or_one_of_mem_card_two hk hq with rfl | rfl
      · simp only [zero_mul, add_zero, u2_zero]
        exact M.one_mem
      · simp only [zero_mul, one_mul, zero_add]
        exact huc
      · simp only [one_mul, zero_mul, add_zero]
        exact hu1
      · simp only [one_mul]
        rw [u2_add]
        exact M.mul_mem hu1 huc
    · exact hl
  have hA : A ∈ M := by
    rw [hMtop]
    exact Subgroup.mem_top A
  obtain ⟨y, hy, hyA⟩ := Subgroup.mem_map.mp hA
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hyA⟩

theorem a2_caseI_alpha {lam c₁ c₂ : K}
    (hlift : ∀ A : SpecialLinearGroup (Fin 2) K,
      ∃ y : rowTwo K, (y : SL(3, K)) ∈ Yc1 lam c₁ ∧ blockHom K y = A)
    {α β : K} (hne : α ≠ 0 ∨ β ≠ 0) (hn : t12 α * t32 β ∈ Yc1 lam c₁) (s : K) :
    t13 s ∈ A2Gen lam c₁ c₂ := by
  have hcomm32 : ∀ a b : K, Commute (t12 a) (t32 b) := by
    intro a b
    show t12 a * t32 b = t32 b * t12 a
    apply Subtype.ext
    show (t12 a : Matrix (Fin 3) (Fin 3) K) * t32 b = t32 b * t12 a
    rw [t12_coe, t32_coe]
    simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hadd : ∀ a b σ : K, t12 (a + σ) * t32 b = t12 a * t32 b * t12 σ := by
    intro a b σ
    calc t12 (a + σ) * t32 b = t12 a * (t12 σ * t32 b) := by rw [t12_add, mul_assoc]
      _ = t12 a * (t32 b * t12 σ) := by rw [(hcomm32 σ b).eq]
      _ = t12 a * t32 b * t12 σ := by rw [mul_assoc]
  have hstep : ∀ a b : K, b ≠ 0 → t12 a * t32 b ∈ Yc1 lam c₁ → ∀ σ : K, t12 σ ∈ Yc1 lam c₁ := by
    intro a b hb hab σ
    obtain ⟨y, hy, hB⟩ := hlift (u2 (σ / b))
    have hconj := rowTwo_conj_n2 y a b
    rw [hB, u2_coe] at hconj
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, zero_mul, zero_add] at hconj
    rw [div_mul_cancel₀ σ hb, hadd] at hconj
    have hmem : (y : SL(3, K)) * (t12 a * t32 b) * (y : SL(3, K))⁻¹ ∈ Yc1 lam c₁ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hab) (Subgroup.inv_mem _ hy)
    rw [hconj] at hmem
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hab) hmem
    rwa [inv_mul_cancel_left] at h2
  have hall : ∀ σ : K, t12 σ ∈ Yc1 lam c₁ := by
    by_cases hβ : β = 0
    · subst hβ
      have hα : α ≠ 0 := hne.resolve_right (fun h => h rfl)
      obtain ⟨y, hy, hB⟩ := hlift (l2 1)
      have hconj := rowTwo_conj_n2 y α 0
      rw [hB, l2_coe] at hconj
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, zero_mul, zero_add,
        mul_zero, add_zero] at hconj
      have h1 : t12 α * t32 α ∈ Yc1 lam c₁ := by
        rw [← hconj]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hn) (Subgroup.inv_mem _ hy)
      have h2 : t12 α ∈ Yc1 lam c₁ := by
        have h := hn
        rwa [t32_zero, mul_one] at h
      have h3 := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
      rw [inv_mul_cancel_left] at h3
      have h4 : t12 0 * t32 α ∈ Yc1 lam c₁ := by
        rw [t12_zero, one_mul]
        exact h3
      exact fun σ => hstep 0 α hα h4 σ
    · exact fun σ => hstep α β hβ hn σ
  have h1 : t12 s ∈ A2Gen lam c₁ c₂ := Yc1_le_A2Gen lam c₁ c₂ (hall s)
  have h2 : t23 1 * t13 c₂ ∈ A2Gen lam c₁ c₂ := z2_mem_A2Gen lam c₁ c₂
  have hcomm := comm_z_aux s 0 c₂
  rw [t13_zero, mul_one] at hcomm
  rw [← hcomm, commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1))
    (Subgroup.inv_mem _ h2)

private theorem a2cc_block_entries (g : rowTwo K) (A : SpecialLinearGroup (Fin 2) K)
    (hg : blockHom K g = A) :
    (A : Matrix (Fin 2) (Fin 2) K) 0 0 = ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 ∧
    (A : Matrix (Fin 2) (Fin 2) K) 0 1 = ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 ∧
    (A : Matrix (Fin 2) (Fin 2) K) 1 0 = ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0 ∧
    (A : Matrix (Fin 2) (Fin 2) K) 1 1 = ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  subst hg
  simp [blockHom_coe]

private theorem a2cc_isCocycle (y : SpecialLinearGroup (Fin 2) K →* rowTwo K)
    (hblk : ∀ A, blockHom K (y A) = A) :
    CFSG.LieType.SeitzGeneration.OmegaF2.IsCocycle (fun A : SpecialLinearGroup (Fin 2) K =>
      !![((y A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1, 0;
        ((y A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 1, 0]) := by
  rintro a b
  obtain ⟨a00, a01, a10, a11⟩ := a2cc_block_entries (y a) a (hblk a)
  obtain ⟨g10, g11, g12⟩ := mem_rowTwo.1 (y a).2
  obtain ⟨h10, h11, h12⟩ := mem_rowTwo.1 (y b).2
  dsimp only
  simp only [map_mul, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, a00, a01, a10, a11,
      g10, g11, g12, h10, h11, h12] <;> ring

theorem a2_cocycle_core [Finite K] [CharP K 2] {k : Subfield K} (hk : Nat.card k = 2) {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d) {c₁ : K} (hc₁ : c₁ ∉ k)
    (y : SpecialLinearGroup (Fin 2) K →* rowTwo K) (hblk : ∀ A, blockHom K (y A) = A)
    (h1 : (y (u2 1) : SL(3, K)) = t13 1) (h2 : (y (u2 c₁) : SL(3, K)) = t12 1 * t13 c₁) :
    ∃ s f : K, f ∉ k ∧ (y (u2 s) : SL(3, K)) = t12 f * t13 s := by
  have hκ := a2cc_isCocycle y hblk
  have hk1 : (!![((y (u2 1) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1, 0;
      ((y (u2 1) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 1, 0] : Matrix (Fin 2) (Fin 2) K) = 0 := by
    rw [h1, t13_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hsec : ∀ t : K, ((y (u2 t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    intro t
    have := (hκ.u2_second_row hk1 t).1
    simpa using this
  have hy : ∀ t : K, (y (u2 t) : SL(3, K)) =
      t12 (((y (u2 t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1) * t13 t := by
    intro t
    obtain ⟨b00, b01, b10, b11⟩ := a2cc_block_entries (y (u2 t)) (u2 t) (hblk (u2 t))
    obtain ⟨r10, r11, r12⟩ := mem_rowTwo.1 (y (u2 t)).2
    have r21 := hsec t
    have e00 : ((y (u2 t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
      rw [← b00, u2_coe]; simp
    have e02 : ((y (u2 t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 = t := by
      rw [← b01, u2_coe]; simp
    have e20 : ((y (u2 t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
      rw [← b10, u2_coe]; simp
    have e22 : ((y (u2 t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      rw [← b11, u2_coe]; simp
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, t12_coe, t13_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e02, e20, e22, r10, r11, r12, r21]
  have hF1 : ((y (u2 c₁) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1 = 1 := by
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, t12_coe, t13_coe]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hE : ∀ ν : K, ν ≠ 0 → ∀ t : K,
      ((y (u2 (ν * ν * t)) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1 =
        ν * ((y (u2 t) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1 +
          t * ((y (u2 (ν * ν)) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1 := by
    intro ν hν t
    have E := congrFun (congrFun (hκ.torus_formula hk1 hν t) 0) 0
    simpa using E
  by_contra hcon
  have hall : ∀ s : K, ((y (u2 s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1 ∈ k := by
    intro s
    by_contra hs
    exact hcon ⟨s, _, hs, hy s⟩
  have hsurj : Function.Surjective (fun p : k × k => (p.1 : K) + c₁ * (p.2 : K)) := by
    intro ν
    by_cases hν : ν = 0
    · exact ⟨(0, 0), by simp [hν]⟩
    · refine ⟨(⟨_, hall (ν * ν * c₁)⟩, ⟨-_, k.neg_mem (hall (ν * ν))⟩), ?_⟩
      have E := hE ν hν c₁
      dsimp only
      linear_combination E + ν * hF1
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, hK, hk] at hcard
  have hd3 : 3 ≤ d := by have := hd.two_le; omega
  have h8 : 2 ^ 3 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd3
  exact absurd (le_trans h8 hcard) (by norm_num)

theorem a2_caseI_beta [Finite K] [CharP K 2] {k : Subfield K} (hk : Nat.card k = 2) {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d) {lam c₁ c₂ : K} (hc₁ : c₁ ∉ k)
    (hlift : ∀ A : SpecialLinearGroup (Fin 2) K,
      ∃ y : rowTwo K, (y : SL(3, K)) ∈ Yc1 lam c₁ ∧ blockHom K y = A)
    (hinj : ∀ α β : K, t12 α * t32 β ∈ Yc1 lam c₁ → α = 0 ∧ β = 0) :
    ∃ s : K, s ∉ k ∧ t13 s ∈ A2Gen lam c₁ c₂ := by
  have huniq : ∀ g h : rowTwo K, (g : SL(3, K)) ∈ Yc1 lam c₁ → (h : SL(3, K)) ∈ Yc1 lam c₁ →
      blockHom K g = blockHom K h → g = h := by
    intro g h hg hh hgh
    have hqY : ((g * h⁻¹ : rowTwo K) : SL(3, K)) ∈ Yc1 lam c₁ := by
      show (g : SL(3, K)) * (h : SL(3, K))⁻¹ ∈ Yc1 lam c₁
      exact (Yc1 lam c₁).mul_mem hg ((Yc1 lam c₁).inv_mem hh)
    have hqB : blockHom K (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hgh, mul_inv_cancel]
    obtain ⟨α, β, hab⟩ := eq_n2_of_blockHom_eq_one hqB
    rw [hab] at hqY
    obtain ⟨rfl, rfl⟩ := hinj α β hqY
    rw [t12_zero, t32_zero, mul_one] at hab
    exact mul_inv_eq_one.mp (Subtype.ext hab)
  choose yf hyf_mem hyf_blk using hlift
  have hmul : ∀ A B : SpecialLinearGroup (Fin 2) K, yf (A * B) = yf A * yf B := by
    intro A B
    refine huniq _ _ (hyf_mem _) ?_ ?_
    · show (yf A : SL(3, K)) * (yf B : SL(3, K)) ∈ Yc1 lam c₁
      exact (Yc1 lam c₁).mul_mem (hyf_mem A) (hyf_mem B)
    · simp only [map_mul, hyf_blk]
  have hone : yf 1 = 1 := by
    refine huniq _ _ (hyf_mem _) ?_ ?_
    · exact (Yc1 lam c₁).one_mem
    · simp only [map_one, hyf_blk]
  let yh : SpecialLinearGroup (Fin 2) K →* rowTwo K :=
    { toFun := yf, map_one' := hone, map_mul' := hmul }
  have hblk : ∀ A, blockHom K (yh A) = A := hyf_blk
  have h1 : (yh (u2 1) : SL(3, K)) = t13 1 := by
    have e : yf (u2 1) = ⟨t13 1, t13_mem_rowTwo 1⟩ :=
      huniq _ _ (hyf_mem _) (t13_mem_Yc1 lam c₁) (by rw [hyf_blk, blockHom_t13])
    exact congrArg Subtype.val e
  have h2 : (yh (u2 c₁) : SL(3, K)) = t12 1 * t13 c₁ := by
    have e : yf (u2 c₁) = ⟨t12 1 * t13 c₁, z_mem_rowTwo 1 c₁⟩ :=
      huniq _ _ (hyf_mem _) (z1_mem_Yc1 lam c₁) (by rw [hyf_blk, blockHom_z])
    exact congrArg Subtype.val e
  obtain ⟨s, f, hf, hsf⟩ := a2_cocycle_core hk hd hd2 hK hc₁ yh hblk h1 h2
  refine ⟨f, hf, ?_⟩
  have hX : t12 f * t13 s ∈ A2Gen lam c₁ c₂ := by
    rw [← hsf]
    exact Yc1_le_A2Gen lam c₁ c₂ (hyf_mem (u2 s))
  have hz2 : t23 1 * t13 c₂ ∈ A2Gen lam c₁ c₂ := z2_mem_A2Gen lam c₁ c₂
  rw [← comm_z_aux f s c₂, commutatorElement_def]
  exact (A2Gen lam c₁ c₂).mul_mem
    ((A2Gen lam c₁ c₂).mul_mem ((A2Gen lam c₁ c₂).mul_mem hX hz2) ((A2Gen lam c₁ c₂).inv_mem hX))
    ((A2Gen lam c₁ c₂).inv_mem hz2)

theorem a2_caseI [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    {lam c₁ : K} (hlam : lam ∉ k) (hc₁ : c₁ ∉ k) (c₂ : K) :
    ∃ s : K, s ∉ k ∧ t13 s ∈ A2Gen lam c₁ c₂ := by
  have hlift := a2_Y_lift hk hd hd2 hK hlam hc₁
  by_cases h : ∃ α β : K, (α ≠ 0 ∨ β ≠ 0) ∧ t12 α * t32 β ∈ Yc1 lam c₁
  · obtain ⟨α, β, hne, hn⟩ := h
    exact ⟨c₁, hc₁, a2_caseI_alpha hlift hne hn c₁⟩
  · push Not at h
    refine a2_caseI_beta hk hd hd2 hK hc₁ hlift fun α β hn => ?_
    by_contra hne
    rw [not_and_or] at hne
    exact (h α β (by simpa [not_not] using hne)) hn |>.elim

end CaseI

section CaseII

variable {K : Type} [Field K]

@[expose] def Jm (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem Jm_mul_Jm : Jm K * Jm K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_Jm : (Jm K).det = -1 := by
  simp [Jm, Matrix.det_fin_three]

@[expose] def iota (K : Type) [Field K] : SL(3, K) →* SL(3, K) where
  toFun g := ⟨Jm K * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jm K, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, (g⁻¹).2, det_Jm]
    ring⟩
  map_one' := by
    apply Subtype.ext
    show Jm K * (((1 : SL(3, K))⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jm K = 1
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one, Jm_mul_Jm]
  map_mul' g h := by
    apply Subtype.ext
    show Jm K * (((g * h)⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jm K =
      (Jm K * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jm K) *
        (Jm K * ((h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jm K)
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    have hJ := Jm_mul_Jm (K := K)
    calc Jm K * (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ *
          ((h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ) * Jm K
        = Jm K * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * 1 *
          ((h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jm K := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [← hJ]
          simp only [Matrix.mul_assoc]

theorem iota_coe (g : SL(3, K)) : (iota K g : Matrix (Fin 3) (Fin 3) K) =
    Jm K * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jm K := rfl

theorem iota_t12 [CharP K 2] (a : K) : iota K (t12 a) = t23 a := by
  apply Subtype.ext
  rw [iota_coe, t12_inv, t12_coe, t23_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul, dotProduct,
      CharTwo.neg_eq]

theorem iota_t23 [CharP K 2] (a : K) : iota K (t23 a) = t12 a := by
  apply Subtype.ext
  rw [iota_coe, t23_inv, t23_coe, t12_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul, dotProduct,
      CharTwo.neg_eq]

theorem iota_t13 [CharP K 2] (a : K) : iota K (t13 a) = t13 a := by
  apply Subtype.ext
  rw [iota_coe, t13_inv, t13_coe, t13_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul, dotProduct,
      CharTwo.neg_eq]

theorem iota_t31 [CharP K 2] (a : K) : iota K (t31 a) = t31 a := by
  apply Subtype.ext
  rw [iota_coe, t31_inv, t31_coe, t31_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul, dotProduct,
      CharTwo.neg_eq]

theorem iota_mem_A2Gen [CharP K 2] {lam c₁ c₂ : K} {g : SL(3, K)} (hg : g ∈ A2Gen lam c₁ c₂) :
    iota K g ∈ A2Gen lam c₂ c₁ := by
  have hle : A2Gen lam c₁ c₂ ≤ (A2Gen lam c₂ c₁).comap (iota K) := by
    rw [A2Gen, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · show iota K (t13 1) ∈ A2Gen lam c₂ c₁
      rw [iota_t13]
      exact t13_one_mem_A2Gen _ _ _
    · show iota K (t31 lam) ∈ A2Gen lam c₂ c₁
      rw [iota_t31]
      exact t31_mem_A2Gen _ _ _
    · show iota K (t12 1 * t13 c₁) ∈ A2Gen lam c₂ c₁
      rw [map_mul, iota_t12, iota_t13]
      exact z2_mem_A2Gen _ _ _
    · show iota K (t23 1 * t13 c₂) ∈ A2Gen lam c₂ c₁
      rw [map_mul, iota_t23, iota_t13]
      exact z1_mem_A2Gen _ _ _
  exact hle hg

theorem a2_caseII [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    {lam : K} (hlam : lam ∉ k) {c₁ c₂ : K} (_hc₁ : c₁ ∈ k) (hc₂ : c₂ ∉ k) :
    ∃ s : K, s ∉ k ∧ t13 s ∈ A2Gen lam c₁ c₂ := by
  obtain ⟨s, hs, h⟩ := a2_caseI hk hd hd2 hK hlam hc₂ c₁
  refine ⟨s, hs, ?_⟩
  have := iota_mem_A2Gen h
  rwa [iota_t13] at this

end CaseII

theorem a2_lemma {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : Subfield K} (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hK : Nat.card K = Nat.card k ^ d) {lam : K} (hlam : lam ∉ k) (c₁ c₂ : K) :
    ∃ s : K, s ∉ k ∧ t13 s ∈ A2Gen lam c₁ c₂ := by
  by_cases h1 : c₁ ∈ k
  · by_cases h2 : c₂ ∈ k
    · exact ⟨lam, hlam, a2_caseIII hk hd hd2 hK hlam h1 h2 lam⟩
    · exact a2_caseII hk hd hd2 hK hlam h1 h2
  · exact a2_caseI hk hd hd2 hK hlam h1 c₂

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
