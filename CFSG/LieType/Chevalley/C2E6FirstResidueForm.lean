module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LieType.Chevalley.C2E6A5CubeTwist

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem unitaryFieldData_K : UnitaryFieldData 2 1 K :=
  ⟨Nat.prime_two, le_rfl, Nat.card_eq_fintype_card.trans card_K⟩

theorem unitaryFieldData_K_bar (c : K) : unitaryFieldData_K.bar c = bar c := by
  rw [UnitaryFieldData.bar_apply]
  rfl

theorem coe_unitaryFieldData_K_bar : ⇑unitaryFieldData_K.bar = bar :=
  funext unitaryFieldData_K_bar

abbrev uVec (i : Fin 6) : Fin 6 → K := Pi.single i 1

@[expose] def herm6 (v w : Fin 6 → K) : K := ∑ i, v i * bar (w (Fin.rev i))

abbrev form6 : (Fin 6 → K) →ₛₗ[unitaryFieldData_K.bar] (Fin 6 → K) →ₗ[K] K :=
  gramForm unitaryFieldData_K J6

theorem J6_apply (i j : Fin 6) : J6 i j = if j = Fin.rev i then 1 else 0 :=
  rfl

theorem J6_mulVec (y : Fin 6 → K) (i : Fin 6) : (J6 *ᵥ y) i = y (Fin.rev i) := by
  simp only [mulVec, dotProduct, J6_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem J6_mul_apply (A : Matrix (Fin 6) (Fin 6) K) (i j : Fin 6) :
    (J6 * A) i j = A (Fin.rev i) j := by
  simp only [mul_apply, J6_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem mul_J6_apply (A : Matrix (Fin 6) (Fin 6) K) (i j : Fin 6) :
    (A * J6) i j = A i (Fin.rev j) := by
  simp only [mul_apply, J6_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · rw [Fin.rev_rev, ite_eq_left rfl]
  · intro k _ hk
    rw [ite_eq_right]
    intro h
    exact hk (by rw [h, Fin.rev_rev])
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem form6_apply (x y : Fin 6 → K) : form6 x y = ∑ i, bar (x i) * y (Fin.rev i) := by
  rw [gramForm_apply, dotProduct]
  simp only [J6_mulVec, unitaryFieldData_K_bar]

theorem herm6_eq_form6 (v w : Fin 6 → K) : herm6 v w = form6 w v := by
  rw [herm6, form6_apply, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.revPerm_apply, Fin.rev_rev, mul_comm]

theorem J6_conjTranspose : (J6.map unitaryFieldData_K.bar)ᵀ = J6 := by
  ext i j
  rw [transpose_apply, map_apply, J6_apply, J6_apply]
  by_cases h : i = Fin.rev j
  · rw [ite_eq_left h, ite_eq_left (by rw [h, Fin.rev_rev]), map_one]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', Fin.rev_rev])), map_zero]

theorem det_J6_ne_zero : J6.det ≠ 0 := by
  intro h
  have := congrArg det J6_mul_J6
  rw [det_mul, h, zero_mul, det_one] at this
  exact zero_ne_one this

theorem form6_isSymm : form6.IsSymm :=
  gramForm_isSymm unitaryFieldData_K J6_conjTranspose

theorem form6_separatingLeft : form6.SeparatingLeft :=
  gramForm_separatingLeft unitaryFieldData_K det_J6_ne_zero

theorem mem_SU6_iff_herm6 (h : SpecialLinearGroup (Fin 6) K) :
    h ∈ SU6 ↔ ∀ v w : Fin 6 → K,
      herm6 ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ v) ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ w) =
        herm6 v w := by
  rw [mem_SU6_iff, ← coe_unitaryFieldData_K_bar, ← gramForm_isometry_iff]
  simp only [herm6_eq_form6]
  exact ⟨fun H v w => H w v, fun H v w => H w v⟩

theorem herm6_mulVec_of_mem_SU6 {h : SpecialLinearGroup (Fin 6) K} (hh : h ∈ SU6)
    (v w : Fin 6 → K) :
    herm6 ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ v) ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ w) =
      herm6 v w :=
  (mem_SU6_iff_herm6 h).mp hh v w

theorem form6_mulVec_of_mem_SU6 {h : SpecialLinearGroup (Fin 6) K} (hh : h ∈ SU6)
    (x y : Fin 6 → K) :
    form6 ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ x) ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ y) =
      form6 x y := by
  rw [← herm6_eq_form6, ← herm6_eq_form6, herm6_mulVec_of_mem_SU6 hh]

theorem inv_apply_of_mem_SU6 {h : SpecialLinearGroup (Fin 6) K} (hh : h ∈ SU6) (i j : Fin 6) :
    ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j =
      bar ((h : Matrix (Fin 6) (Fin 6) K) (Fin.rev j) (Fin.rev i)) := by
  set M : Matrix (Fin 6) (Fin 6) K := (h : Matrix (Fin 6) (Fin 6) K)
  set X : Matrix (Fin 6) (Fin 6) K := J6 * (M.map bar)ᵀ * J6
  have hX : X * M = 1 := by
    have e := (mem_SU6_iff h).mp hh
    calc X * M = J6 * ((M.map bar)ᵀ * J6 * M) := by simp only [X, Matrix.mul_assoc]
      _ = 1 := by rw [e, J6_mul_J6]
  have hinv : ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = X := by
    have h1 : M * ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      change ((h * h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1
      rw [mul_inv_cancel]
      rfl
    calc ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
        = X * M * ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
          rw [hX, Matrix.one_mul]
      _ = X := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [hinv]
  change (J6 * (M.map bar)ᵀ * J6) i j = _
  rw [mul_J6_apply, J6_mul_apply, transpose_apply, map_apply]

@[expose] def nativeHerm (s t : Fin 6 → K) : K :=
  ∑ i : Fin 3, (s ⟨i, by omega⟩ * bar (t ⟨i + 3, by omega⟩) +
    s ⟨i + 3, by omega⟩ * bar (t ⟨i, by omega⟩))

@[expose] def nativeCoord : (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.swap 0 2)

theorem nativeCoord_apply (v : Fin 6 → K) (j : Fin 6) : nativeCoord v j = v (Equiv.swap 0 2 j) :=
  rfl

theorem nativeCoord_uVec (i : Fin 6) : nativeCoord (uVec i) = uVec (Equiv.swap 0 2 i) := by
  funext j
  simp only [nativeCoord_apply, uVec, Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem nativeHerm_eq (s t : Fin 6 → K) :
    nativeHerm s t = s 0 * bar (t 3) + s 3 * bar (t 0) + (s 1 * bar (t 4) + s 4 * bar (t 1)) +
      (s 2 * bar (t 5) + s 5 * bar (t 2)) := by
  rw [nativeHerm, Fin.sum_univ_three]
  rfl

theorem nativeHerm_nativeCoord (v w : Fin 6 → K) :
    nativeHerm (nativeCoord v) (nativeCoord w) = herm6 v w := by
  have e0 : Equiv.swap (0 : Fin 6) 2 0 = 2 := rfl
  have e1 : Equiv.swap (0 : Fin 6) 2 1 = 1 := rfl
  have e2 : Equiv.swap (0 : Fin 6) 2 2 = 0 := rfl
  have e3 : Equiv.swap (0 : Fin 6) 2 3 = 3 := rfl
  have e4 : Equiv.swap (0 : Fin 6) 2 4 = 4 := rfl
  have e5 : Equiv.swap (0 : Fin 6) 2 5 = 5 := rfl
  have r0 : Fin.rev (0 : Fin 6) = 5 := rfl
  have r1 : Fin.rev (1 : Fin 6) = 4 := rfl
  have r2 : Fin.rev (2 : Fin 6) = 3 := rfl
  have r3 : Fin.rev (3 : Fin 6) = 2 := rfl
  have r4 : Fin.rev (4 : Fin 6) = 1 := rfl
  have r5 : Fin.rev (5 : Fin 6) = 0 := rfl
  rw [nativeHerm_eq, herm6, Fin.sum_univ_six]
  simp only [nativeCoord_apply, e0, e1, e2, e3, e4, e5, r0, r1, r2, r3, r4, r5]
  ring

end CFSG.LieType.Chevalley.C2E6Std
