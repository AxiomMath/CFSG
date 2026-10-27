module

public import CFSG.LargeExtraspecial.AS35QThGamU
public import CFSG.LargeExtraspecial.AS35QThModel

public section

namespace CFSG.LargeExtraspecial.AS35QTh

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

theorem pow_three_K {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have h := pow_four_K c
  rw [pow_succ] at h
  exact mul_left_cancel₀ hc (by rw [mul_one, mul_comm]; exact h)

theorem eq_one_of_sq_K {c : K} (hc : c ^ 2 = 1) : c = 1 := by
  rw [← pow_four_K c, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc, one_pow]

@[expose] noncomputable def fLin (A : Matrix (Fin 3) (Fin 3) K) :
    (Fin (3 + 2) → K) →ₗ[K] (Fin (3 + 2) → K) :=
  LinearMap.id + (ι 3).comp ((Matrix.toLin' A - LinearMap.id).comp (π 3))

theorem fLin_apply (A : Matrix (Fin 3) (Fin 3) K) (x : Fin (3 + 2) → K) :
    fLin A x = x + ι 3 (A *ᵥ π 3 x - π 3 x) := by
  simp only [fLin, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, Matrix.toLin'_apply]

theorem π_fLin (A : Matrix (Fin 3) (Fin 3) K) (x : Fin (3 + 2) → K) :
    π 3 (fLin A x) = A *ᵥ π 3 x := by
  rw [fLin_apply, map_add, π_ι, add_sub_cancel]

theorem herm_v₀_fLin (A : Matrix (Fin 3) (Fin 3) K) (x : Fin (3 + 2) → K) :
    herm frob (v₀ 3) (fLin A x) = herm frob (v₀ 3) x := by
  rw [fLin_apply, herm_add_right, herm_v₀_ι, add_zero]

theorem herm_u₀_fLin (A : Matrix (Fin 3) (Fin 3) K) (x : Fin (3 + 2) → K) :
    herm frob (u₀ 3) (fLin A x) = herm frob (u₀ 3) x := by
  rw [fLin_apply, herm_add_right, herm_u₀_ι, add_zero]

theorem fLin_v₀ (A : Matrix (Fin 3) (Fin 3) K) : fLin A (v₀ 3) = v₀ 3 := by
  rw [fLin_apply, π_v₀, Matrix.mulVec_zero, sub_zero, map_zero, add_zero]

theorem fLin_ι (A : Matrix (Fin 3) (Fin 3) K) (z : Fin 3 → K) : fLin A (ι 3 z) = ι 3 (A *ᵥ z) := by
  rw [fLin_apply, π_ι, map_sub, add_sub_cancel]

theorem fLin_comp (A B : Matrix (Fin 3) (Fin 3) K) :
    (fLin A).comp (fLin B) = fLin (A * B) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, fLin_apply A, π_fLin, fLin_apply, fLin_apply, ← Matrix.mulVec_mulVec,
    add_assoc, ← map_add]
  congr 2
  abel

theorem herm_fLin {A : Matrix (Fin 3) (Fin 3) K} (hA : conjTr frob A * A = 1)
    (x y : Fin (3 + 2) → K) : herm frob (fLin A x) (fLin A y) = herm frob x y := by
  rw [herm_eq_coords (fLin A x), herm_eq_coords x y, herm_u₀_fLin, herm_u₀_fLin, herm_v₀_fLin,
    herm_v₀_fLin, π_fLin, π_fLin, herm_mulVec, hA, Matrix.one_mulVec]

theorem det_eq_det_submatrix_succ {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (h : ∀ i, N i 0 = (Pi.single 0 1 : Fin (n + 1) → K) i) :
    N.det = (N.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, h 0, Pi.single_eq_same]
  rw [Finset.sum_eq_zero (fun j _ => by
    rw [h j.succ, Pi.single_eq_of_ne (Fin.succ_ne_zero j), mul_zero, zero_mul]), add_zero]
  simp

theorem toMatrix'_fLin_apply (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin (3 + 2)) :
    LinearMap.toMatrix' (fLin A) i j = fLin A (Pi.single j 1) i := by
  rw [LinearMap.toMatrix'_apply]

theorem det_toMatrix'_fLin (A : Matrix (Fin 3) (Fin 3) K) :
    (LinearMap.toMatrix' (fLin A)).det = A.det := by
  set N := LinearMap.toMatrix' (fLin A) with hN
  have hπ0 : π 3 (Pi.single (0 : Fin (3 + 2)) (1 : K)) = 0 := by
    funext k
    rw [π_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero _)]
    rfl
  have hπ1 : π 3 (Pi.single (Fin.succ (0 : Fin (3 + 1))) (1 : K)) = 0 := by
    funext k
    rw [π_apply, Pi.single_eq_of_ne]
    · rfl
    · exact fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h)
  have h1 : N.det = (N.submatrix Fin.succ Fin.succ).det := by
    refine det_eq_det_submatrix_succ N fun i => ?_
    rw [hN, toMatrix'_fLin_apply, fLin_apply, hπ0, Matrix.mulVec_zero, sub_zero, map_zero,
      add_zero]
  have h2 : (N.submatrix Fin.succ Fin.succ).det =
      ((N.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ).det := by
    refine det_eq_det_submatrix_succ _ fun i => ?_
    rw [Matrix.submatrix_apply, hN, toMatrix'_fLin_apply, fLin_apply, hπ1, Matrix.mulVec_zero,
      sub_zero, map_zero, add_zero]
    cases i using Fin.cases with
    | zero => simp
    | succ k =>
      rw [Pi.single_eq_of_ne, Pi.single_eq_of_ne (Fin.succ_ne_zero k)]
      exact fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h)
  have h3 : (N.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ = A := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hN, toMatrix'_fLin_apply]
    have he : (Pi.single j.succ.succ 1 : Fin (3 + 2) → K) = ι 3 (Pi.single j 1) := by
      funext k
      cases k using Fin.cases with
      | zero => rw [Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm]; rfl
      | succ k =>
        cases k using Fin.cases with
        | zero =>
          rw [Pi.single_eq_of_ne]
          · rfl
          · exact fun h => Fin.succ_ne_zero j (Fin.succ_injective _ h).symm
        | succ k =>
          rw [ι_apply_succ_succ]
          by_cases hk : k = j
          · subst hk; simp
          · rw [Pi.single_eq_of_ne (fun h => hk (Fin.succ_injective _ (Fin.succ_injective _ h))),
              Pi.single_eq_of_ne hk]
    rw [he, fLin_ι, ι_apply_succ_succ, Matrix.mulVec_single_one]
    rfl
  rw [h1, h2, h3]

@[expose] noncomputable def lLin (A : GU3) : (Fin (3 + 2) → K) →ₗ[K] (Fin (3 + 2) → K) :=
  (gm A).det • fLin (gm A)

theorem lLin_apply (A : GU3) (x : Fin (3 + 2) → K) : lLin A x = (gm A).det • fLin (gm A) x := rfl

theorem det_gm_ne_zero (A : GU3) : (gm A).det ≠ 0 := by
  have h := congrArg Matrix.det (mem_GU3.1 A.2)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact right_ne_zero_of_mul_eq_one h

theorem frob_det_mul (A : GU3) : frob (gm A).det * (gm A).det = 1 :=
  frob_mul_self (det_gm_ne_zero A)

@[expose] noncomputable def Lmat (A : GU3) : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K :=
  LinearMap.toMatrix' (lLin A)

theorem Lmat_mulVec (A : GU3) (x : Fin (3 + 2) → K) : Lmat A *ᵥ x = lLin A x :=
  LinearMap.toMatrix'_mulVec _ _

theorem det_Lmat (A : GU3) : (Lmat A).det = 1 := by
  rw [Lmat, lLin, map_smul, Matrix.det_smul, det_toMatrix'_fLin, Fintype.card_fin]
  have h3 := pow_three_K (det_gm_ne_zero A)
  calc (gm A).det ^ (3 + 2) * (gm A).det = ((gm A).det ^ 3) ^ 2 := by ring
    _ = 1 := by rw [h3, one_pow]

theorem herm_lLin (A : GU3) (x y : Fin (3 + 2) → K) :
    herm frob (lLin A x) (lLin A y) = herm frob x y := by
  rw [lLin_apply, lLin_apply, herm_smul_left, herm_smul_right, herm_fLin (mem_GU3.1 A.2),
    ← mul_assoc, frob_det_mul, one_mul]

@[expose] noncomputable def Lsu (A : GU3) : SUid frob (3 + 2) :=
  mkSU frob (Lmat A) (det_Lmat A) (fun x y => by
    rw [Lmat_mulVec, Lmat_mulVec]
    exact herm_lLin A x y)

theorem Lsu_smul (A : GU3) (x : Fin (3 + 2) → K) : Lsu A • x = lLin A x := by
  rw [Lsu, mkSU_smul, Lmat_mulVec]

theorem gm_mul (A B : GU3) : gm (A * B) = gm A * gm B := by
  simp only [gm, Subgroup.coe_mul, Units.val_mul]

theorem Lsu_mul (A B : GU3) : Lsu A * Lsu B = Lsu (A * B) := by
  refine ext_smul _ fun x => ?_
  rw [mul_smul, Lsu_smul, Lsu_smul, Lsu_smul, lLin_apply, lLin_apply, lLin_apply, map_smul,
    ← LinearMap.comp_apply, fLin_comp, smul_smul, gm_mul, Matrix.det_mul]

theorem Lsu_one : Lsu 1 = 1 := by
  refine ext_smul _ fun x => ?_
  rw [Lsu_smul, lLin_apply, one_smul]
  simp only [gm, OneMemClass.coe_one, Units.val_one, Matrix.det_one, one_smul]
  rw [fLin_apply, Matrix.one_mulVec, sub_self, map_zero, add_zero]

theorem Lsu_inv (A : GU3) : (Lsu A)⁻¹ = Lsu A⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, Lsu_mul, mul_inv_cancel, Lsu_one]

theorem Lsu_smul_v₀ (A : GU3) : Lsu A • v₀ 3 = (gm A).det • v₀ 3 := by
  rw [Lsu_smul, lLin_apply, fLin_v₀]

theorem Lsu_smul_ι (A : GU3) (z : Fin 3 → K) :
    Lsu A • ι 3 z = (gm A).det • ι 3 (gv A z) := by
  rw [Lsu_smul, lLin_apply, fLin_ι]

theorem Lsu_mul_Usu (A : GU3) (d : Fin 3 → K) (β : K) (hβ : β + frob β = herm frob d d)
    (hβ' : β + frob β = herm frob (gv A d) (gv A d)) :
    Lsu A * Usu d β hβ = Usu (gv A d) β hβ' * Lsu A := by
  refine ext_smul _ fun x => ?_
  rw [mul_smul, mul_smul, Lsu_smul, Lsu_smul, Usu_smul, Usu_smul, uLin_apply, uLin_apply,
    lLin_apply, lLin_apply, map_add, map_add, map_smul, map_smul, fLin_v₀, fLin_ι,
    herm_smul_right, herm_smul_right, herm_v₀_fLin, herm_ι_left (gv A d), π_fLin, herm_gv,
    ← herm_ι_left]
  module

@[expose] noncomputable def Dmat (c : K) : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K :=
  Matrix.diagonal fun i => if i.val < 2 then c else 1

theorem det_Dmat (c : K) : (Dmat c).det = c ^ 2 := by
  rw [Dmat, Matrix.det_diagonal, Fin.prod_univ_five]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  ring

theorem Dmat_mulVec (c : K) (x : Fin (3 + 2) → K) :
    Dmat c *ᵥ x = c • (x - ι 3 (π 3 x)) + ι 3 (π 3 x) := by
  funext i
  rw [Dmat, Matrix.mulVec_diagonal]
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.succ_zero_eq_one, Fin.val_one, Nat.one_lt_ofNat, ↓reduceIte, Pi.add_apply,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [ι_apply_one, sub_zero, add_zero]
    | succ k =>
      have hk : ¬ (k.succ.succ : Fin (3 + 2)).val < 2 := by simp
      simp only [hk, ↓reduceIte, one_mul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ι_apply_succ_succ, π_apply, sub_self, mul_zero, zero_add]

theorem π_Dmat (c : K) (x : Fin (3 + 2) → K) : π 3 (Dmat c *ᵥ x) = π 3 x := by
  rw [Dmat_mulVec, map_add, map_smul, map_sub, π_ι, sub_self, smul_zero, zero_add]

theorem Dmat_mulVec_v₀ (c : K) : Dmat c *ᵥ v₀ 3 = c • v₀ 3 := by
  rw [Dmat_mulVec, π_v₀, map_zero, sub_zero, add_zero]

theorem herm_Dmat {c : K} (hc : frob c * c = 1) (x y : Fin (3 + 2) → K) :
    herm frob (Dmat c *ᵥ x) (Dmat c *ᵥ y) = herm frob x y := by
  have hdec : ∀ x : Fin (3 + 2) → K, x - ι 3 (π 3 x) =
      herm frob (u₀ 3) x • v₀ 3 + herm frob (v₀ 3) x • u₀ 3 := by
    intro x
    nth_rewrite 1 [decomp x]
    abel
  rw [Dmat_mulVec, Dmat_mulVec, hdec, hdec]
  conv_rhs => rw [decomp x, decomp y]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_v₀_v₀,
    herm_u₀_u₀, herm_v₀_u₀, herm_u₀_v₀, herm_v₀_ι, herm_u₀_ι, herm_ι_v₀, herm_ι_u₀, herm_ι_ι,
    smul_add]
  linear_combination (frob (herm frob (u₀ 3) x) * herm frob (v₀ 3) y +
    frob (herm frob (v₀ 3) x) * herm frob (u₀ 3) y) * hc

end CFSG.LargeExtraspecial.AS35QTh
