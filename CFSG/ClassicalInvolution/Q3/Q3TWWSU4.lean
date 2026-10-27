module

public import CFSG.ClassicalInvolution.Q3.Q3TWWF9
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusSU

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.WeakCT.SU4
open scoped Matrix

section Transport

variable {K : Type} [Field K] [CharP K 3]

@[expose] noncomputable def phi9 (ι : K) (hι : ι ^ 2 = -1) : F9 →+* K where
  toFun x := (ZMod.castHom (dvd_refl 3) K x.re) + (ZMod.castHom (dvd_refl 3) K x.im) * ι
  map_one' := by
    show (ZMod.castHom (dvd_refl 3) K 1) + (ZMod.castHom (dvd_refl 3) K 0) * ι = 1
    simp
  map_zero' := by
    show (ZMod.castHom (dvd_refl 3) K 0) + (ZMod.castHom (dvd_refl 3) K 0) * ι = 0
    simp
  map_add' x y := by
    show (ZMod.castHom (dvd_refl 3) K (x.re + y.re)) +
      (ZMod.castHom (dvd_refl 3) K (x.im + y.im)) * ι = _
    simp only [map_add]
    ring
  map_mul' x y := by
    show (ZMod.castHom (dvd_refl 3) K (x.re * y.re - x.im * y.im)) +
      (ZMod.castHom (dvd_refl 3) K (x.re * y.im + x.im * y.re)) * ι = _
    simp only [map_add, map_sub, map_mul]
    linear_combination (-(ZMod.castHom (dvd_refl 3) K x.im) *
      (ZMod.castHom (dvd_refl 3) K y.im)) * hι

variable (ι : K) (hι : ι ^ 2 = -1)

theorem phi9_iota9 : phi9 ι hι iota9 = ι := by
  show (ZMod.castHom (dvd_refl 3) K 0) + (ZMod.castHom (dvd_refl 3) K 1) * ι = ι
  simp

theorem phi9_frob9 (x : F9) : phi9 ι hι (frob9 x) = (phi9 ι hι x) ^ 3 := by
  rw [frob9, map_pow]

theorem mapMatrix_longMatF9 (i : Fin 4) (c : F9) :
    (phi9 ι hι).mapMatrix (longMatF9 i c) = longRootMatrix i (phi9 ι hι c) := by
  ext a b
  simp [longMatF9, longRootMatrix, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem mapMatrix_rootMatF9 (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 3) (i j : Fin 4) (c : F9) :
    (phi9 ι hι).mapMatrix (rootMatF9 i j c) = rootMatrix σ i j (phi9 ι hι c) := by
  ext a b
  simp [rootMatF9, rootMatrix, Matrix.single_apply, Matrix.one_apply, hσ]
  split_ifs <;> simp_all [phi9_frob9 ι hι]

end Transport

section Mat

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def suMat : SU σ 4 →* Matrix (Fin 4) (Fin 4) K :=
  (Units.coeHom (Matrix (Fin 4) (Fin 4) K)).comp (SU σ 4).subtype

theorem suMat_injective : Function.Injective (suMat σ) := fun _ _ h => Subtype.ext (Units.ext h)

end Mat

section Letters

variable {K : Type} [Field K] [CharP K 3]

omit [CharP K 3] in
theorem sigma_iota (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 3) (ι : K) (hι : ι ^ 2 = -1) :
    σ ι = -ι := by
  rw [hσ]
  linear_combination ι * hι

@[expose] noncomputable def suLetter (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 3)
    (hσσ : ∀ c, σ (σ c) = c) (ι : K) (hι : ι ^ 2 = -1) : Fin 12 → SU σ 4 :=
  ![sulong σ 0 (by decide) ι (sigma_iota σ hσ ι hι),
    sulong σ 3 (by decide) (-ι) (by rw [map_neg, sigma_iota σ hσ ι hι]),
    sulong σ 1 (by decide) ι (sigma_iota σ hσ ι hι),
    sulong σ 2 (by decide) (-ι) (by rw [map_neg, sigma_iota σ hσ ι hι]),
    suroot σ hσσ 0 2 (by decide) (by decide) (by decide) 1,
    suroot σ hσσ 0 2 (by decide) (by decide) (by decide) ι,
    suroot σ hσσ 0 1 (by decide) (by decide) (by decide) 1,
    suroot σ hσσ 0 1 (by decide) (by decide) (by decide) ι,
    suroot σ hσσ 1 0 (by decide) (by decide) (by decide) 1,
    suroot σ hσσ 1 0 (by decide) (by decide) (by decide) ι,
    suroot σ hσσ 2 0 (by decide) (by decide) (by decide) 1,
    suroot σ hσσ 2 0 (by decide) (by decide) (by decide) ι]

theorem evalCube_map {m : ℕ} {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (n : Fin m → M)
    (w : List (Fin m × Bool)) : evalCube (fun i => f (n i)) w = f (evalCube n w) := by
  induction w with
  | nil => simp [evalCube]
  | cons p w ih =>
    simp only [evalCube, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    cases p.2 <;> simp

variable (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 3) (hσσ : ∀ c, σ (σ c) = c) (ι : K)
  (hι : ι ^ 2 = -1)

theorem suMat_suLetter (j : Fin 12) :
    suMat σ (suLetter σ hσ hσσ ι hι j) = (phi9 ι hι).mapMatrix (nF9 j) := by
  have e2 := phi9_iota9 ι hι
  have e3 : (phi9 ι hι) (-iota9) = -ι := by rw [map_neg, e2]
  have e1 : (phi9 ι hι) 1 = 1 := map_one _
  fin_cases j
  · show longRootMatrix 0 ι = (phi9 ι hι).mapMatrix (longMatF9 0 iota9)
    rw [mapMatrix_longMatF9, e2]
  · show longRootMatrix 3 (-ι) = (phi9 ι hι).mapMatrix (longMatF9 3 (-iota9))
    rw [mapMatrix_longMatF9, e3]
  · show longRootMatrix 1 ι = (phi9 ι hι).mapMatrix (longMatF9 1 iota9)
    rw [mapMatrix_longMatF9, e2]
  · show longRootMatrix 2 (-ι) = (phi9 ι hι).mapMatrix (longMatF9 2 (-iota9))
    rw [mapMatrix_longMatF9, e3]
  · show rootMatrix σ 0 2 1 = (phi9 ι hι).mapMatrix (rootMatF9 0 2 1)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e1]
  · show rootMatrix σ 0 2 ι = (phi9 ι hι).mapMatrix (rootMatF9 0 2 iota9)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e2]
  · show rootMatrix σ 0 1 1 = (phi9 ι hι).mapMatrix (rootMatF9 0 1 1)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e1]
  · show rootMatrix σ 0 1 ι = (phi9 ι hι).mapMatrix (rootMatF9 0 1 iota9)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e2]
  · show rootMatrix σ 1 0 1 = (phi9 ι hι).mapMatrix (rootMatF9 1 0 1)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e1]
  · show rootMatrix σ 1 0 ι = (phi9 ι hι).mapMatrix (rootMatF9 1 0 iota9)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e2]
  · show rootMatrix σ 2 0 1 = (phi9 ι hι).mapMatrix (rootMatF9 2 0 1)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e1]
  · show rootMatrix σ 2 0 ι = (phi9 ι hι).mapMatrix (rootMatF9 2 0 iota9)
    rw [mapMatrix_rootMatF9 ι hι σ hσ, e2]

theorem relsHold_suLetter : RelsHold (suLetter σ hσ hσσ ι hι) su4Words := by
  refine relsHold_of_evalCube (suMat σ) (suMat_injective σ) _
    (fun j => (phi9 ι hι).mapMatrix (nF9 j)) (suMat_suLetter σ hσ hσσ ι hι) ?_ ?_
  · intro i
    rw [← map_mul, ← map_mul, su4_cube_F9 i, map_one]
  · intro w hw
    show evalCube (fun j => ((phi9 ι hι).mapMatrix : Matrix (Fin 4) (Fin 4) F9 →+*
      Matrix (Fin 4) (Fin 4) K).toMonoidHom (nF9 j)) w = 1
    rw [evalCube_map, su4_rels_F9 w hw, map_one]

end Letters

end CFSG.ClassicalInvolution.Q3.Q3TW
