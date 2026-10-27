module

public import CFSG.CGT.Stroth77.Section34T201Mats
public import CFSG.CGT.Stroth77.Section34T201Natural
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T201Levels

open Matrix

private def meqB (k : Fin 3 → ℕ) (A B : IntMat) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j => (A i j - B i j) % 2 ^ k i == 0

private theorem meqB_iff {k : Fin 3 → ℕ} {A B : IntMat} : meqB k A B = true ↔ MatEq k A B := by
  simp only [meqB, List.all_eq_true, List.mem_finRange, forall_const, beq_iff_eq]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Int.modEq_iff_dvd, dvd_sub_comm, Int.dvd_iff_emod_eq_zero]

private def natB (k : Fin 3 → ℕ) (M : IntMat) : Bool :=
  meqB k (conjρ (conjρ M) * conjρ M * M) 1 &&
    (meqB k (conjU M) M || meqB k (conjU M) (conjρ M) || meqB k (conjU M) (conjρ M * M))

private theorem natB_iff {k : Fin 3 → ℕ} {M : IntMat} : natB k M = true ↔ NatCond k M := by
  simp only [natB, NatCond, Bool.and_eq_true, Bool.or_eq_true, meqB_iff, or_assoc]

private def nf (x₀ x₁ x₂ y₀ y₁ y₂ : ℤ) : IntMat := ofCols ![1, 0, 0] ![x₀, x₁, x₂] ![y₀, y₁, y₂]

private def bits : List ℤ := [0, 1]
private def odds : List ℤ := [1, 3, 5, 7]
private def evens : List ℤ := [0, 2, 4, 6]

private def checkA (N : IntMat) : Bool :=
  !(meqB (Type200.k 1) (N * Type200.uvM) (Type200.uvM * N) &&
      meqB (Type200.k 1) (N * Type200.tM) (Type200.tM * N) && natB (Type200.k 1) N &&
      !meqB (Type200.k 1) N 1) ||
    (meqB (Type200.k 1) N (wMat 1 0) || meqB (Type200.k 1) N (wMat 1 1) ||
      meqB (Type200.k 1) N (wMat 1 2))

private theorem checkA_nf : ∀ x₀ ∈ bits, ∀ x₁ ∈ odds, ∀ x₂ ∈ evens, ∀ y₀ ∈ bits, ∀ y₁ ∈ evens,
    ∀ y₂ ∈ odds, checkA (nf x₀ x₁ x₂ y₀ y₁ y₂) = true := by
  decide +kernel

private def checkV₁ (N : IntMat) : Bool :=
  !(meqB (Type201.k 1) (N * Type201.uvM 1) (Type201.uvM 1 * N) &&
      meqB (Type201.k 1) (N * Type201.tM 1) (Type201.tM 1 * N * eMat 1) &&
      (meqB (Type201.k 1) (N * N) 1 || meqB (Type201.k 1) (N * N) (eMat 1)) &&
      (meqB (Type201.k 1) (conjρ (conjρ N) * conjρ N * N) 1 ||
        meqB (Type201.k 1) (conjρ (conjρ N) * conjρ N * N) (eMat 1)) &&
      (meqB (Type201.k 1) (conjU N) N || meqB (Type201.k 1) (conjU N) (N * eMat 1)))

private theorem checkV₁_nf : ∀ x₀ ∈ bits, ∀ x₁ ∈ odds, ∀ x₂ ∈ evens, ∀ y₀ ∈ bits, ∀ y₁ ∈ evens,
    ∀ y₂ ∈ odds, checkV₁ (nf x₀ x₁ x₂ y₀ y₁ y₂) = true := by
  decide +kernel

private theorem exists_nf {k : Fin 3 → ℕ} (hk : k = ![1, 3, 3]) {M : IntMat} (h1 : IsAut1 k M) :
    ∃ x₀ ∈ bits, ∃ x₁ ∈ odds, ∃ x₂ ∈ evens, ∃ y₀ ∈ bits, ∃ y₁ ∈ evens, ∃ y₂ ∈ odds,
      MatEq k M (nf x₀ x₁ x₂ y₀ y₁ y₂) := by
  subst hk
  have e : ∀ i j, (M * omegaMat ![1, 3, 3]) i j ≡ omegaMat ![1, 3, 3] i j
      [ZMOD 2 ^ (![1, 3, 3] : Fin 3 → ℕ) i] := h1
  have e00 := e 0 0
  have e10 := e 1 0
  have e20 := e 2 0
  have e11 := e 1 1
  have e21 := e 2 1
  have e12 := e 1 2
  have e22 := e 2 2
  simp [omegaMat, Matrix.mul_diagonal, Int.ModEq] at e00 e10 e20 e11 e21 e12 e22
  refine ⟨M 0 1 % 2, ?_, M 1 1 % 8, ?_, M 2 1 % 8, ?_, M 0 2 % 2, ?_, M 1 2 % 8, ?_, M 2 2 % 8, ?_,
    ?_⟩
  · simp only [bits, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [odds, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [evens, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [bits, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [evens, List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [odds, List.mem_cons, List.not_mem_nil, or_false]; omega
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [nf, ofCols_apply, Int.ModEq] <;> omega

section Congr

variable {k : Fin 3 → ℕ}

private theorem comm_congr {X M N : IntMat} (hX : Compat k X) (hM : Compat k M)
    (hMN : MatEq k M N) (h : MatEq k (M * X) (X * M)) : MatEq k (N * X) (X * N) :=
  ((MatEq.mul hM hMN (MatEq.refl X)).symm.trans h).trans (MatEq.mul hX (MatEq.refl X) hMN)

private theorem twist_congr {X E M N : IntMat} (hX : Compat k X) (hM : Compat k M)
    (hMN : MatEq k M N) (h : MatEq k (M * X) (X * M * E)) : MatEq k (N * X) (X * N * E) :=
  ((MatEq.mul hM hMN (MatEq.refl X)).symm.trans h).trans
    (MatEq.mul (hX.mul hM) (MatEq.mul hX (MatEq.refl X) hMN) (MatEq.refl E))

private theorem compat_conjρ (hρ : Compat k Type200.ρM) {M : IntMat} (hM : Compat k M) :
    Compat k (conjρ M) :=
  (hρ.mul hM).mul (hρ.mul hρ)

private theorem conjρ_congr (hρ : Compat k Type200.ρM) {M N : IntMat} (hM : Compat k M)
    (hMN : MatEq k M N) : MatEq k (conjρ M) (conjρ N) :=
  MatEq.mul (hρ.mul hM) (MatEq.mul hρ (MatEq.refl _) hMN) (MatEq.refl _)

private theorem conjU_congr (hu : Compat k Type200.uM) {M N : IntMat} (hM : Compat k M)
    (hMN : MatEq k M N) : MatEq k (conjU M) (conjU N) :=
  MatEq.mul (hu.mul hM) (MatEq.mul hu (MatEq.refl _) hMN) (MatEq.refl _)

private theorem prod_congr (hρ : Compat k Type200.ρM) {M N : IntMat} (hM : Compat k M)
    (hMN : MatEq k M N) :
    MatEq k (conjρ (conjρ M) * conjρ M * M) (conjρ (conjρ N) * conjρ N * N) :=
  MatEq.mul ((compat_conjρ hρ (compat_conjρ hρ hM)).mul (compat_conjρ hρ hM))
    (MatEq.mul (compat_conjρ hρ (compat_conjρ hρ hM))
      (conjρ_congr hρ (compat_conjρ hρ hM) (conjρ_congr hρ hM hMN)) (conjρ_congr hρ hM hMN)) hMN

private theorem natCond_congr (hρ : Compat k Type200.ρM) (hu : Compat k Type200.uM) {M N : IntMat}
    (hM : Compat k M) (hMN : MatEq k M N) (h : NatCond k M) : NatCond k N := by
  obtain ⟨h1, h2⟩ := h
  have hU := conjU_congr hu hM hMN
  have hR := conjρ_congr hρ hM hMN
  refine ⟨(prod_congr hρ hM hMN).symm.trans h1, ?_⟩
  rcases h2 with h2 | h2 | h2
  · exact Or.inl ((hU.symm.trans h2).trans hMN)
  · exact Or.inr (Or.inl ((hU.symm.trans h2).trans hR))
  · exact Or.inr (Or.inr ((hU.symm.trans h2).trans
      (MatEq.mul (compat_conjρ hρ hM) hR hMN)))

end Congr

private abbrev red : IntMat →+* Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (Int.castRingHom (ZMod 2)).mapMatrix

private theorem red_apply (A : IntMat) (i j : Fin 3) : red A i j = (A i j : ZMod 2) := rfl

private theorem matEq_add_omega_iff {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (Y P Q : IntMat) :
    MatEq k (Y + omegaMat k * P) (Y + omegaMat k * Q) ↔ red P = red Q := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [red_apply, red_apply, ZMod.intCast_eq_intCast_iff]
  simp only [Matrix.add_apply, omegaMat, Matrix.diagonal_mul, Nat.cast_ofNat]
  have h2 : (2 : ℤ) ^ k i = 2 ^ (k i - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (hk i)]
  rw [h2]
  constructor
  · intro h
    exact Int.ModEq.mul_left_cancel' (pow_ne_zero _ two_ne_zero) (Int.ModEq.add_left_cancel' _ h)
  · intro h
    exact (Int.ModEq.mul_left' h).add_left _

private theorem matEq_one_iff {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (P : IntMat) :
    MatEq k (1 + omegaMat k * P) 1 ↔ red P = 0 := by
  have h := matEq_add_omega_iff hk 1 P 0
  rwa [mul_zero, add_zero, map_zero] at h

private theorem exists_eq_one_add {k : Fin 3 → ℕ} {M : IntMat}
    (hN : MatEq (fun i => k i - 1) M 1) : ∃ A, M = 1 + omegaMat k * A := by
  refine ⟨Matrix.of fun i j => (M i j - (1 : IntMat) i j) / 2 ^ (k i - 1), ?_⟩
  ext i j
  have hd : (2 : ℤ) ^ (k i - 1) ∣ M i j - (1 : IntMat) i j := Int.modEq_iff_dvd.1 (hN i j).symm
  simp only [Matrix.add_apply, omegaMat, Matrix.diagonal_mul, Matrix.of_apply]
  rw [Int.mul_ediv_cancel' hd]
  ring

private theorem one_add_mul_one_add (D A B : IntMat) :
    (1 + D * A) * (1 + D * B) = 1 + D * (A + B + A * D * B) := by
  noncomm_ring

private theorem one_add_mul (D A X : IntMat) : (1 + D * A) * X = X + D * (A * X) := by
  noncomm_ring

private theorem mul_one_add {D X Xo : IntMat} (hX : X * D = D * Xo) (A : IntMat) :
    X * (1 + D * A) = X + D * (Xo * A) := by
  calc X * (1 + D * A) = X + X * D * A := by noncomm_ring
    _ = X + D * (Xo * A) := by rw [hX]; noncomm_ring

private theorem conj_one_add {D X Y Xo : IntMat} (hX : X * D = D * Xo) (hXY : X * Y = 1)
    (A : IntMat) : X * (1 + D * A) * Y = 1 + D * (Xo * A * Y) := by
  calc X * (1 + D * A) * Y = X * Y + X * D * A * Y := by noncomm_ring
    _ = 1 + D * (Xo * A * Y) := by rw [hXY, hX]; noncomm_ring

private theorem uvM_eq : Type200.uvM = !![-3, 1, 1; -4, 1, 2; -4, 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, ofCols_apply]

private theorem tM_eq : Type200.tM = !![1, 0, -1; 4, -1, -2; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Type200.uvA, Type200.tM, Type200.ρM, ofCols_apply]

private theorem ρM_eq : Type200.ρM = !![1, 0, -1; 0, 0, -1; 0, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Type200.ρM, ofCols_apply]

private theorem uM_eq : Type200.uM = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Type200.uM, uMat, ofCols_apply]

private theorem uvM201_eq (m : ℕ) :
    Type201.uvM m = !![-3, 1, 1; -4, 1, (1 + 2 ^ (m + 1)) * (2 + 2 ^ (m + 1));
      -4, 2 + 2 ^ (m + 1), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply] <;> ring

private theorem tM201_eq (m : ℕ) :
    Type201.tM m = !![1, 0, -1 - 2 ^ (m + 1); 4, -1 + 2 ^ (m + 1), -2 - 2 ^ (m + 1);
      0, 0, -1 - 2 ^ (m + 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Type201.uvA, Type201.tM, Type201.ρM, ofCols_apply] <;> ring

private theorem ρM_cube : Type200.ρM * (Type200.ρM * Type200.ρM) = 1 := by
  rw [ρM_eq]; decide

private theorem uM_sq : Type200.uM * Type200.uM = 1 := by
  rw [uM_eq]; decide

private theorem k_two_le (q : ℕ) (i : Fin 3) : 2 ≤ Type200.k (q + 2) i := by
  fin_cases i <;> simp [Type200.k]

private theorem k_one_le (q : ℕ) (i : Fin 3) : 1 ≤ Type200.k (q + 2) i :=
  le_trans (by norm_num) (k_two_le q i)

private theorem k_pred (q : ℕ) : Type200.k (q + 2 - 1) = fun i => Type200.k (q + 2) i - 1 := by
  funext i
  fin_cases i <;> simp [Type200.k]

private theorem omega_eq (q : ℕ) :
    omegaMat (Type200.k (q + 2)) = !![2 ^ (q + 1), 0, 0; 0, 2 ^ (q + 3), 0; 0, 0, 2 ^ (q + 3)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omegaMat, Type200.k, Matrix.diagonal]

private theorem two_zmod : (2 : ZMod 2) = 0 := rfl

private theorem red_omega (q : ℕ) : red (omegaMat (Type200.k (q + 2))) = 0 := by
  rw [omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [red_apply, pow_succ, two_zmod]

private theorem uvM_omega (q : ℕ) :
    Type200.uvM * omegaMat (Type200.k (q + 2)) =
      omegaMat (Type200.k (q + 2)) * !![-3, 4, 4; -1, 1, 2; -1, 2, 1] := by
  rw [uvM_eq, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem tM_omega (q : ℕ) :
    Type200.tM * omegaMat (Type200.k (q + 2)) =
      omegaMat (Type200.k (q + 2)) * !![1, 0, -4; 1, -1, -2; 0, 0, -1] := by
  rw [tM_eq, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem ρM_omega (q : ℕ) :
    Type200.ρM * omegaMat (Type200.k (q + 2)) =
      omegaMat (Type200.k (q + 2)) * !![1, 0, -4; 0, 0, -1; 0, 1, -1] := by
  rw [ρM_eq, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem uM_omega (q : ℕ) :
    Type200.uM * omegaMat (Type200.k (q + 2)) = omegaMat (Type200.k (q + 2)) * Type200.uM := by
  rw [uM_eq, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem uvM201_omega (q : ℕ) :
    Type201.uvM (q + 2) * omegaMat (Type200.k (q + 2)) =
      omegaMat (Type200.k (q + 2)) *
        !![-3, 4, 4; -1, 1, 4 * (2 ^ (q + 2)) ^ 2 + 6 * 2 ^ (q + 2) + 2;
          -1, 2 * 2 ^ (q + 2) + 2, 1] := by
  rw [uvM201_eq, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem tM201_omega (q : ℕ) :
    Type201.tM (q + 2) * omegaMat (Type200.k (q + 2)) =
      omegaMat (Type200.k (q + 2)) * !![1, 0, -8 * 2 ^ (q + 2) - 4;
        1, 2 * 2 ^ (q + 2) - 1, -2 * 2 ^ (q + 2) - 2; 0, 0, -2 * 2 ^ (q + 2) - 1] := by
  rw [tM201_eq, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem conjρ_one_add (q : ℕ) (A : IntMat) :
    conjρ (1 + omegaMat (Type200.k (q + 2)) * A) =
      1 + omegaMat (Type200.k (q + 2)) *
        (!![1, 0, -4; 0, 0, -1; 0, 1, -1] * A * (Type200.ρM * Type200.ρM)) :=
  conj_one_add (ρM_omega q) ρM_cube A

private theorem conjU_one_add (q : ℕ) (A : IntMat) :
    conjU (1 + omegaMat (Type200.k (q + 2)) * A) =
      1 + omegaMat (Type200.k (q + 2)) * (Type200.uM * A * Type200.uM) :=
  conj_one_add (uM_omega q) uM_sq A

private def Fuv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 1; 0, 1, 0; 0, 0, 1]
private def Ouv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 1, 0, 1]
private def Ft : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
private def Ot : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 0, 0, 1]
private def Fρ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 0, 1; 0, 1, 1]
private def Oρ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]
private def Fu : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
private def Fe : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 1, 0; 0, 0, 1]

private theorem red_uvM : red Type200.uvM = Fuv := by rw [uvM_eq]; decide
private theorem red_tM : red Type200.tM = Ft := by rw [tM_eq]; decide
private theorem red_ρM : red Type200.ρM = Fρ := by rw [ρM_eq]; decide
private theorem red_uM : red Type200.uM = Fu := by rw [uM_eq]; decide
private theorem red_uvo : red !![-3, 4, 4; -1, 1, 2; -1, 2, 1] = Ouv := by decide
private theorem red_to : red !![1, 0, -4; 1, -1, -2; 0, 0, -1] = Ot := by decide
private theorem red_ρo : red !![1, 0, -4; 0, 0, -1; 0, 1, -1] = Oρ := by decide

private theorem red_uvM201 (q : ℕ) : red (Type201.uvM (q + 2)) = Fuv := by
  rw [uvM201_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [red_apply, Fuv, pow_succ, two_zmod] <;> decide

private theorem red_tM201 (q : ℕ) : red (Type201.tM (q + 2)) = Ft := by
  rw [tM201_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [red_apply, Ft, pow_succ, two_zmod]
  decide

private theorem red_uvo201 (q : ℕ) :
    red !![-3, 4, 4; -1, 1, 4 * (2 ^ (q + 2)) ^ 2 + 6 * 2 ^ (q + 2) + 2;
      -1, 2 * 2 ^ (q + 2) + 2, 1] = Ouv := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [red_apply, Ouv, pow_succ, two_zmod] <;> decide

private theorem red_to201 (q : ℕ) :
    red !![1, 0, -8 * 2 ^ (q + 2) - 4; 1, 2 * 2 ^ (q + 2) - 1, -2 * 2 ^ (q + 2) - 2;
      0, 0, -2 * 2 ^ (q + 2) - 1] = Ot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [red_apply, Ot, pow_succ, two_zmod]
  decide

private abbrev CondB (ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  ε * Fuv = Ouv * ε → ε * Ft = Ot * ε →
    Oρ * (Oρ * ε * (Fρ * Fρ)) * (Fρ * Fρ) + Oρ * ε * (Fρ * Fρ) + ε = 0 →
    (Fu * ε * Fu = ε ∨ Fu * ε * Fu = Oρ * ε * (Fρ * Fρ) ∨
      Fu * ε * Fu = Oρ * ε * (Fρ * Fρ) + ε) → ε ≠ 0 →
    ε = !![0, 0, 0; 0, 0, 1; 0, 1, 0] ∨ ε = !![0, 0, 0; 0, 1, 0; 0, 1, 1] ∨
      ε = !![0, 0, 0; 0, 1, 1; 0, 0, 1]

private def condBB (ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Bool := decide (CondB ε)

private theorem condBB_entries : ∀ a b c d e f g h i : ZMod 2,
    condBB !![a, b, c; d, e, f; g, h, i] = true := by
  decide +kernel

private theorem condB (ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) : CondB ε := by
  rw [Matrix.eta_fin_three ε]
  exact of_decide_eq_true (condBB_entries _ _ _ _ _ _ _ _ _)

private abbrev CondV (ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  ε * Fuv = Ouv * ε → ε * Ft = Ot * (ε + Fe) →
    (Oρ * (Oρ * ε * (Fρ * Fρ)) * (Fρ * Fρ) + Oρ * ε * (Fρ * Fρ) + ε = 0 ∨
      Oρ * (Oρ * ε * (Fρ * Fρ)) * (Fρ * Fρ) + Oρ * ε * (Fρ * Fρ) + ε = Fe) →
    (Fu * ε * Fu = ε ∨ Fu * ε * Fu = ε + Fe) →
    ε = !![0, 1, 1; 1, 1, 1; 1, 1, 1] ∨ ε = !![0, 1, 1; 1, 1, 1; 1, 1, 1] + Fe ∨
      ε = !![0, 1, 1; 1, 0, 0; 1, 0, 0] ∨ ε = !![0, 1, 1; 1, 0, 0; 1, 0, 0] + Fe

private def condVB (ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Bool := decide (CondV ε)

private theorem condVB_entries : ∀ a b c d e f g h i : ZMod 2,
    condVB !![a, b, c; d, e, f; g, h, i] = true := by
  decide +kernel

private theorem condV (ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) : CondV ε := by
  rw [Matrix.eta_fin_three ε]
  exact of_decide_eq_true (condVB_entries _ _ _ _ _ _ _ _ _)

private theorem wMat_zero (q : ℕ) :
    wMat (q + 2) 0 = 1 + omegaMat (Type200.k (q + 2)) * !![0, 0, 0; 0, 0, 1; 0, 1, 0] := by
  rw [omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, ofCols_apply]

private theorem wMat_one (q : ℕ) :
    wMat (q + 2) 1 = 1 + omegaMat (Type200.k (q + 2)) * !![0, 0, 0; 0, 1, 0; 0, 1, 1] := by
  rw [omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, ofCols_apply]

private theorem wMat_two (q : ℕ) :
    wMat (q + 2) 2 = 1 + omegaMat (Type200.k (q + 2)) * !![0, 0, 0; 0, 1, 1; 0, 0, 1] := by
  rw [omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, ofCols_apply]

private theorem eMat_eq (q : ℕ) :
    eMat (q + 2) = 1 + omegaMat (Type200.k (q + 2)) * !![0, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eMat, ofCols_apply]

private theorem theta₁₁_eq (q : ℕ) :
    Stroth34T201Natural.theta₁₁ (q + 2) =
      1 + omegaMat (Type200.k (q + 2)) * !![0, 1, 1; 1, 1, 1; 1, 1, 1] := by
  rw [Stroth34T201Natural.theta₁₁, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofCols_apply]

private theorem theta₂₁_eq (q : ℕ) :
    Stroth34T201Natural.theta₂₁ (q + 2) =
      1 + omegaMat (Type200.k (q + 2)) * !![0, 1, 1; 1, 0, 0; 1, 0, 0] := by
  rw [Stroth34T201Natural.theta₂₁, omega_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofCols_apply]

private theorem red_e : red !![0, 0, 0; 0, 1, 0; 0, 0, 1] = Fe := by decide
private theorem red_θ₁₁ : red !![0, 1, 1; 1, 1, 1; 1, 1, 1] = !![0, 1, 1; 1, 1, 1; 1, 1, 1] := by
  decide
private theorem red_θ₂₁ : red !![0, 1, 1; 1, 0, 0; 1, 0, 0] = !![0, 1, 1; 1, 0, 0; 1, 0, 0] := by
  decide

theorem exists_wMat_one {M : IntMat} (hM : Compat (Type200.k 1) M) (h1 : IsAut1 (Type200.k 1) M)
    (huv : MatEq (Type200.k 1) (M * Type200.uvM) (Type200.uvM * M))
    (ht : MatEq (Type200.k 1) (M * Type200.tM) (Type200.tM * M))
    (hnat : NatCond (Type200.k 1) M) (hne : ¬ MatEq (Type200.k 1) M 1) :
    ∃ i, MatEq (Type200.k 1) M (wMat 1 i) := by
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, y₀, hy₀, y₁, hy₁, y₂, hy₂, hMN⟩ :=
    exists_nf (k := Type200.k 1) rfl h1
  have key := checkA_nf x₀ hx₀ x₁ hx₁ x₂ hx₂ y₀ hy₀ y₁ hy₁ y₂ hy₂
  have huv' := comm_congr (Type200.compat_uv 1) hM hMN huv
  have ht' := comm_congr (Type200.compat_t 1) hM hMN ht
  have hnat' := natCond_congr (Type200.compat_rho 1) (Type200.compat_u 1) hM hMN hnat
  have hne' : meqB (Type200.k 1) (nf x₀ x₁ x₂ y₀ y₁ y₂) 1 = false :=
    Bool.eq_false_iff.2 fun h => hne (hMN.trans (meqB_iff.1 h))
  rw [checkA, meqB_iff.2 huv', meqB_iff.2 ht', natB_iff.2 hnat', hne'] at key
  simp only [Bool.and_self, Bool.not_false, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    meqB_iff] at key
  rcases key with (h | h) | h
  · exact ⟨0, hMN.trans h⟩
  · exact ⟨1, hMN.trans h⟩
  · exact ⟨2, hMN.trans h⟩

theorem exists_wMat_of_two_le {p : ℕ} (hp : 2 ≤ p) {M : IntMat} (hM : Compat (Type200.k p) M)
    (hN : MatEq (Type200.k (p - 1)) M 1)
    (huv : MatEq (Type200.k p) (M * Type200.uvM) (Type200.uvM * M))
    (ht : MatEq (Type200.k p) (M * Type200.tM) (Type200.tM * M))
    (hnat : NatCond (Type200.k p) M) (hne : ¬ MatEq (Type200.k p) M 1) :
    ∃ i, MatEq (Type200.k p) M (wMat p i) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  rw [k_pred] at hN
  obtain ⟨A, rfl⟩ := exists_eq_one_add hN
  have hk := k_one_le q
  rw [one_add_mul, mul_one_add (uvM_omega q), matEq_add_omega_iff hk] at huv
  rw [one_add_mul, mul_one_add (tM_omega q), matEq_add_omega_iff hk] at ht
  obtain ⟨hn1, hn2⟩ := hnat
  rw [conjρ_one_add, conjρ_one_add, one_add_mul_one_add, one_add_mul_one_add,
    matEq_one_iff hk] at hn1
  simp only [conjU_one_add, conjρ_one_add, one_add_mul_one_add, matEq_add_omega_iff hk] at hn2
  rw [matEq_one_iff hk] at hne
  simp only [map_add, map_mul, red_omega, red_uvM, red_tM, red_ρM, red_uM, red_uvo, red_to,
    red_ρo, mul_zero, zero_mul, add_zero] at huv ht hn1 hn2
  rcases condB (red A) huv ht hn1 hn2 hne with h | h | h
  · refine ⟨0, ?_⟩
    rw [wMat_zero, matEq_add_omega_iff hk, h]
    decide
  · refine ⟨1, ?_⟩
    rw [wMat_one, matEq_add_omega_iff hk, h]
    decide
  · refine ⟨2, ?_⟩
    rw [wMat_two, matEq_add_omega_iff hk, h]
    decide

theorem theta_classify {m : ℕ} (hm : 2 ≤ m) {M : IntMat} (hM : Compat (Type201.k m) M)
    (hN : MatEq (Type200.k (m - 1)) M 1)
    (huv : MatEq (Type201.k m) (M * Type201.uvM m) (Type201.uvM m * M))
    (ht : MatEq (Type201.k m) (M * Type201.tM m) (Type201.tM m * M * eMat m))
    (hρ : MatEq (Type201.k m) (conjρ (conjρ M) * conjρ M * M) 1 ∨
      MatEq (Type201.k m) (conjρ (conjρ M) * conjρ M * M) (eMat m))
    (hu : MatEq (Type201.k m) (conjU M) M ∨ MatEq (Type201.k m) (conjU M) (M * eMat m)) :
    MatEq (Type201.k m) M (Stroth34T201Natural.theta₁₁ m) ∨
      MatEq (Type201.k m) M (Stroth34T201Natural.theta₁₁ m * eMat m) ∨
      MatEq (Type201.k m) M (Stroth34T201Natural.theta₂₁ m) ∨
      MatEq (Type201.k m) M (Stroth34T201Natural.theta₂₁ m * eMat m) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 := ⟨m - 2, by omega⟩
  rw [k_pred] at hN
  obtain ⟨A, rfl⟩ := exists_eq_one_add hN
  have hkk : Type201.k (q + 2) = Type200.k (q + 2) := rfl
  rw [hkk] at huv ht hρ hu ⊢
  have hk := k_one_le q
  have et : Type201.tM (q + 2) * (1 + omegaMat (Type200.k (q + 2)) * A) *
      (1 + omegaMat (Type200.k (q + 2)) * !![0, 0, 0; 0, 1, 0; 0, 0, 1]) =
      Type201.tM (q + 2) + omegaMat (Type200.k (q + 2)) *
        (!![1, 0, -8 * 2 ^ (q + 2) - 4; 1, 2 * 2 ^ (q + 2) - 1, -2 * 2 ^ (q + 2) - 2;
          0, 0, -2 * 2 ^ (q + 2) - 1] *
          (A + !![0, 0, 0; 0, 1, 0; 0, 0, 1] +
            A * omegaMat (Type200.k (q + 2)) * !![0, 0, 0; 0, 1, 0; 0, 0, 1])) := by
    rw [mul_assoc, one_add_mul_one_add, mul_one_add (tM201_omega q)]
  rw [one_add_mul, mul_one_add (uvM201_omega q), matEq_add_omega_iff hk] at huv
  rw [eMat_eq, one_add_mul, et, matEq_add_omega_iff hk] at ht
  rw [conjρ_one_add, conjρ_one_add, one_add_mul_one_add, one_add_mul_one_add, eMat_eq,
    matEq_one_iff hk, matEq_add_omega_iff hk] at hρ
  rw [conjU_one_add, eMat_eq, one_add_mul_one_add, matEq_add_omega_iff hk,
    matEq_add_omega_iff hk] at hu
  rw [theta₁₁_eq, theta₂₁_eq, eMat_eq, one_add_mul_one_add, one_add_mul_one_add,
    matEq_add_omega_iff hk, matEq_add_omega_iff hk, matEq_add_omega_iff hk,
    matEq_add_omega_iff hk]
  simp only [map_add, map_mul, red_omega, red_uvM201, red_tM201, red_uvo201, red_to201, red_ρM,
    red_uM, red_ρo, red_e, red_θ₁₁, red_θ₂₁, mul_zero, zero_mul, add_zero] at huv ht hρ hu ⊢
  exact condV (red A) huv ht hρ hu

theorem false_of_theta_one {M : IntMat} (hM : Compat (Type201.k 1) M)
    (h1 : IsAut1 (Type201.k 1) M)
    (huv : MatEq (Type201.k 1) (M * Type201.uvM 1) (Type201.uvM 1 * M))
    (ht : MatEq (Type201.k 1) (M * Type201.tM 1) (Type201.tM 1 * M * eMat 1))
    (hsq : MatEq (Type201.k 1) (M * M) 1 ∨ MatEq (Type201.k 1) (M * M) (eMat 1))
    (hρ : MatEq (Type201.k 1) (conjρ (conjρ M) * conjρ M * M) 1 ∨
      MatEq (Type201.k 1) (conjρ (conjρ M) * conjρ M * M) (eMat 1))
    (hu : MatEq (Type201.k 1) (conjU M) M ∨ MatEq (Type201.k 1) (conjU M) (M * eMat 1)) :
    False := by
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, y₀, hy₀, y₁, hy₁, y₂, hy₂, hMN⟩ :=
    exists_nf (k := Type201.k 1) rfl h1
  set N := nf x₀ x₁ x₂ y₀ y₁ y₂ with hNdef
  have hρc : Compat (Type201.k 1) Type200.ρM := Type200.compat_rho 1
  have huc : Compat (Type201.k 1) Type200.uM := Type200.compat_u 1
  have e1 := meqB_iff.2 (comm_congr (Type201.compat_uv 1) hM hMN huv)
  have e2 := meqB_iff.2 (twist_congr (Type201.compat_t 1) hM hMN ht)
  have hsq' := MatEq.mul hM hMN hMN
  have hP := prod_congr hρc hM hMN
  have hU := conjU_congr huc hM hMN
  have hMe := MatEq.mul hM hMN (MatEq.refl (eMat 1))
  have e3 : (meqB (Type201.k 1) (N * N) 1 || meqB (Type201.k 1) (N * N) (eMat 1)) = true := by
    rcases hsq with h | h <;> simp [meqB_iff.2 (hsq'.symm.trans h)]
  have e4 : (meqB (Type201.k 1) (conjρ (conjρ N) * conjρ N * N) 1 ||
      meqB (Type201.k 1) (conjρ (conjρ N) * conjρ N * N) (eMat 1)) = true := by
    rcases hρ with h | h <;> simp [meqB_iff.2 (hP.symm.trans h)]
  have e5 : (meqB (Type201.k 1) (conjU N) N || meqB (Type201.k 1) (conjU N) (N * eMat 1)) =
      true := by
    rcases hu with h | h
    · simp [meqB_iff.2 ((hU.symm.trans h).trans hMN)]
    · simp [meqB_iff.2 ((hU.symm.trans h).trans hMe)]
  have key := checkV₁_nf x₀ hx₀ x₁ hx₁ x₂ hx₂ y₀ hy₀ y₁ hy₁ y₂ hy₂
  rw [← hNdef, checkV₁, e1, e2, e3, e4, e5] at key
  simp at key

end Stroth34T201Levels

end CFSG.CGT.Stroth77
