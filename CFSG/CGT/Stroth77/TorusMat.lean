module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.CGT.Stroth77

open Matrix

abbrev Torus (k : Fin 3 → ℕ) := (i : Fin 3) → ZMod (2 ^ k i)

abbrev StrothTorus (m n : ℕ) := Torus ![m, n, n]

abbrev IntMat := Matrix (Fin 3) (Fin 3) ℤ

@[expose] def gen (k : Fin 3 → ℕ) (j : Fin 3) : Torus k := Pi.single j 1

@[expose] def Compat (k : Fin 3 → ℕ) (M : IntMat) : Prop :=
  ∀ i j, (2 : ℤ) ^ k i ∣ 2 ^ k j * M i j

@[expose] def MatEq (k : Fin 3 → ℕ) (A B : IntMat) : Prop :=
  ∀ i j, A i j ≡ B i j [ZMOD 2 ^ k i]

variable {k : Fin 3 → ℕ}

theorem Compat.one : Compat k 1 := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne' (Ne.symm h)]

theorem Compat.mul {M N : IntMat} (hM : Compat k M) (hN : Compat k N) : Compat k (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.dvd_sum fun l _ => ?_
  obtain ⟨p, hp⟩ := hM i l
  obtain ⟨q, hq⟩ := hN l j
  exact ⟨p * q, by linear_combination (M i l) * hq + q * hp⟩

@[expose] def entryHom (k : Fin 3 → ℕ) (M : IntMat) (hM : Compat k M) (i j : Fin 3) :
    ZMod (2 ^ k j) →+ ZMod (2 ^ k i) :=
  ZMod.lift (2 ^ k j) ⟨zmultiplesHom (ZMod (2 ^ k i)) ((M i j : ℤ) : ZMod (2 ^ k i)), by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 ^ k j * M i j) (2 ^ k i)).2
      (by simpa using hM i j)
    simpa [zmultiplesHom_apply, zsmul_eq_mul] using h⟩

theorem entryHom_intCast (M : IntMat) (hM : Compat k M) (i j : Fin 3) (z : ℤ) :
    entryHom k M hM i j (z : ZMod (2 ^ k j)) = ((z * M i j : ℤ) : ZMod (2 ^ k i)) := by
  simp [entryHom, ZMod.lift_coe, zmultiplesHom_apply, zsmul_eq_mul]

@[expose] def matAct (k : Fin 3 → ℕ) (M : IntMat) (hM : Compat k M) : Torus k →+ Torus k :=
  Pi.addMonoidHom fun i =>
    ∑ j, (entryHom k M hM i j).comp (Pi.evalAddMonoidHom (fun j => ZMod (2 ^ k j)) j)

theorem matAct_apply (M : IntMat) (hM : Compat k M) (x : Torus k) (i : Fin 3) :
    matAct k M hM x i = ∑ j, entryHom k M hM i j (x j) := by
  show (∑ j, (entryHom k M hM i j).comp
    (Pi.evalAddMonoidHom (fun j => ZMod (2 ^ k j)) j)) x = _
  simp [AddMonoidHom.finset_sum_apply]

theorem torus_hom_ext {A : Type*} [AddCommMonoid A] (f g : Torus k →+ A)
    (h : ∀ (j : Fin 3) (z : ℤ), f (Pi.single j (z : ZMod (2 ^ k j))) =
      g (Pi.single j (z : ZMod (2 ^ k j)))) : f = g :=
  AddMonoidHom.functions_ext _ f g fun j x => by
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    exact h j z

theorem matAct_single (M : IntMat) (hM : Compat k M) (i j : Fin 3) (z : ℤ) :
    matAct k M hM (Pi.single j (z : ZMod (2 ^ k j))) i = ((z * M i j : ℤ) : ZMod (2 ^ k i)) := by
  rw [matAct_apply, Finset.sum_eq_single j]
  · simp [entryHom_intCast]
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

theorem matAct_gen (M : IntMat) (hM : Compat k M) (i j : Fin 3) :
    matAct k M hM (gen k j) i = ((M i j : ℤ) : ZMod (2 ^ k i)) := by
  simpa [gen] using matAct_single M hM i j 1

theorem matAct_gen_eq (M : IntMat) (hM : Compat k M) (j : Fin 3) :
    matAct k M hM (gen k j) =
      (M 0 j) • gen k 0 + (M 1 j) • gen k 1 + (M 2 j) • gen k 2 := by
  funext i
  rw [matAct_gen]
  fin_cases i <;> simp [gen, Pi.single_apply]

theorem matAct_mul (M N : IntMat) (hM : Compat k M) (hN : Compat k N) :
    matAct k (M * N) (hM.mul hN) = (matAct k M hM).comp (matAct k N hN) := by
  refine torus_hom_ext _ _ fun j z => ?_
  funext i
  have h1 : matAct k N hN (Pi.single j (z : ZMod (2 ^ k j))) =
      fun l => ((z * N l j : ℤ) : ZMod (2 ^ k l)) :=
    funext fun l => matAct_single N hN l j z
  rw [AddMonoidHom.comp_apply, h1, matAct_single, matAct_apply]
  simp only [entryHom_intCast, Matrix.mul_apply, Finset.mul_sum, Int.cast_sum]
  exact Finset.sum_congr rfl fun l _ => by push_cast; ring

theorem matAct_one : matAct k 1 Compat.one = AddMonoidHom.id (Torus k) := by
  refine torus_hom_ext _ _ fun j z => ?_
  funext i
  rw [matAct_single]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne' (Ne.symm h), Pi.single_eq_of_ne h]

theorem entryHom_congr {M N : IntMat} (hM : Compat k M) (hN : Compat k N) (i j : Fin 3)
    (h : M i j ≡ N i j [ZMOD 2 ^ k i]) : entryHom k M hM i j = entryHom k N hN i j := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [entryHom_intCast, entryHom_intCast, ZMod.intCast_eq_intCast_iff]
  simpa using h.mul_left z

theorem matAct_congr {M N : IntMat} (hM : Compat k M) (hN : Compat k N) (h : MatEq k M N) :
    matAct k M hM = matAct k N hN := by
  refine AddMonoidHom.ext fun x => ?_
  funext i
  simp only [matAct_apply, entryHom_congr hM hN i _ (h i _)]

theorem matAct_eq_iff {M N : IntMat} (hM : Compat k M) (hN : Compat k N) :
    matAct k M hM = matAct k N hN ↔ MatEq k M N := by
  refine ⟨fun h i j => ?_, matAct_congr hM hN⟩
  have := congrFun (DFunLike.congr_fun h (gen k j)) i
  rw [matAct_gen, matAct_gen, ZMod.intCast_eq_intCast_iff] at this
  simpa using this

theorem MatEq.of_witness {A B W : IntMat} (h : ∀ i j, A i j - B i j = 2 ^ k i * W i j) :
    MatEq k A B := fun i j =>
  (Int.modEq_iff_dvd.2 ⟨-W i j, by linear_combination (-1 : ℤ) * h i j⟩)

theorem MatEq.of_dvd {A B P : IntMat} (s : ℤ) (hs : ∀ i, (2 : ℤ) ^ k i ∣ s)
    (h : ∀ i j, A i j - B i j = s * P i j) : MatEq k A B := fun i j =>
  Int.modEq_iff_dvd.2 (by
    have : (2 : ℤ) ^ k i ∣ B i j - A i j := by
      rw [show B i j - A i j = -(A i j - B i j) by ring, h, ← mul_neg]
      exact (hs i).mul_right _
    exact this)

theorem MatEq.refl (A : IntMat) : MatEq k A A := fun _ _ => Int.ModEq.refl _

theorem MatEq.of_eq {A B : IntMat} (h : A = B) : MatEq k A B := h ▸ MatEq.refl A

theorem Compat.of_witness {M C : IntMat} (h : ∀ i j, 2 ^ k j * M i j = 2 ^ k i * C i j) :
    Compat k M := fun i j => ⟨C i j, h i j⟩

@[expose] def ofCols (c a b : Fin 3 → ℤ) : IntMat := Matrix.of fun i j => ![c, a, b] j i

@[expose] def uMat (cu : Fin 3 → ℤ) (κ : ℤ) : IntMat :=
  ofCols cu ![κ, 0, 1] (![0, 1, 0] - κ • cu)

theorem ofCols_apply (c a b : Fin 3 → ℤ) (i j : Fin 3) :
    ofCols c a b i j = ![c, a, b] j i := rfl

theorem matAct_gen_of (M : IntMat) (hM : Compat k M) (j : Fin 3) (x₀ x₁ x₂ : ℤ)
    (h₀ : M 0 j = x₀) (h₁ : M 1 j = x₁) (h₂ : M 2 j = x₂) :
    matAct k M hM (gen k j) = x₀ • gen k 0 + x₁ • gen k 1 + x₂ • gen k 2 := by
  rw [matAct_gen_eq, h₀, h₁, h₂]

abbrev Torus.c : Torus k := gen k 0
abbrev Torus.a : Torus k := gen k 1
abbrev Torus.b : Torus k := gen k 2

end CFSG.CGT.Stroth77
