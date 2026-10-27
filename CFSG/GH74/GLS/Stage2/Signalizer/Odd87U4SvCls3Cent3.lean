module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Cent3Elt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Cent3Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Perm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Std
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open scoped MatrixGroups commutatorElement

section Main

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {A : GL (HypIndex 2 0) K}
  {E : Matrix (HypIndex 2 0) (Fin 4) K} {d : Fin 4 → h.fixedField}

theorem U4Frame.E_mul_coord (fr : U4Frame h A E d) (X : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :
    E * (U4Frame.fm h E d * X * E) = X * E := by
  calc E * (U4Frame.fm h E d * X * E) = (E * U4Frame.fm h E d) * X * E := by
        simp only [Matrix.mul_assoc]
    _ = X * E := by rw [fr.E_mul_fm, Matrix.one_mul]

theorem U4Frame.coord_back (fr : U4Frame h A E d) (X : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :
    E * (U4Frame.fm h E d * X * E) * U4Frame.fm h E d = X := by
  rw [fr.E_mul_coord, Matrix.mul_assoc, fr.E_mul_fm, Matrix.mul_one]

theorem U4Frame.coord_pow (fr : U4Frame h A E d) (X : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (k : ℕ) : (U4Frame.fm h E d * X * E) ^ k = U4Frame.fm h E d * X ^ k * E := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, fr.fm_mul_E]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc U4Frame.fm h E d * X ^ k * E * (U4Frame.fm h E d * X * E)
        = U4Frame.fm h E d * X ^ k * (E * U4Frame.fm h E d) * X * E := by
          simp only [Matrix.mul_assoc]
      _ = U4Frame.fm h E d * (X ^ k * X) * E := by
          rw [fr.E_mul_fm, Matrix.mul_one]
          simp only [Matrix.mul_assoc]

theorem U4Frame.coord_iso (fr : U4Frame h A E d) {X : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hX : (X.map h.bar)ᵀ * hypGram 2 0 K * X = hypGram 2 0 K) :
    ((U4Frame.fm h E d * X * E).map h.bar)ᵀ * Matrix.diagonal (fun i => ((d i : h.fixedField) : K)) *
      (U4Frame.fm h E d * X * E) = Matrix.diagonal (fun i => ((d i : h.fixedField) : K)) := by
  have hEx := fr.E_mul_coord X
  calc ((U4Frame.fm h E d * X * E).map h.bar)ᵀ *
        Matrix.diagonal (fun i => ((d i : h.fixedField) : K)) * (U4Frame.fm h E d * X * E)
      = ((U4Frame.fm h E d * X * E).map h.bar)ᵀ * ((E.map h.bar)ᵀ * hypGram 2 0 K * E) *
          (U4Frame.fm h E d * X * E) := by rw [fr.gram]
    _ = ((E * (U4Frame.fm h E d * X * E)).map h.bar)ᵀ * hypGram 2 0 K *
          (E * (U4Frame.fm h E d * X * E)) := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((X * E).map h.bar)ᵀ * hypGram 2 0 K * (X * E) := by rw [hEx]
    _ = (E.map h.bar)ᵀ * ((X.map h.bar)ᵀ * hypGram 2 0 K * X) * E := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (E.map h.bar)ᵀ * hypGram 2 0 K * E := by rw [hX]
    _ = Matrix.diagonal (fun i => ((d i : h.fixedField) : K)) := fr.gram

theorem U4Frame.exists_norm (fr : U4Frame h A E d) (i : Fin 4) :
    ∃ a : K, a ≠ 0 ∧ h.norm a = ((d i : h.fixedField) : K) := by
  obtain ⟨a, ha⟩ := h.card_ker_normUnits_and_surjective.2 (Units.mk0 (d i) (fr.ne i))
  refine ⟨(a : K), a.ne_zero, ?_⟩
  have := congrArg (fun v : h.fixedFieldˣ => (((v : h.fixedField)) : K)) ha
  simpa using this

theorem u4_cls3_cent3_frame (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1)
    {σ : K ≃+* K} {hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0}
    {α : MulAut (hypPSU h 2 0)}
    (hα : α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩)
    (hσ : ∀ c, σ c = h.bar c) (hq : p ^ f = 3) (hd01 : d 0 = d 1) (x : ↥(hypSU h 2 0))
    (hxr : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (hc : ∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α → hypProj h 2 0 b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    x ∈ hypScalars h 2 0 := by
  classical
  obtain ⟨r, n, hr, hr5, hxn⟩ := hxr
  have hK : Nat.card K = 9 := by rw [h.card_eq_sq, hq]; norm_num
  have hdvd : p ∣ 3 := hq ▸ dvd_pow_self p (by have := h.one_le; omega)
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 hdvd
  have hf1 : f = 1 := by
    subst hp3
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ f = 3 ^ 1 by simpa using hq)
  subst hp3 hf1
  obtain ⟨a, b, haA, hbA, hab⟩ := fr.exists_comm_elts hA hAA hd01
  have hxab := hc a b (u4_cls3_proj_mem_fix hα hσ a haA) (u4_cls3_proj_mem_fix hα hσ b hbA)
  set X : Matrix (HypIndex 2 0) (HypIndex 2 0) K := ((x : GL (HypIndex 2 0) K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K) with hX
  have hcomm : X * (E * (u4My : Matrix (Fin 4) (Fin 4) K) * U4Frame.fm h E d) =
      (E * (u4My : Matrix (Fin 4) (Fin 4) K) * U4Frame.fm h E d) * X := by
    have := congrArg (fun g : ↥(hypSU h 2 0) => ((g : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hxab
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [hab] at this
    exact this
  have hY : (U4Frame.fm h E d * X * E) * (u4My : Matrix (Fin 4) (Fin 4) K) =
      (u4My : Matrix (Fin 4) (Fin 4) K) * (U4Frame.fm h E d * X * E) := by
    have h1 : U4Frame.fm h E d * (X * (E * (u4My : Matrix (Fin 4) (Fin 4) K) * U4Frame.fm h E d)) *
        E = U4Frame.fm h E d * ((E * (u4My : Matrix (Fin 4) (Fin 4) K) * U4Frame.fm h E d) * X) *
          E := by rw [hcomm]
    calc (U4Frame.fm h E d * X * E) * (u4My : Matrix (Fin 4) (Fin 4) K)
        = U4Frame.fm h E d * (X * (E * u4My * U4Frame.fm h E d)) * E := by
          calc _ = (U4Frame.fm h E d * X * E) * u4My * (U4Frame.fm h E d * E) := by
                rw [fr.fm_mul_E, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]
      _ = U4Frame.fm h E d * ((E * u4My * U4Frame.fm h E d) * X) * E := h1
      _ = (u4My : Matrix (Fin 4) (Fin 4) K) * (U4Frame.fm h E d * X * E) := by
          calc _ = (U4Frame.fm h E d * E) * u4My * (U4Frame.fm h E d * X * E) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [fr.fm_mul_E, Matrix.one_mul]
  have hiso := fr.coord_iso (X := X) (mem_hypSU.1 x.2).1
  have hpow : (U4Frame.fm h E d * X * E) ^ (r ^ n) = 1 := by
    rw [fr.coord_pow, hX, ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hxn]
    simp [fr.fm_mul_E]
  have hY' : (U4Frame.fm h E d * X * E) * Matrix.diagonal ![-1, -1, 1, 1] =
      Matrix.diagonal ![-1, -1, 1, 1] * (U4Frame.fm h E d * X * E) := hY
  have h1 := core4 hK h hr hr5 (fun i => ((d i : h.fixedField) : K)) fr.exists_norm hY' hiso hpow
  have hx1 : X = 1 := by
    rw [← fr.coord_back X, h1, Matrix.mul_one, fr.E_mul_fm]
  have hx : x = 1 := Subtype.ext (Units.ext hx1)
  rw [hx]
  exact Subgroup.one_mem _

end Main

theorem ne_two_of_pow_eq_three {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f = 3) : p ≠ 2 := by
  rintro rfl
  have : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩
  rw [hq] at this
  exact absurd this (by decide)

theorem u4_cls3_cent3 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f = 3) (α : MulAut (hypPSU h 2 0)) (hα : SurvU4Cls3 h α) (x : ↥(hypSU h 2 0))
    (hxr : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (hc : ∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α → hypProj h 2 0 b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    x ∈ hypScalars h 2 0 := by
  obtain ⟨A, σ, hx, hA, hσ, hAA, hαeq⟩ := hα
  obtain ⟨E, d, fr, hd01⟩ := u4_cls3_frame_three h (ne_two_of_pow_eq_three h hq) hq hA hAA
  exact u4_cls3_cent3_frame fr hA hAA hαeq hσ hq hd01 x hxr hc

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
