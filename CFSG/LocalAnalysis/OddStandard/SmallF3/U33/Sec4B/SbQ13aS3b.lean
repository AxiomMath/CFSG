module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13aS3a
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Pi

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Multiplicative

noncomputable section

variable {B : Type} [Group B]

@[expose] def s3Add (e : B ≃* Outside.Z4pow 2) (φ : MulAut B) :
    (Fin 2 → ZMod 4) →+ (Fin 2 → ZMod 4) where
  toFun v := (e (φ (e.symm (Multiplicative.ofAdd v)))).toAdd
  map_zero' := by simp
  map_add' v w := by
    simp only [ofAdd_add, map_mul, toAdd_mul]

@[expose] def s3coord (e : B ≃* Outside.Z4pow 2) (b : B) : ZMod 4 × ZMod 4 :=
  ((e b).toAdd 0, (e b).toAdd 1)

@[expose] def s3Mat (e : B ≃* Outside.Z4pow 2) (φ : MulAut B) : S3M2 :=
  (s3Add e φ (Pi.single 0 1) 0, s3Add e φ (Pi.single 1 1) 0,
    s3Add e φ (Pi.single 0 1) 1, s3Add e φ (Pi.single 1 1) 1)

private lemma s3vec_one (v : ZMod 4 × ZMod 4) : s3vec s3one v = v := by
  simp [s3vec, s3one]

private lemma s3vec_neg (v : ZMod 4 × ZMod 4) : s3vec s3neg v = (-v.1, -v.2) := by
  have h3 : (3 : ZMod 4) = -1 := by decide
  apply Prod.ext <;> simp [s3vec, s3neg, h3]

private lemma s3vec_mul (X Y : S3M2) (v : ZMod 4 × ZMod 4) :
    s3vec (s3mul X Y) v = s3vec X (s3vec Y v) := by
  simp only [s3vec, s3mul]
  apply Prod.ext <;> ring

private lemma s3vec_ext {M N : S3M2} (h : ∀ v : ZMod 4 × ZMod 4, s3vec M v = s3vec N v) :
    M = N := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  obtain ⟨a, b, c, d⟩ := M
  obtain ⟨a', b', c', d'⟩ := N
  simp only [s3vec, Prod.mk.injEq, mul_one, mul_zero, add_zero, zero_mul, zero_add] at h1 h2
  exact Prod.ext h1.1 (Prod.ext h2.1 (Prod.ext h1.2 h2.2))

private lemma s3Add_eq_sum (e : B ≃* Outside.Z4pow 2) (φ : MulAut B) (v : Fin 2 → ZMod 4) :
    s3Add e φ v = v 0 • s3Add e φ (Pi.single 0 1) + v 1 • s3Add e φ (Pi.single 1 1) := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  have hg : (s3Add e φ).toZModLinearMap 4 v =
      v 0 • (s3Add e φ).toZModLinearMap 4 (Pi.single 0 1)
        + v 1 • (s3Add e φ).toZModLinearMap 4 (Pi.single 1 1) := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  simpa using hg

theorem s3coord_injective (e : B ≃* Outside.Z4pow 2) {b b' : B}
    (h : s3coord e b = s3coord e b') : b = b' := by
  have h0 : (e b).toAdd 0 = (e b').toAdd 0 := by
    have := congrArg Prod.fst h
    simpa [s3coord] using this
  have h1 : (e b).toAdd 1 = (e b').toAdd 1 := by
    have := congrArg Prod.snd h
    simpa [s3coord] using this
  have hv : (e b).toAdd = (e b').toAdd := by
    funext i
    fin_cases i <;> assumption
  exact e.injective (Multiplicative.ext hv)

theorem s3coord_surjective (e : B ≃* Outside.Z4pow 2) (v : ZMod 4 × ZMod 4) :
    ∃ b : B, s3coord e b = v := by
  refine ⟨e.symm (Multiplicative.ofAdd (fun i => if i = 0 then v.1 else v.2)), ?_⟩
  simp [s3coord]

theorem s3coord_one (e : B ≃* Outside.Z4pow 2) : s3coord e 1 = (0, 0) := by
  simp [s3coord]

theorem s3coord_inv (e : B ≃* Outside.Z4pow 2) (b : B) :
    s3coord e b⁻¹ = (-(s3coord e b).1, -(s3coord e b).2) := by
  simp [s3coord, toAdd_inv]

theorem s3Mat_apply (e : B ≃* Outside.Z4pow 2) (φ : MulAut B) (b : B) :
    s3coord e (φ b) = s3vec (s3Mat e φ) (s3coord e b) := by
  have h1 : (e (φ b)).toAdd = s3Add e φ ((e b).toAdd) := by
    simp [s3Add]
  have h2 := s3Add_eq_sum e φ ((e b).toAdd)
  simp only [s3coord]
  rw [h1, h2]
  simp only [s3vec, s3Mat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply Prod.ext <;> ring

theorem s3Mat_mul (e : B ≃* Outside.Z4pow 2) (φ ψ : MulAut B) :
    s3Mat e (φ * ψ) = s3mul (s3Mat e φ) (s3Mat e ψ) := by
  apply s3vec_ext
  intro v
  obtain ⟨b, hb⟩ := s3coord_surjective e v
  rw [← hb]
  have hl : s3vec (s3Mat e (φ * ψ)) (s3coord e b)
      = s3vec (s3Mat e φ) (s3vec (s3Mat e ψ) (s3coord e b)) := by
    rw [← s3Mat_apply e (φ * ψ) b, ← s3Mat_apply e ψ b, ← s3Mat_apply e φ (ψ b)]
    rfl
  rw [hl, s3vec_mul]

theorem s3Mat_one (e : B ≃* Outside.Z4pow 2) : s3Mat e (1 : MulAut B) = s3one := by
  apply s3vec_ext
  intro v
  obtain ⟨b, hb⟩ := s3coord_surjective e v
  rw [← hb, ← s3Mat_apply, s3vec_one]
  rfl

theorem eq_one_of_s3Mat (e : B ≃* Outside.Z4pow 2) {φ : MulAut B} (h : s3Mat e φ = s3one) :
    ∀ b : B, φ b = b := by
  intro b
  apply s3coord_injective e
  rw [s3Mat_apply, h, s3vec_one]

theorem inv_of_s3Mat (e : B ≃* Outside.Z4pow 2) {φ : MulAut B} (h : s3Mat e φ = s3neg) :
    ∀ b : B, φ b = b⁻¹ := by
  intro b
  apply s3coord_injective e
  rw [s3Mat_apply, h, s3vec_neg, s3coord_inv]

theorem s3Mat_fixed (e : B ≃* Outside.Z4pow 2) {φ : MulAut B}
    (h : ∀ b : B, φ b = b → b = 1) :
    ∀ v : ZMod 4 × ZMod 4, s3vec (s3Mat e φ) v = v → v = (0, 0) := by
  intro v hv
  obtain ⟨b, hb⟩ := s3coord_surjective e v
  have hb' : φ b = b := by
    apply s3coord_injective e
    rw [s3Mat_apply, hb, hv]
  have hb1 : b = 1 := h b hb'
  rw [← hb, hb1, s3coord_one]

end

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
