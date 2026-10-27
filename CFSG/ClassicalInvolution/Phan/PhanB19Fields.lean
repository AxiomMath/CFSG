module

public import CFSG.ClassicalInvolution.Phan.PhanB18Rel

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock mat_longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] [Algebra F K] (Q : QData F K (unitaryInvolution K p f)) (c d : F)
  (hcd : c * c + d * d = -1) (h2 : (2 : F) ≠ 0)

theorem hcd_neg {c d : F} (hcd : c * c + d * d = -1) : c * c + -d * -d = -1 := by
  rw [neg_mul_neg]
  exact hcd

@[expose] noncomputable def sHom : Su K p f 2 →* StatedSp 2 F :=
  (twShort h2).comp (nuQ Q c d hcd)

@[expose] noncomputable def lHom : Su K p f 2 →* StatedSp 2 F :=
  (longBlock F 2 1).comp
    ((conjD (2⁻¹ : F) (mul_inv_cancel₀ h2)).comp (nuQ Q c (-d) (hcd_neg hcd)))

theorem mat_sHom (A : Su K p f 2) :
    mat 2 F (sHom Q c d hcd h2 A) = twMat (2⁻¹ : F) (nuOf Q c d A) := by
  show mat 2 F (twShort h2 (nuQ Q c d hcd A)) = _
  rw [mat_twShort, coe_nuQ]

theorem mat_lHom (A : Su K p f 2) :
    mat 2 F (lHom Q c d hcd h2 A) =
      Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
        (conjD2 (2⁻¹ : F) (nuOf Q c (-d) A)) := by
  show mat 2 F (longBlock F 2 1 (conjD (2⁻¹ : F) (mul_inv_cancel₀ h2)
    (nuQ Q c (-d) (hcd_neg hcd) A))) = _
  rw [mat_longBlock_one, coe_conjD, coe_nuQ]

theorem normOne_coord (x : normOne (unitaryInvolution K p f)) :
    Q.re ((x : Kˣ) : K) * Q.re ((x : Kˣ) : K) + Q.im ((x : Kˣ) : K) * Q.im ((x : Kˣ) : K) = 1 := by
  have h := (mem_normOne (unitaryInvolution K p f)).1 x.2
  have := congrArg Q.re h
  rw [mul_comm, Q.re_mul_σ, Q.re_one] at this
  exact this

theorem ent_torus_zero_zero (x : normOne (unitaryInvolution K p f)) :
    ent (torusTwo (unitaryInvolution K p f) x) 0 0 = ((x : Kˣ) : K) := by
  simp [ent, coe_torusTwo]

theorem ent_torus_zero_one (x : normOne (unitaryInvolution K p f)) :
    ent (torusTwo (unitaryInvolution K p f) x) 0 1 = 0 := by
  simp [ent, coe_torusTwo]

theorem nuOf_torus (x : normOne (unitaryInvolution K p f)) :
    nuOf Q c d (torusTwo (unitaryInvolution K p f) x) =
      nuMat c d (Q.re ((x : Kˣ) : K)) (Q.im ((x : Kˣ) : K)) 0 0 := by
  rw [nuOf, ent_torus_zero_zero, ent_torus_zero_one, Q.re_zero, Q.im_zero]

variable {hK : Nat.card K = (p ^ f) ^ 2}

theorem val_inv_normOne (x : normOne (unitaryInvolution K p f)) :
    (((x⁻¹ : normOne (unitaryInvolution K p f)) : Kˣ) : K) =
      unitaryInvolution K p f ((x : Kˣ) : K) := by
  have h := (mem_normOne (unitaryInvolution K p f)).1 x.2
  have h' : ((x : Kˣ) : K) * unitaryInvolution K p f ((x : Kˣ) : K) = 1 := by rw [mul_comm]; exact h
  rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  exact inv_eq_of_mul_eq_one_right h'

theorem ent_conjDiag_zero_one (w : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    ent (conjDiag hK ![w, 1] A) 0 1 = ((w : Kˣ) : K) * ent A 0 1 := by
  simp [ent, coe_conjDiag_apply]

theorem ent_conjDiag_zero_zero (w : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    ent (conjDiag hK ![w, 1] A) 0 0 = ent A 0 0 := by
  have hw : ((w : Kˣ) : K) ≠ 0 := Units.ne_zero _
  simp [ent, coe_conjDiag_apply]
  field_simp

theorem nuOf_conjDiag (w : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    nuOf Q c d (conjDiag hK ![w, 1] A) =
      nuMat c d (Q.re (ent A 0 0)) (Q.im (ent A 0 0))
        (Q.re ((w : Kˣ) : K) * Q.re (ent A 0 1) - Q.im ((w : Kˣ) : K) * Q.im (ent A 0 1))
        (Q.re ((w : Kˣ) : K) * Q.im (ent A 0 1) + Q.im ((w : Kˣ) : K) * Q.re (ent A 0 1)) := by
  rw [nuOf, ent_conjDiag_zero_zero, ent_conjDiag_zero_one, Q.re_mul, Q.im_mul]

theorem nuOf_conjDiag_inv (x : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    nuOf Q c d (conjDiag hK ![x⁻¹, 1] A) =
      nuMat c d (Q.re (ent A 0 0)) (Q.im (ent A 0 0))
        (Q.re ((x : Kˣ) : K) * Q.re (ent A 0 1) + Q.im ((x : Kˣ) : K) * Q.im (ent A 0 1))
        (Q.re ((x : Kˣ) : K) * Q.im (ent A 0 1) - Q.im ((x : Kˣ) : K) * Q.re (ent A 0 1)) := by
  rw [nuOf_conjDiag Q c d x⁻¹ A, val_inv_normOne, Q.re_σ, Q.im_σ]
  congr 1 <;> ring

theorem nuOf_conjDiag_sq (y : normOne (unitaryInvolution K p f)) (A : Su K p f 2) (c' : F) :
    nuOf Q c' d (conjDiag hK ![y⁻¹ * y⁻¹, 1] A) =
      nuMat c' d (Q.re (ent A 0 0)) (Q.im (ent A 0 0))
        ((Q.re ((y : Kˣ) : K) * Q.re ((y : Kˣ) : K) - Q.im ((y : Kˣ) : K) * Q.im ((y : Kˣ) : K)) *
            Q.re (ent A 0 1) - (-(2 * Q.re ((y : Kˣ) : K) * Q.im ((y : Kˣ) : K))) *
            Q.im (ent A 0 1))
        ((Q.re ((y : Kˣ) : K) * Q.re ((y : Kˣ) : K) - Q.im ((y : Kˣ) : K) * Q.im ((y : Kˣ) : K)) *
            Q.im (ent A 0 1) + (-(2 * Q.re ((y : Kˣ) : K) * Q.im ((y : Kˣ) : K))) *
            Q.re (ent A 0 1)) := by
  have hval : (((y⁻¹ * y⁻¹ : normOne (unitaryInvolution K p f)) : Kˣ) : K) =
      unitaryInvolution K p f ((y : Kˣ) : K) * unitaryInvolution K p f ((y : Kˣ) : K) := by
    rw [Subgroup.coe_mul, Units.val_mul, val_inv_normOne]
  rw [nuOf_conjDiag Q c' d (y⁻¹ * y⁻¹) A, hval, Q.re_mul, Q.im_mul, Q.re_σ, Q.im_σ]
  congr 1 <;> ring

theorem comm_tor_rel (x y : normOne (unitaryInvolution K p f)) :
    lHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x) *
        sHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) y) =
      sHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) y) *
        lHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x) := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  apply mat_injective
  rw [map_mul, map_mul, mat_lHom, mat_sHom, nuOf_torus, nuOf_torus]
  exact rel_B1 _ c d _ _ _ _ ht

theorem conj_ℓ_s_rel (x : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    lHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x) * sHom Q c d hcd h2 A *
        (lHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x))⁻¹ =
      sHom Q c d hcd h2 (conjDiag hK ![x⁻¹, 1] A) := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, mat_lHom, mat_sHom, mat_sHom, nuOf_torus, nuOf_conjDiag_inv]
  exact rel_B2 _ c d _ _ (Q.re (ent A 0 0)) (Q.im (ent A 0 0)) (Q.re (ent A 0 1))
    (Q.im (ent A 0 1)) ht (normOne_coord Q x)

theorem conj_s_ℓ_rel (y : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    sHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) y) * lHom Q c d hcd h2 A *
        (sHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) y))⁻¹ =
      lHom Q c d hcd h2 (conjDiag hK ![y⁻¹ * y⁻¹, 1] A) := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, mat_lHom, mat_sHom, mat_lHom, nuOf_torus, nuOf_conjDiag_sq]
  exact rel_B3 _ c d _ _ (Q.re (ent A 0 0)) (Q.im (ent A 0 0)) (Q.re (ent A 0 1))
    (Q.im (ent A 0 1)) ht (normOne_coord Q y)

end CFSG.ClassicalInvolution.PhanB3
