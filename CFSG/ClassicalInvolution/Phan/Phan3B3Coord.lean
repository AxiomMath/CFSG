module

public import CFSG.ClassicalInvolution.Phan.PhanB21Exists
public import CFSG.ClassicalInvolution.Phan.Phan3AModel
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary
open CFSG.LieType.Multipliers.U43 (F9)

abbrev F3F : Type := GaloisField 3 1

theorem natCard_F3F : Nat.card F3F = 3 := by
  simpa using GaloisField.card 3 1 one_ne_zero

noncomputable def eF : ZMod 3 ≃+* F3F :=
  haveI := Fintype.ofFinite F3F
  FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, natCard_F3F])

def zF9 : ZMod 3 →+* F9 where
  toFun x := ⟨x, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' x y := by revert x y; decide +kernel
  map_add' x y := by revert x y; decide +kernel

noncomputable def fK : F3F →+* K9 := (phi9r.comp zF9).comp eF.symm.toRingHom

@[instance_reducible] noncomputable def algF3K9 : Algebra F3F K9 := fK.toAlgebra

attribute [local instance] algF3K9

theorem algebraMap_eq (x : ZMod 3) : algebraMap F3F K9 (eF x) = phi9r (zF9 x) := by
  show fK (eF x) = _
  simp [fK]

theorem i9_mul_i9 : i9 * i9 = -1 := by decide +kernel

theorem zF9_add_mul_i9 (x : F9) : zF9 (x.re) + zF9 (x.im) * i9 = x := by
  revert x; decide +kernel

theorem zF9_eq_zero : ∀ a b : ZMod 3, zF9 a + zF9 b * i9 = 0 → a = 0 ∧ b = 0 := by decide +kernel

theorem cj9_zF9 (a : ZMod 3) : cj9 (zF9 a) = zF9 a := by revert a; decide +kernel

theorem cj9_i9 : cj9 i9 = -i9 := by decide +kernel

noncomputable def qData3 : QData F3F K9 (unitaryInvolution K9 3 1) where
  i := phi9r i9
  hi := by
    rw [← map_mul, i9_mul_i9, map_neg, map_one, map_neg, map_one]
  re z := eF ((phi9.symm z).re)
  im z := eF ((phi9.symm z).im)
  decomp z := by
    rw [algebraMap_eq, algebraMap_eq, ← map_mul, ← map_add, zF9_add_mul_i9]
    exact (phi9.apply_symm_apply z).symm
  ind a b h := by
    obtain ⟨a', rfl⟩ := eF.surjective a
    obtain ⟨b', rfl⟩ := eF.surjective b
    rw [algebraMap_eq, algebraMap_eq, ← map_mul, ← map_add] at h
    have h0 : zF9 a' + zF9 b' * i9 = 0 :=
      phi9r.injective (by rw [h, map_zero])
    obtain ⟨h1, h2⟩ := zF9_eq_zero a' b' h0
    rw [h1, h2]
    exact ⟨map_zero _, map_zero _⟩
  σ_alg a := by
    obtain ⟨a', rfl⟩ := eF.surjective a
    rw [algebraMap_eq, phi9_cj, cj9_zF9]
  σ_i := by
    rw [phi9_cj, cj9_i9, map_neg]

theorem qData3_re (x : F9) : qData3.re (phi9r x) = eF x.re := by
  show eF ((phi9.symm (phi9r x)).re) = _
  rw [show phi9.symm (phi9r x) = x from phi9.symm_apply_apply x]

theorem qData3_im (x : F9) : qData3.im (phi9r x) = eF x.im := by
  show eF ((phi9.symm (phi9r x)).im) = _
  rw [show phi9.symm (phi9r x) = x from phi9.symm_apply_apply x]

theorem hcd3 : (1 : F3F) * 1 + 1 * 1 = -1 := by
  have h : ((1 : ZMod 3) + 1 + 1 : ZMod 3) = 0 := by decide
  have := congrArg eF h
  simp only [map_add, map_one, map_zero] at this
  linear_combination this

theorem h2F : (2 : F3F) ≠ 0 := by
  intro h
  have h1 := congrArg eF.symm h
  rw [map_ofNat, map_zero] at h1
  revert h1
  decide

noncomputable def b2Coord3 : B2Coord card_K9 F3F h2F :=
  b2CoordOfData qData3 1 1 hcd3 h2F card_K9

section Mats

open Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem eF_neg (x : ZMod 3) : eF (-x) = -eF x := map_neg eF x

theorem eF_inv2 : eF ((2 : ZMod 3)⁻¹) = (2 : F3F)⁻¹ := by
  rw [map_inv₀, map_ofNat]

theorem spBlockMat_map {κ : Type} [Fintype κ] [DecidableEq κ] {R S : Type} [Field R] [Field S]
    {G : Type} [FunLike G R S] [RingHomClass G R S] (f : G) (p q : κ)
    (A : Matrix (Fin 2) (Fin 2) R) :
    (CFSG.LieType.Steinberg.Sp.blockMat p q A).map f =
      CFSG.LieType.Steinberg.Sp.blockMat p q (A.map f) := by
  ext a b
  simp only [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.map_apply, Matrix.of_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem conjD2_map {R S : Type} [Field R] [Field S] {G : Type} [FunLike G R S]
    [RingHomClass G R S] (f : G) (t : R)
    (X : Matrix (Fin 2) (Fin 2) R) : (conjD2 t X).map f = conjD2 (f t) (X.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjD2, map_neg, map_mul, map_ofNat]

theorem nuMat_map {R S : Type} [Field R] [Field S] {G : Type} [FunLike G R S]
    [RingHomClass G R S] (f : G) (c d a b β1 β2 : R) :
    (nuMat c d a b β1 β2).map f = nuMat (f c) (f d) (f a) (f b) (f β1) (f β2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nuMat, map_neg, map_mul, map_add, map_sub]

theorem twMat_map {R S : Type} [Field R] [Field S] {G : Type} [FunLike G R S]
    [RingHomClass G R S] (f : G) (t : R)
    (M : Matrix (Fin 2) (Fin 2) R) : (twMat t M).map f = twMat (f t) (M.map f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twMat, Matrix.fromBlocks, map_neg, map_mul, map_add, map_sub]

theorem ent_A2_00 : ent A2 0 0 = phi9r i9 := rfl

theorem ent_A2_01 : ent A2 0 1 = phi9r 0 := rfl

theorem ent_B2_00 : ent B2 0 0 = phi9r ⟨1, 1⟩ := rfl

theorem ent_B2_01 : ent B2 0 1 = phi9r ⟨1, 1⟩ := rfl

theorem nuOf_A2 (c d : F3F) :
    nuOf qData3 c d A2 = nuMat c d (eF 0) (eF 1) (eF 0) (eF 0) := by
  simp only [nuOf, ent_A2_00, ent_A2_01, qData3_re, qData3_im]
  rfl

theorem nuOf_B2 (c d : F3F) :
    nuOf qData3 c d B2 = nuMat c d (eF 1) (eF 1) (eF 1) (eF 1) := by
  simp only [nuOf, ent_B2_00, ent_B2_01, qData3_re, qData3_im]

@[expose] def LAz : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
    (conjD2 (2⁻¹ : ZMod 3) (nuMat 1 (-1) 0 1 0 0))

@[expose] def LBz : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
    (conjD2 (2⁻¹ : ZMod 3) (nuMat 1 (-1) 1 1 1 1))

@[expose] def SAz : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  twMat (2⁻¹ : ZMod 3) (nuMat 1 1 0 1 0 0)

@[expose] def SBz : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  twMat (2⁻¹ : ZMod 3) (nuMat 1 1 1 1 1 1)

theorem mat_ell_A2 : mat 2 F3F (b2Coord3.ℓ A2) = LAz.map eF := by
  show mat 2 F3F (lHom qData3 1 1 hcd3 h2F A2) = _
  rw [mat_lHom, nuOf_A2, LAz, spBlockMat_map, conjD2_map, nuMat_map, eF_inv2]
  simp [eF_neg]

theorem mat_ell_B2 : mat 2 F3F (b2Coord3.ℓ B2) = LBz.map eF := by
  show mat 2 F3F (lHom qData3 1 1 hcd3 h2F B2) = _
  rw [mat_lHom, nuOf_B2, LBz, spBlockMat_map, conjD2_map, nuMat_map, eF_inv2]
  simp [eF_neg]

theorem mat_s_A2 : mat 2 F3F (b2Coord3.s A2) = SAz.map eF := by
  show mat 2 F3F (sHom qData3 1 1 hcd3 h2F A2) = _
  rw [mat_sHom, nuOf_A2, SAz, twMat_map, nuMat_map, eF_inv2]
  simp

theorem mat_s_B2 : mat 2 F3F (b2Coord3.s B2) = SBz.map eF := by
  show mat 2 F3F (sHom qData3 1 1 hcd3 h2F B2) = _
  rw [mat_sHom, nuOf_B2, SBz, twMat_map, nuMat_map, eF_inv2]
  simp

end Mats

end CFSG.ClassicalInvolution.Phan.Q3G
