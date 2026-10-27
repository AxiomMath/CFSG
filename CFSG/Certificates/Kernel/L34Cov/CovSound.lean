
module

public import CFSG.Certificates.Kernel.L34Cov.WalkSound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase
import all CFSG.Fischer.F4
import all CFSG.LieType.Multipliers.L34Data

public section

namespace CFSG.Certificates.L34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers.L34 CFSG.Fischer
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable CFSG.ComponentClassification.GrSLit.L34Facts

variable {X : Type} {n : ℕ}

@[expose] def IsTr (e : (Equiv.Perm (X × ZMod n))ᵐᵒᵖ) (t : ZMod n) : Prop :=
  ∀ p, e.unop p = (p.1, p.2 + t)

theorem isTr_one : IsTr (1 : (Equiv.Perm (X × ZMod n))ᵐᵒᵖ) 0 := fun p => by simp

theorem IsTr.mul {a b : (Equiv.Perm (X × ZMod n))ᵐᵒᵖ} {s t : ZMod n} (ha : IsTr a s)
    (hb : IsTr b t) : IsTr (a * b) (s + t) := fun p => by
  rw [MulOpposite.unop_mul, Equiv.Perm.mul_apply, ha, hb, add_assoc]

theorem IsTr.pow {a : (Equiv.Perm (X × ZMod n))ᵐᵒᵖ} {s : ZMod n} (ha : IsTr a s) :
    ∀ k : ℕ, IsTr (a ^ k) ((k : ZMod n) * s)
  | 0 => by simpa using (isTr_one (X := X) (n := n))
  | k + 1 => by
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact (ha.pow k).mul ha

theorem IsTr.eq_one {a : (Equiv.Perm (X × ZMod n))ᵐᵒᵖ} (ha : IsTr a 0) : a = 1 := by
  apply MulOpposite.unop_injective
  ext1 p
  rw [ha, add_zero]
  rfl

@[expose] def MonoModel (T : ℕ → ℕ) (a₁ a₂ : ZMod 4) : Prop :=
  ∃ φ : Cover →* (Equiv.Perm (Fin 960 × ZMod 4))ᵐᵒᵖ,
    IsTr (φ z₁) a₁ ∧ IsTr (φ z₂) a₂ ∧ IsTr (φ z₃) 0 ∧
    ∀ (u : List (Fin 2 × Bool)) (x : Fin 960),
      Mono.walk T 4 4 (u.map letterCode) x.val =
        ((φ (cv u)).unop (x, 0)).1.val + Nat.shiftLeft ((φ (cv u)).unop (x, 0)).2.val 16

theorem pSL_z₁ : pSL z₁ = 1 := by
  rw [pSL_mk]
  exact lift_genSL_eq_one zOne_eq_one

theorem pSL_z₂ : pSL z₂ = 1 := by
  rw [pSL_mk]
  exact lift_genSL_eq_one zTwo_eq_one

theorem exists_of_mem_ker_pSL {u : Cover} (hu : u ∈ pSL.ker) :
    ∃ a b : ZMod 4, u = z₁ ^ a.val * z₂ ^ b.val := by
  let f : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* Cover :=
    zHom.comp ((MonoidHom.fst _ _).prod ((MonoidHom.snd _ _).prod 1))
  have hf : Function.Injective f := by
    intro x y e
    have e2 := zHom_injective e
    simp only [MonoidHom.prod_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MonoidHom.one_apply,
      Prod.mk.injEq] at e2
    exact Prod.ext e2.1 e2.2.1
  have hfa : ∀ x, f x = z₁ ^ (Multiplicative.toAdd x.1).val * z₂ ^ (Multiplicative.toAdd x.2).val := by
    intro x
    change zHom (x.1, x.2, 1) = _
    rw [zHom_apply]
    simp
  have hle : f.range ≤ pSL.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hfa, map_mul, map_pow, map_pow, pSL_z₁, pSL_z₂, one_pow, one_pow,
      mul_one]
  have hcard : Nat.card pSL.ker ≤ Nat.card f.range := by
    obtain ⟨e⟩ := nonempty_ker_pSL_mulEquiv
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hu
  obtain ⟨x, rfl⟩ := hu
  exact ⟨Multiplicative.toAdd x.1, Multiplicative.toAdd x.2, hfa x⟩

@[expose] def omF : F4 := ⟨2⟩

theorem lamR_lt (r : ℕ) : lamR r < 4 := by
  unfold lamR
  cases Nat.beq r 0 <;> cases Nat.beq r 1 <;> decide

theorem lamC_lt (c : ℕ) : lamC c < 4 := lamR_lt _

theorem lamR_eq : ∀ r < 3, (⟨⟨lamR r, lamR_lt r⟩⟩ : F4) = omF ^ r := by decide +kernel

theorem lamC_eq (c : ℕ) : (⟨⟨lamC c, lamC_lt c⟩⟩ : F4) = omF ^ c := by
  have h3 : omF ^ 3 = 1 := by decide +kernel
  calc (⟨⟨lamC c, lamC_lt c⟩⟩ : F4) = omF ^ (c % 3) := lamR_eq (c % 3) (Nat.mod_lt _ (by norm_num))
    _ = omF ^ c := by
      conv_rhs => rw [← Nat.div_add_mod c 3]
      rw [pow_add, pow_mul, h3, one_pow, one_mul]

theorem wordMat_zThree : wordMat zThree = Mat3.scalar omF := by decide +kernel

theorem coe_pSL_cv (w : List (Fin 2 × Bool)) :
    ((pSL (cv w) : SL3) : M3) = (wordMat w).toMatrix := by
  rw [pSL_mk, coe_lift_genSL]

theorem pSL_cv_of_rowsOK {V : ℕ} (hV : vtOK V = true)
    {w : List (Fin 2 × Bool)} {c : ℕ} (h : rowsOK V (w.map letterCode) (lamC c) = true) :
    pSL (cv w) = pSL z₃ ^ c := by
  have hW := wordMat_eq_scalar hV (lamC_lt c) h
  rw [lamC_eq] at hW
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_pSL_cv, coe_pSL_cv, hW, wordMat_zThree,
    Mat3.toMatrix_scalar, Mat3.toMatrix_scalar, map_pow]

theorem shiftLeft16_inj {a b : ℕ} (h : Nat.shiftLeft a 16 = Nat.shiftLeft b 16) : a = b := by
  change a <<< 16 = b <<< 16 at h
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem label_of_walk {T : ℕ → ℕ}
    {φ : Cover →* (Equiv.Perm (Fin 960 × ZMod 4))ᵐᵒᵖ}
    (hw : ∀ (u : List (Fin 2 × Bool)) (x : Fin 960),
      Mono.walk T 4 4 (u.map letterCode) x.val =
        ((φ (cv u)).unop (x, 0)).1.val + Nat.shiftLeft ((φ (cv u)).unop (x, 0)).2.val 16)
    {w : List (Fin 2 × Bool)} {s : ZMod 4} (hs : IsTr (φ (cv w)) s) {k : ℕ}
    (h : Mono.walk T 4 4 (w.map letterCode) 0 = Nat.shiftLeft (k % 4) 16) : s = (k : ZMod 4) := by
  have e := hw w 0
  rw [hs] at e
  simp only [Fin.val_zero, zero_add] at e
  rw [h] at e
  have e2 := shiftLeft16_inj e
  rw [← ZMod.natCast_zmod_val s, ← e2, ZMod.natCast_mod]

theorem cv_eq_of_cvIdOK {V : ℕ} {TA TB : ℕ → ℕ}
    (hV : vtOK V = true) (hA : MonoModel TA 3 2) (hB : MonoModel TB 0 1)
    {w : List (Fin 2 × Bool)} {c₁ c₂ c₃ : ℕ}
    (h : cvIdOK V TA TB (w.map letterCode) c₁ c₂ c₃ = true) :
    cv w = z₁ ^ c₁ * z₂ ^ c₂ * z₃ ^ c₃ := by
  unfold cvIdOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hr, ha, hb⟩ := h
  have hP := pSL_cv_of_rowsOK hV hr
  set zw := z₁ ^ c₁ * z₂ ^ c₂ * z₃ ^ c₃ with hzw
  have hu : cv w * zw⁻¹ ∈ pSL.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hP, hzw, map_mul, map_mul, map_pow, map_pow,
      map_pow, pSL_z₁, pSL_z₂, one_pow, one_pow, one_mul, one_mul, mul_inv_cancel]
  obtain ⟨a, b, hab⟩ := exists_of_mem_ker_pSL hu
  have hcv : cv w = z₁ ^ a.val * z₂ ^ b.val * zw := by
    rw [← hab]
    group
  obtain ⟨φA, hA1, hA2, hA3, hAw⟩ := hA
  obtain ⟨φB, hB1, hB2, hB3, hBw⟩ := hB
  have trA : IsTr (φA (cv w)) ((a.val : ZMod 4) * 3 + (b.val : ZMod 4) * 2 +
      ((c₁ : ZMod 4) * 3 + (c₂ : ZMod 4) * 2 + (c₃ : ZMod 4) * 0)) := by
    rw [hcv, hzw]
    simp only [map_mul, map_pow]
    exact (((hA1.pow _).mul (hA2.pow _)).mul (((hA1.pow _).mul (hA2.pow _)).mul (hA3.pow _)))
  have trB : IsTr (φB (cv w)) ((a.val : ZMod 4) * 0 + (b.val : ZMod 4) * 1 +
      ((c₁ : ZMod 4) * 0 + (c₂ : ZMod 4) * 1 + (c₃ : ZMod 4) * 0)) := by
    rw [hcv, hzw]
    simp only [map_mul, map_pow]
    exact (((hB1.pow _).mul (hB2.pow _)).mul (((hB1.pow _).mul (hB2.pow _)).mul (hB3.pow _)))
  have eA := label_of_walk hAw trA (Nat.eq_of_beq_eq_true ha)
  have eB := label_of_walk hBw trB (Nat.eq_of_beq_eq_true hb)
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at eA eB
  rw [show (Nat.mul 3 c₁).add (Nat.mul 2 c₂) = 3 * c₁ + 2 * c₂ from rfl] at eA
  push_cast at eA eB
  have hb0 : b = 0 := by linear_combination eB
  have ha3 : 3 * a = 0 := by linear_combination eA - 2 * eB
  have ha0 : a = 0 := by
    revert ha3
    generalize a = x
    decide +revert
  rw [hcv, ha0, hb0, ZMod.val_zero, pow_zero, pow_zero, one_mul, one_mul]

end CFSG.Certificates.L34Cov

end
