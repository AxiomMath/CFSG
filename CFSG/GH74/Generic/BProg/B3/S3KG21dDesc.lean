module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.Generic.BProg.B3.S3KG

open Matrix Subgroup

variable {F : Type} [Field F]

@[expose] noncomputable def descend :
    MulAut (Matrix.SpecialLinearGroup (Fin 2) F) →*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) where
  toFun v := QuotientGroup.congr (center _) (center _) v (Subgroup.map_center_eq v)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' v w := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

theorem descend_mk (v : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (y : Matrix.SpecialLinearGroup (Fin 2) F) :
    descend v (QuotientGroup.mk y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      QuotientGroup.mk (v y) := rfl

theorem descend_conj (s : Matrix.SpecialLinearGroup (Fin 2) F) :
    descend (MulAut.conj s) =
      MulAut.conj (QuotientGroup.mk s : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

theorem transvection_pow_ringChar {i j : Fin 2} (hij : i ≠ j) (c : F) :
    Matrix.SpecialLinearGroup.transvection hij c ^ ringChar F = 1 := by
  have h0 : Matrix.SpecialLinearGroup.transvection hij (0 : F) = 1 := by
    have h := Matrix.SpecialLinearGroup.transvection_add hij (0 : F) 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hn : ∀ n : ℕ, Matrix.SpecialLinearGroup.transvection hij c ^ n =
      Matrix.SpecialLinearGroup.transvection hij ((n : F) * c) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, h0]
    | succ n ih =>
      rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add, Nat.cast_succ, add_mul,
        one_mul]
  rw [hn, ringChar.Nat.cast_ringChar, zero_mul, h0]

theorem mul_self_eq_one_of_mem_center {z : Matrix.SpecialLinearGroup (Fin 2) F}
    (hz : z ∈ center (Matrix.SpecialLinearGroup (Fin 2) F)) : z * z = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  apply Subtype.ext
  rw [Fintype.card_fin] at hr
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrz, Matrix.SpecialLinearGroup.coe_one, scalar_apply,
    diagonal_mul_diagonal, ← sq, hr, diagonal_one]

theorem fix_transvection_of_descend_eq_one [Finite F] (hF : ringChar F ≠ 2)
    {v : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)} (hv : descend v = 1) {i j : Fin 2}
    (hij : i ≠ j) (c : F) :
    v (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij c := by
  set t := Matrix.SpecialLinearGroup.transvection hij c with ht
  have hzc : t⁻¹ * v t ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have h := congrArg (fun φ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =>
      φ (QuotientGroup.mk t)) hv
    simp only [descend_mk, MulAut.one_apply] at h
    exact QuotientGroup.eq.mp h.symm
  set z := t⁻¹ * v t with hzdef
  have hz2 : z * z = 1 := mul_self_eq_one_of_mem_center hzc
  have hvt : v t = t * z := by rw [hzdef, mul_inv_cancel_left]
  have hcomm : Commute t z := Subgroup.mem_center_iff.mp hzc t
  have hp := CharP.prime_ringChar F
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hF
  have htp : t ^ ringChar F = 1 := transvection_pow_ringChar hij c
  have hvtp : (v t) ^ ringChar F = 1 := by rw [← map_pow, htp, map_one]
  have hzp : z ^ ringChar F = z := by
    rw [hk, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  have hz1 : z = 1 := by
    rw [hvt, hcomm.mul_pow, htp, one_mul, hzp] at hvtp
    exact hvtp
  rw [hvt, hz1, mul_one]

theorem descend_injective [Finite F] (hF : ringChar F ≠ 2) :
    Function.Injective (descend (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { carrier := {y | v y = y}
      mul_mem' := fun {a b} ha hb => by
        show v (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one v
      inv_mem' := fun {a} ha => by
        show v a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have htop : H = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := F),
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    exact fix_transvection_of_descend_eq_one hF hv hij c
  refine MulEquiv.ext fun y => ?_
  have hy : y ∈ H := htop ▸ mem_top y
  exact hy

theorem exists_conj_of_descend [Finite F] (hF : ringChar F ≠ 2)
    {v : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)}
    {x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F} (hx : descend v = MulAut.conj x) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) F, v = MulAut.conj s := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨s, descend_injective hF (by rw [hx, descend_conj])⟩

end CFSG.GH74.Generic.BProg.B3.S3KG
