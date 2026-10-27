module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.PureD

open Matrix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private def gramSix : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0]

private def comb (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  A + B + A * gramSix * B

private def phi (b : LinearMap.BilinForm (ZMod 2) V) (v : Fin 6 → V)
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) (x : V) : V :=
  x + ∑ i, (A *ᵥ fun j => b x (v j)) i • v i

private theorem gramSix_transpose : gramSixᵀ = gramSix := by decide

private theorem gramSix_symm (i j : Fin 6) : gramSix i j = gramSix j i := by
  rw [← transpose_apply gramSix i j, gramSix_transpose]

section Phi

variable {b : LinearMap.BilinForm (ZMod 2) V} {v : Fin 6 → V}

private theorem ell_phi (hv : ∀ i j, b (v i) (v j) = gramSix i j)
    (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) (x : V) :
    (fun j => b (phi b v B x) (v j)) =
      (fun j => b x (v j)) + gramSix *ᵥ (B *ᵥ fun j => b x (v j)) := by
  funext j
  simp only [phi, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hv, Pi.add_apply, Matrix.mulVec,
    dotProduct]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gramSix_symm, mul_comm]

private theorem phi_phi (hv : ∀ i j, b (v i) (v j) = gramSix i j)
    (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) (x : V) :
    phi b v A (phi b v B x) = phi b v (comb A B) x := by
  have h := ell_phi hv B x
  unfold phi at h ⊢
  rw [h]
  simp only [comb, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Pi.add_apply,
    add_smul, Finset.sum_add_distrib]
  abel

private theorem phi_single (m : Fin 6) (x : V) :
    phi b v (Matrix.single m m 1) x = x + b x (v m) • v m := by
  simp only [phi, Matrix.single_mulVec_eq, one_mul, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

private theorem phi_commute (hv : ∀ i j, b (v i) (v j) = gramSix i j)
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) (g : V →ₗ[ZMod 2] V)
    (hg : ∀ x y, b (g x) (g y) = b x y) (hgv : ∀ i, g (v i) = v i) (x : V) :
    phi b v A (g x) = g (phi b v A x) := by
  have hℓ : (fun j => b (g x) (v j)) = fun j => b x (v j) := by
    funext j
    calc b (g x) (v j) = b (g x) (g (v j)) := by rw [hgv]
      _ = b x (v j) := hg x (v j)
  simp only [phi, hℓ, map_add, map_sum, map_smul, hgv]

end Phi

private def matN : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 1, 1, 1; 0, 1, 1, 1, 1, 1; 0, 0, 1, 1, 1, 1; 0, 0, 0, 1, 1, 1;
    0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

private def matN2 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 1, 1, 0; 1, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1;
    0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1]

private def matN4 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0; 1, 0, 1, 1, 0, 1;
    0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 1, 1]

private def matM4 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

private def matM3 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1;
    0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

private def matM2 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 1, 1, 1, 1; 0, 0, 0, 1, 1, 1;
    0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

private def matM1 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 1, 1; 0, 0, 1, 1, 1, 1; 0, 0, 0, 1, 1, 1;
    0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

private theorem comb_M4 : comb (Matrix.single 4 4 1) (Matrix.single 5 5 1) = matM4 := by decide
private theorem comb_M3 : comb (Matrix.single 3 3 1) matM4 = matM3 := by decide
private theorem comb_M2 : comb (Matrix.single 2 2 1) matM3 = matM2 := by decide
private theorem comb_M1 : comb (Matrix.single 1 1 1) matM2 = matM1 := by decide
private theorem comb_N : comb (Matrix.single 0 0 1) matM1 = matN := by decide
private theorem comb_N2 : comb matN matN = matN2 := by decide
private theorem comb_N4 : comb matN2 matN2 = matN4 := by decide
private theorem comb_N8 : comb matN4 matN4 = matN := by decide

section Main

variable {b : LinearMap.BilinForm (ZMod 2) V}

private def tv (hb : b.IsAlt) (w : V) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.transvection (f := b.flip w) (v := w)
    (hb.self_eq_zero w)

private theorem tv_apply (hb : b.IsAlt) (w x : V) : tv hb w x = x + b x w • w := rfl

private theorem symm_of_isAlt (hb : b.IsAlt) (x y : V) : b x y = b y x := by
  rw [← hb.neg_eq x y, ZMod.neg_eq_self_mod_two]

private theorem tv_mem (hb : b.IsAlt) (w : V) :
    tv hb w ∈ TauCeti.BilinForm.isometryGroup b := by
  refine TauCeti.BilinForm.mem_isometryGroup.2 (TauCeti.BilinForm.isIsometry_iff.2 fun x y => ?_)
  show b (tv hb w x) (tv hb w y) = b x y
  rw [tv_apply, tv_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hb.self_eq_zero, mul_zero, add_zero]
  rw [symm_of_isAlt hb w y]
  have h : ∀ c d : ZMod 2, d * c + c * d = 0 := by decide
  rw [add_assoc, h, add_zero]

private def chain (e f : Fin 3 → V) : Fin 6 → V := ![e 0, f 0, e 0 + e 1, f 1, e 1 + e 2, f 2]

private theorem chain_gram (hb : b.IsAlt) {e f : Fin 3 → V} (hee : ∀ i j, b (e i) (e j) = 0)
    (hff : ∀ i j, b (f i) (f j) = 0) (hef : ∀ i j, b (e i) (f j) = if i = j then 1 else 0) :
    ∀ i j, b (chain e f i) (chain e f j) = gramSix i j := by
  have hfe : ∀ i j, b (f i) (e j) = if i = j then 1 else 0 := fun i j => by
    rw [symm_of_isAlt hb, hef j i]
    exact if_congr eq_comm rfl rfl
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [chain, gramSix, hee, hff, hef, hfe]

private def tT (hb : b.IsAlt) (v : Fin 6 → V) : V ≃ₗ[ZMod 2] V :=
  tv hb (v 0) * tv hb (v 1) * tv hb (v 2) * tv hb (v 3) * tv hb (v 4) * tv hb (v 5)

private theorem tT_apply (hb : b.IsAlt) {v : Fin 6 → V}
    (hv : ∀ i j, b (v i) (v j) = gramSix i j) (x : V) : tT hb v x = phi b v matN x := by
  rw [← comb_N, ← phi_phi hv, ← comb_M1, ← phi_phi hv, ← comb_M2, ← phi_phi hv, ← comb_M3,
    ← phi_phi hv, ← comb_M4, ← phi_phi hv]
  simp only [tT, LinearEquiv.mul_apply, tv_apply, phi_single]

private theorem tT_pow_eight (hb : b.IsAlt) {v : Fin 6 → V}
    (hv : ∀ i j, b (v i) (v j) = gramSix i j) : tT hb v ^ 8 = tT hb v := by
  have h1 : ∀ x, tT hb v x = phi b v matN x := tT_apply hb hv
  have h2 : ∀ x, (tT hb v ^ 2) x = phi b v matN2 x := fun x => by
    rw [pow_two, LinearEquiv.mul_apply, h1, h1, phi_phi hv, comb_N2]
  have h4 : ∀ x, (tT hb v ^ 4) x = phi b v matN4 x := fun x => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, LinearEquiv.mul_apply, h2, h2, phi_phi hv,
      comb_N4]
  refine LinearEquiv.ext fun x => ?_
  rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, LinearEquiv.mul_apply, h4, h4, phi_phi hv, comb_N8,
    h1]

private theorem tT_ne_one (hb : b.IsAlt) {v : Fin 6 → V}
    (hv : ∀ i j, b (v i) (v j) = gramSix i j) : tT hb v ≠ 1 := by
  intro h
  have h0 : b (tT hb v (v 0)) (v 0) = b (v 0) (v 0) :=
    congrArg (fun T : V ≃ₗ[ZMod 2] V => b (T (v 0)) (v 0)) h
  rw [tT_apply hb hv] at h0
  have h1 := congrFun (ell_phi hv matN (v 0)) 0
  have hl : (fun j => b (v 0) (v j)) = fun j => gramSix 0 j := funext fun j => hv 0 j
  rw [hl] at h1
  rw [h1, hv] at h0
  revert h0
  decide

theorem exists_isometry_orderOf_seven (hb : b.IsAlt) (e f : Fin 3 → V)
    (hee : ∀ i j, b (e i) (e j) = 0) (hff : ∀ i j, b (f i) (f j) = 0)
    (hef : ∀ i j, b (e i) (f j) = if i = j then 1 else 0) :
    ∃ T : V ≃ₗ[ZMod 2] V, T ∈ TauCeti.BilinForm.isometryGroup b ∧ orderOf T = 7 ∧
      ∀ g : V →ₗ[ZMod 2] V, (∀ x y, b (g x) (g y) = b x y) → (∀ i, g (e i) = e i) →
        (∀ i, g (f i) = f i) → ∀ x, T (g x) = g (T x) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hv := chain_gram hb hee hff hef
  refine ⟨tT hb (chain e f), ?_, ?_, ?_⟩
  · have h := tv_mem (b := b) hb
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (h _) (h _)) (h _)) (h _)) (h _)) (h _)
  · refine orderOf_eq_prime ?_ (tT_ne_one hb hv)
    have h8 := tT_pow_eight hb hv
    rw [pow_succ] at h8
    exact mul_right_cancel (h8.trans (one_mul _).symm)
  · intro g hg he hf x
    have hgv : ∀ i, g (chain e f i) = chain e f i := by
      intro i
      fin_cases i <;> simp [chain, map_add, he, hf]
    rw [tT_apply hb hv, tT_apply hb hv]
    exact phi_commute hv matN g hg hgv x

end Main

end CFSG.LocalAnalysis.GLTheoremA.H1017.PureD
