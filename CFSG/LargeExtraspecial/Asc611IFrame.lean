module

public import CFSG.LargeExtraspecial.Asc611IBasic

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m} {r : ℕ}

structure IsFrame (e : SUid frob m) (q : Fin r → Fin m → K) : Prop where
  orth : ∀ i j, herm frob (q i) (invN e (q j)) = if i = j then 1 else 0
  iso : ∀ i j, herm frob (q i) (q j) = 0

@[expose] noncomputable def frameMap (e : SUid frob m) (q : Fin r → Fin m → K)
    (M : Matrix (Fin r) (Fin r) K) (x : Fin m → K) : Fin m → K :=
  ∑ l, ∑ l', (M l l' * herm frob (invN e (q l)) x) • invN e (q l')

@[expose] def ActsBy (e : SUid frob m) (q : Fin r → Fin m → K)
    (M : Matrix (Fin r) (Fin r) K) (g : SUid frob m) : Prop :=
  ∀ x, g • x = x + frameMap e q M x

theorem herm_sum_right' {ι : Type*} (s : Finset ι) (x : Fin m → K) (f : ι → Fin m → K) :
    herm frob x (∑ i ∈ s, f i) = ∑ i ∈ s, herm frob x (f i) :=
  map_sum (hermL frob x) f s

theorem herm_sum_left' {ι : Type*} (s : Finset ι) (f : ι → Fin m → K) (y : Fin m → K) :
    herm frob (∑ i ∈ s, f i) y = ∑ i ∈ s, herm frob (f i) y :=
  map_sum (AddMonoidHom.mk' (fun x => herm frob x y) (fun a b => herm_add_left frob a b y)) f s

theorem invN_sum {ι : Type*} (s : Finset ι) (f : ι → Fin m → K) :
    invN e (∑ i ∈ s, f i) = ∑ i ∈ s, invN e (f i) :=
  map_sum (AddMonoidHom.mk' (invN e) (invN_add e)) f s

variable {q : Fin r → Fin m → K}

theorem frameMap_add (M : Matrix (Fin r) (Fin r) K) (x y : Fin m → K) :
    frameMap e q M (x + y) = frameMap e q M x + frameMap e q M y := by
  simp only [frameMap, herm_add_right, mul_add, add_smul, Finset.sum_add_distrib]

theorem frameMap_add_mat (M M' : Matrix (Fin r) (Fin r) K) (x : Fin m → K) :
    frameMap e q (M + M') x = frameMap e q M x + frameMap e q M' x := by
  simp only [frameMap, Matrix.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

theorem frameMap_eq_zero_of (M : Matrix (Fin r) (Fin r) K) {x : Fin m → K}
    (hx : ∀ l, herm frob (invN e (q l)) x = 0) : frameMap e q M x = 0 := by
  simp only [frameMap, hx, mul_zero, zero_smul, Finset.sum_const_zero]

theorem herm_invN_frameMap (he : e * e = 1) (M : Matrix (Fin r) (Fin r) K) (z x : Fin m → K) :
    herm frob (invN e z) (frameMap e q M x) = 0 := by
  simp only [frameMap, herm_sum_right', herm_smul_right, herm_invN_invN he, mul_zero,
    Finset.sum_const_zero]

namespace ActsBy

variable (he : e * e = 1)
include he

theorem mul {M M' : Matrix (Fin r) (Fin r) K} {g g' : SUid frob m} (hg : ActsBy e q M g)
    (hg' : ActsBy e q M' g') : ActsBy e q (M + M') (g * g') := fun x => by
  rw [mul_smul, hg, hg', frameMap_add, frameMap_eq_zero_of M (fun l => herm_invN_frameMap he _ _ _),
    frameMap_add_mat, add_zero, add_assoc, add_comm (frameMap e q M' x)]

theorem mul_self {M : Matrix (Fin r) (Fin r) K} {g : SUid frob m} (hg : ActsBy e q M g) :
    g * g = 1 := by
  refine ext_smul _ fun x => ?_
  rw [mul_smul, hg, hg, frameMap_add,
    frameMap_eq_zero_of M (fun l => herm_invN_frameMap he _ _ _), add_zero, add_assoc,
    vec_add_self, add_zero, one_smul]

theorem inv_eq {M : Matrix (Fin r) (Fin r) K} {g : SUid frob m} (hg : ActsBy e q M g) :
    g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (hg.mul_self he)

end ActsBy

namespace IsFrame

variable (F : IsFrame e q) (he : e * e = 1)
include F he

omit he in
theorem herm_q_p (j l : Fin r) : herm frob (q j) (invN e (q l)) = if j = l then 1 else 0 :=
  F.orth j l

omit he in
theorem herm_q_sum (d : Fin r → K) (j : Fin r) :
    herm frob (q j) (∑ l, d l • invN e (q l)) = d j := by
  rw [herm_sum_right']
  simp only [herm_smul_right, F.herm_q_p, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end IsFrame

theorem ActsBy.eq_tvU (he : e * e = 1) {d : Fin r → K} {g : SUid frob m}
    (hg : ActsBy e q (fun l l' => frob (d l) * d l') g) :
    g = tvU (∑ l, d l • invN e (q l)) := by
  have hiso : herm frob (∑ l, d l • invN e (q l)) (∑ l, d l • invN e (q l)) = 0 := by
    rw [herm_sum_right']
    simp only [herm_smul_right, herm_sum_left', herm_smul_left, herm_invN_invN he, mul_zero,
      Finset.sum_const_zero]
  refine ext_smul _ fun x => ?_
  rw [hg, tvU_smul hiso]
  unfold frameMap
  rw [herm_sum_left', Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [herm_smul_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [smul_smul]
  congr 1
  ring

theorem sum_ne_zero_of_frame (F : IsFrame e q) {d : Fin r → K} (hd : d ≠ 0) :
    ∑ l, d l • invN e (q l) ≠ 0 := by
  intro h0
  apply hd
  funext j
  have := F.herm_q_sum d j
  rw [h0, herm_zero_right] at this
  exact this.symm

theorem frameMap_eq_vecMul (M : Matrix (Fin r) (Fin r) K) (x : Fin m → K) :
    frameMap e q M x =
      ∑ b, (Matrix.vecMul (fun a => herm frob (invN e (q a)) x) M) b • invN e (q b) := by
  unfold frameMap
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.vecMul, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem ActsBy.conj {c : SUid frob m} (hcc : c * c = 1) {T : Matrix (Fin r) (Fin r) K}
    (hcT : ∀ l, c • invN e (q l) = ∑ b, T l b • invN e (q b))
    {M : Matrix (Fin r) (Fin r) K} {g : SUid frob m} (hg : ActsBy e q M g) :
    ActsBy e q ((T.map frob)ᵀ * M * T) (c * g * c) := fun x => by
  have hcx : c • c • x = x := by rw [← mul_smul, hcc, one_smul]
  set X : Fin r → K := fun a => herm frob (invN e (q a)) x with hX
  have hpc : (fun l => herm frob (invN e (q l)) (c • x)) = (T.map frob) *ᵥ X := by
    funext l
    rw [← herm_smul_smul frob c, hcx, hcT, herm_sum_left', Matrix.mulVec, dotProduct]
    simp only [herm_smul_left, Matrix.map_apply, hX]
  rw [mul_smul, mul_smul, hg, smul_add, hcx]
  congr 1
  rw [frameMap_eq_vecMul, frameMap_eq_vecMul, hpc, Finset.smul_sum]
  simp only [smul_comm c, hcT, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul]
  congr 1
  change _ = (X ᵥ* ((T.map frob)ᵀ * M * T)) b
  rw [← Matrix.vecMul_vecMul X ((T.map frob)ᵀ * M) T]
  rfl

@[expose] noncomputable def tmat (c : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  fun l b => (if l = b then 1 else 0) + frob (c l) * c b

section Test

variable (he : e * e = 1) (F : IsFrame e q) (c : Fin r → K)
  (hc : ∑ i, frob (c i) * c i = 0)
include he F hc

omit he hc in
theorem iso_sum : herm frob (∑ i, c i • q i) (∑ i, c i • q i) = 0 := by
  simp only [herm_sum_left', herm_sum_right', herm_smul_left, herm_smul_right, F.iso, mul_zero,
    Finset.sum_const_zero]

omit he in
theorem isoN_sum : herm frob (∑ i, c i • q i) (invN e (∑ i, c i • q i)) = 0 := by
  rw [invN_sum, herm_sum_left']
  simp only [invN_smul, herm_smul_left, F.herm_q_sum]
  exact hc

theorem cv_smul_frame (l : Fin r) :
    cv e (∑ i, c i • q i) • invN e (q l) = ∑ b, tmat c l b • invN e (q b) := by
  rw [cv_smul_ker he (iso_sum F c) (isoN_sum F c hc) (invN_invN he _), herm_sum_left',
    invN_sum]
  simp only [herm_smul_left, F.herm_q_p, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, invN_smul, tmat, add_smul, Finset.sum_add_distrib, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.smul_sum, smul_smul]

theorem ActsBy.comm_cv {M : Matrix (Fin r) (Fin r) K} {g : SUid frob m} (hg : ActsBy e q M g) :
    ActsBy e q (M + ((tmat c).map frob)ᵀ * M * tmat c)
      (g * cv e (∑ i, c i • q i) * g⁻¹ * (cv e (∑ i, c i • q i))⁻¹) := by
  have hy := iso_sum F c
  have hyN := isoN_sum F c hc
  rw [hg.inv_eq he, cv_inv hy hyN]
  have h1 : g * cv e (∑ i, c i • q i) * g * cv e (∑ i, c i • q i) =
      g * (cv e (∑ i, c i • q i) * g * cv e (∑ i, c i • q i)) := by group
  rw [h1]
  exact hg.mul he (ActsBy.conj (cv_mul_self hy hyN) (cv_smul_frame he F c hc) hg)

end Test

end CFSG.LargeExtraspecial.Asc611I
