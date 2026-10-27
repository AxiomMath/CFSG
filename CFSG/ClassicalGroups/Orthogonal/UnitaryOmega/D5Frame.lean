module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.RankThree.PartOne.KC.OrthogonalPlanePermutations
import CFSG.Mathlib.LinearAlgebra.QuadraticForm.OrthogonalSum

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.KCOrthogonal
open _root_.QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

@[expose] noncomputable def d5Tau : K :=
  (E.isUnitary.trace_surj 1 (map_one _)).choose

theorem d5Tau_add_sigma : d5Tau E + unitaryInvolution K 2 f (d5Tau E) = 1 :=
  (E.isUnitary.trace_surj 1 (map_one _)).choose_spec

@[expose] def d5PlaneVec (i j : Fin 4) (a b : K) : Fin 4 → K :=
  Pi.single i a + Pi.single j b

@[expose] noncomputable def d5FrameVecE : Fin 5 → (F × F) × (Fin 4 → K) :=
  ![(0, d5PlaneVec 2 3 1 1), (0, d5PlaneVec 2 3 (d5Tau E) (d5Tau E)),
    (0, d5PlaneVec 0 1 (d5Tau E) (d5Tau E)), (0, d5PlaneVec 0 1 1 1), ((1, 0), 0)]

@[expose] noncomputable def d5FrameVecF : Fin 5 → (F × F) × (Fin 4 → K) :=
  ![(0, d5PlaneVec 2 3 (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)),
    (0, d5PlaneVec 2 3 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)),
    (0, d5PlaneVec 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)),
    (0, d5PlaneVec 0 1 (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)),
    ((0, 1), 0)]

private theorem d5Tau_sigma :
    unitaryInvolution K 2 f (d5Tau E) = 1 + d5Tau E := by
  have h := d5Tau_add_sigma E
  rw [← CharTwo.sub_eq_add]
  linear_combination h

private theorem d5Tau_mul_sigma :
    d5Tau E * unitaryInvolution K 2 f (d5Tau E) = d5Tau E ^ 2 + d5Tau E := by
  calc d5Tau E * unitaryInvolution K 2 f (d5Tau E)
      = d5Tau E * (1 + d5Tau E) := by rw [d5Tau_sigma E]
    _ = d5Tau E ^ 2 + d5Tau E := by ring

private theorem d5Tau_sq_add_sigma_sq :
    d5Tau E ^ 2 + (unitaryInvolution K 2 f (d5Tau E)) ^ 2 = 1 := by
  rw [← CharTwo.add_sq, d5Tau_add_sigma E]
  ring

private theorem algebraMap_Qn_d5PlaneVec (i j : Fin 4) (hij : i ≠ j) (a b : K) :
    algebraMap F K (Qn E 4 (d5PlaneVec i j a b))
      = a * unitaryInvolution K 2 f a + b * unitaryInvolution K 2 f b := by
  rw [algebraMap_Qn, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp_all [d5PlaneVec, Pi.add_apply] <;>
    ring

private theorem algebraMap_polar_Qn_d5PlaneVec_same (i j : Fin 4) (hij : i ≠ j) (a b c d : K) :
    algebraMap F K (polar (Qn E 4) (d5PlaneVec i j a b) (d5PlaneVec i j c d))
      = (a * unitaryInvolution K 2 f c + c * unitaryInvolution K 2 f a)
        + (b * unitaryInvolution K 2 f d + d * unitaryInvolution K 2 f b) := by
  rw [algebraMap_polar_Qn]
  have hT : ∑ m, d5PlaneVec i j a b m * unitaryInvolution K 2 f (d5PlaneVec i j c d m)
      = a * unitaryInvolution K 2 f c + b * unitaryInvolution K 2 f d := by
    rw [Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      simp_all [d5PlaneVec, Pi.add_apply] <;>
      ring
  rw [hT]
  simp only [map_add, map_mul, E.isUnitary.invol]
  ring

private theorem polar_Qn_d5PlaneVec_01_23 (a b c d : K) :
    polar (Qn E 4) (d5PlaneVec 0 1 a b) (d5PlaneVec 2 3 c d) = 0 := by
  apply (algebraMap F K).injective
  rw [map_zero, algebraMap_polar_Qn]
  have hT : ∑ m, d5PlaneVec 0 1 a b m * unitaryInvolution K 2 f (d5PlaneVec 2 3 c d m)
      = 0 := by
    rw [Fin.sum_univ_four]
    simp [d5PlaneVec, Pi.add_apply]
  rw [hT, map_zero, add_zero]

private theorem polar_Qn_d5PlaneVec_23_01 (a b c d : K) :
    polar (Qn E 4) (d5PlaneVec 2 3 a b) (d5PlaneVec 0 1 c d) = 0 := by
  apply (algebraMap F K).injective
  rw [map_zero, algebraMap_polar_Qn]
  have hT : ∑ m, d5PlaneVec 2 3 a b m * unitaryInvolution K 2 f (d5PlaneVec 0 1 c d m)
      = 0 := by
    rw [Fin.sum_univ_four]
    simp [d5PlaneVec, Pi.add_apply]
  rw [hT, map_zero, add_zero]

private theorem polar_Qn_d5PlaneVec_AC (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (1 : K) 1)
      (d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) = 1 := by
  apply (algebraMap F K).injective
  rw [map_one, algebraMap_polar_Qn_d5PlaneVec_same E i j hij, map_mul, E.isUnitary.invol,
    map_one, mul_one, one_mul, map_pow]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination d5Tau_sq_add_sigma_sq E
    + (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) * h2

private theorem polar_Qn_d5PlaneVec_BD (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (d5Tau E) (d5Tau E))
      (d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) = 1 := by
  apply (algebraMap F K).injective
  rw [map_one, algebraMap_polar_Qn_d5PlaneVec_same E i j hij]
  simp only [E.isUnitary.invol]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination d5Tau_sq_add_sigma_sq E
    + (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) * h2

private theorem polar_Qn_d5PlaneVec_AB (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (1 : K) 1)
      (d5PlaneVec i j (d5Tau E) (d5Tau E)) = 0 := by
  apply (algebraMap F K).injective
  rw [map_zero, algebraMap_polar_Qn_d5PlaneVec_same E i j hij]
  simp only [map_one, mul_one, one_mul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination 2 * d5Tau_add_sigma E + h2

private theorem polar_Qn_d5PlaneVec_AD (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (1 : K) 1)
      (d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) = 0 := by
  apply (algebraMap F K).injective
  rw [map_zero, algebraMap_polar_Qn_d5PlaneVec_same E i j hij]
  simp only [map_one, mul_one, one_mul, E.isUnitary.invol]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination 2 * d5Tau_add_sigma E + h2

private theorem polar_Qn_d5PlaneVec_BC (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (d5Tau E) (d5Tau E))
      (d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) = 0 := by
  apply (algebraMap F K).injective
  rw [map_zero, algebraMap_polar_Qn_d5PlaneVec_same E i j hij]
  simp only [map_mul, map_pow, E.isUnitary.invol]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination
    (d5Tau E ^ 2 * unitaryInvolution K 2 f (d5Tau E)
      + d5Tau E * (unitaryInvolution K 2 f (d5Tau E)) ^ 2) * h2

private theorem polar_Qn_d5PlaneVec_CD (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4)
      (d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2))
      (d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) = 0 := by
  apply (algebraMap F K).injective
  rw [map_zero, algebraMap_polar_Qn_d5PlaneVec_same E i j hij]
  simp only [map_mul, map_pow, E.isUnitary.invol]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination
    (d5Tau E ^ 2 * unitaryInvolution K 2 f (d5Tau E)
      + d5Tau E * (unitaryInvolution K 2 f (d5Tau E)) ^ 2) * h2

private theorem iterateFrobenius_eq_unitaryInvolution (x : K) :
    iterateFrobenius K 2 f x = unitaryInvolution K 2 f x := by
  rw [iterateFrobenius_def, CFSG.LieType.BorelTits.unitaryInvolution_apply]

private theorem polar_Qn_d5PlaneVec_AC_iter (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (1 : K) 1)
      (d5PlaneVec i j (d5Tau E * iterateFrobenius K 2 f (d5Tau E)) (d5Tau E ^ 2)) = 1 := by
  rw [iterateFrobenius_eq_unitaryInvolution]
  exact polar_Qn_d5PlaneVec_AC E i j hij

private theorem polar_Qn_d5PlaneVec_BD_iter (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (d5Tau E) (d5Tau E))
      (d5PlaneVec i j (iterateFrobenius K 2 f (d5Tau E)) (d5Tau E)) = 1 := by
  rw [iterateFrobenius_eq_unitaryInvolution]
  exact polar_Qn_d5PlaneVec_BD E i j hij

private theorem polar_Qn_d5PlaneVec_AD_iter (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (1 : K) 1)
      (d5PlaneVec i j (iterateFrobenius K 2 f (d5Tau E)) (d5Tau E)) = 0 := by
  rw [iterateFrobenius_eq_unitaryInvolution]
  exact polar_Qn_d5PlaneVec_AD E i j hij

private theorem polar_Qn_d5PlaneVec_BC_iter (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (d5Tau E) (d5Tau E))
      (d5PlaneVec i j (d5Tau E * iterateFrobenius K 2 f (d5Tau E)) (d5Tau E ^ 2)) = 0 := by
  rw [iterateFrobenius_eq_unitaryInvolution]
  exact polar_Qn_d5PlaneVec_BC E i j hij

private theorem polar_Qn_d5PlaneVec_CD_iter (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4)
      (d5PlaneVec i j (d5Tau E * iterateFrobenius K 2 f (d5Tau E)) (d5Tau E ^ 2))
      (d5PlaneVec i j (iterateFrobenius K 2 f (d5Tau E)) (d5Tau E)) = 0 := by
  rw [iterateFrobenius_eq_unitaryInvolution]
  exact polar_Qn_d5PlaneVec_CD E i j hij

private theorem polar_Qn_d5PlaneVec_BA (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4) (d5PlaneVec i j (d5Tau E) (d5Tau E))
      (d5PlaneVec i j (1 : K) 1) = 0 := by
  rw [polar_comm]
  exact polar_Qn_d5PlaneVec_AB E i j hij

private theorem polar_Qn_d5PlaneVec_DC (i j : Fin 4) (hij : i ≠ j) :
    polar (Qn E 4)
      (d5PlaneVec i j (iterateFrobenius K 2 f (d5Tau E)) (d5Tau E))
      (d5PlaneVec i j (d5Tau E * iterateFrobenius K 2 f (d5Tau E)) (d5Tau E ^ 2)) = 0 := by
  rw [polar_comm]
  exact polar_Qn_d5PlaneVec_CD_iter E i j hij

private theorem polar_d5FrameVecE_E (i j : Fin 5) (hij : i ≠ j) :
    polar (normHypForm E 4) (d5FrameVecE E i) (d5FrameVecE E j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [d5FrameVecE, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum,
      polar_Qn_d5PlaneVec_AB, polar_Qn_d5PlaneVec_BA,
      polar_Qn_d5PlaneVec_01_23, polar_Qn_d5PlaneVec_23_01]

private theorem polar_d5FrameVecF_F (i j : Fin 5) (hij : i ≠ j) :
    polar (normHypForm E 4) (d5FrameVecF E i) (d5FrameVecF E j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [d5FrameVecF, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum,
      polar_Qn_d5PlaneVec_CD_iter, polar_Qn_d5PlaneVec_DC,
      polar_Qn_d5PlaneVec_01_23, polar_Qn_d5PlaneVec_23_01]

private theorem polar_d5FrameVecE_F (i j : Fin 5) (hij : i ≠ j) :
    polar (normHypForm E 4) (d5FrameVecE E i) (d5FrameVecF E j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [d5FrameVecE, d5FrameVecF, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum,
      polar_Qn_d5PlaneVec_AD_iter, polar_Qn_d5PlaneVec_BC_iter,
      polar_Qn_d5PlaneVec_01_23, polar_Qn_d5PlaneVec_23_01]

private theorem polar_d5FrameVecF_E (i j : Fin 5) (hij : i ≠ j) :
    polar (normHypForm E 4) (d5FrameVecF E i) (d5FrameVecE E j) = 0 := by
  rw [polar_comm]
  exact polar_d5FrameVecE_F E j i hij.symm

private theorem polar_d5FrameVecE_F_self (k : Fin 5) :
    polar (normHypForm E 4) (d5FrameVecE E k) (d5FrameVecF E k) = 1 := by
  fin_cases k <;>
    simp_all [d5FrameVecE, d5FrameVecF, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum,
      polar_Qn_d5PlaneVec_AC_iter, polar_Qn_d5PlaneVec_BD_iter]

private theorem normHypForm_zero_anchor (m : ℕ) (w : Fin m → K) :
    normHypForm E m ((0 : F × F), w) = Qn E m w := by
  simp [normHypForm, CFSG.Timmesfeld.ClassicalOrders.hypSum_apply]

private theorem Qn_d5PlaneVec (i j : Fin 4) (hij : i ≠ j) (a b : K) :
    Qn E 4 (d5PlaneVec i j a b) = normQuad E a + normQuad E b := by
  apply (algebraMap F K).injective
  rw [algebraMap_Qn_d5PlaneVec E i j hij, map_add, algebraMap_normQuad, algebraMap_normQuad]

private theorem normQuad_one_add_self : normQuad E (1 : K) + normQuad E 1 = 0 := by
  have h2 : (2 : F) = 0 :=
    @CharP.cast_eq_zero F _ 2 ((algebraMap F K).charP (algebraMap F K).injective 2)
  rw [normQuad_one, ← two_mul, h2, zero_mul]

private theorem normQuad_tau_add_self :
    normQuad E (d5Tau E) + normQuad E (d5Tau E) = 0 := by
  have h2 : (2 : F) = 0 :=
    @CharP.cast_eq_zero F _ 2 ((algebraMap F K).charP (algebraMap F K).injective 2)
  rw [← two_mul, h2, zero_mul]

private theorem normQuad_sigma_tau_add_tau :
    normQuad E (unitaryInvolution K 2 f (d5Tau E)) + normQuad E (d5Tau E) = 0 := by
  apply (algebraMap F K).injective
  rw [map_add, map_zero, algebraMap_normQuad, algebraMap_normQuad]
  simp only [E.isUnitary.invol]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (unitaryInvolution K 2 f (d5Tau E) * d5Tau E) * h2

private theorem normQuad_tau_mul_sigma_add_tau_sq :
    normQuad E (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) + normQuad E (d5Tau E ^ 2) = 0 := by
  apply (algebraMap F K).injective
  rw [map_add, map_zero, algebraMap_normQuad, algebraMap_normQuad]
  simp only [map_mul, map_pow, E.isUnitary.invol]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (d5Tau E ^ 2 * (unitaryInvolution K 2 f (d5Tau E)) ^ 2) * h2

private theorem d5_E_Q (k : Fin 5) : normHypForm E 4 (d5FrameVecE E k) = 0 := by
  fin_cases k <;>
    simp [d5FrameVecE, CFSG.Timmesfeld.ClassicalOrders.hypSum_apply,
      Qn_d5PlaneVec, normQuad_one_add_self, normQuad_tau_add_self]

private theorem d5_F_Q (k : Fin 5) : normHypForm E 4 (d5FrameVecF E k) = 0 := by
  fin_cases k
  · change normHypForm E 4 ((0 : F × F), d5PlaneVec 2 3
        (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) = 0
    rw [normHypForm_zero_anchor E, Qn_d5PlaneVec E 2 3 (by decide),
      normQuad_tau_mul_sigma_add_tau_sq E]
  · change normHypForm E 4 ((0 : F × F), d5PlaneVec 2 3
        (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) = 0
    rw [normHypForm_zero_anchor E, Qn_d5PlaneVec E 2 3 (by decide),
      normQuad_sigma_tau_add_tau E]
  · change normHypForm E 4 ((0 : F × F), d5PlaneVec 0 1
        (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) = 0
    rw [normHypForm_zero_anchor E, Qn_d5PlaneVec E 0 1 (by decide),
      normQuad_sigma_tau_add_tau E]
  · change normHypForm E 4 ((0 : F × F), d5PlaneVec 0 1
        (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) = 0
    rw [normHypForm_zero_anchor E, Qn_d5PlaneVec E 0 1 (by decide),
      normQuad_tau_mul_sigma_add_tau_sq E]
  · simp [d5FrameVecF, CFSG.Timmesfeld.ClassicalOrders.hypSum_apply]
private theorem polar_d5FrameVecF_E_self (k : Fin 5) :
    polar (normHypForm E 4) (d5FrameVecF E k) (d5FrameVecE E k) = 1 := by
  rw [polar_comm]
  exact polar_d5FrameVecE_F_self E k

private noncomputable def d5HypFrame : HypFrame (normHypForm E 4) 5 where
  vec k s := if s then d5FrameVecE E k else d5FrameVecF E k
  map_vec k s := by cases s <;> simp [d5_E_Q, d5_F_Q]
  polar_vec_of_ne i j hij s t := by
    cases s <;> cases t <;>
      simp_all [polar_d5FrameVecE_E, polar_d5FrameVecF_F, polar_d5FrameVecE_F,
        polar_d5FrameVecF_E]
  polar_vec_not i s := by
    cases s <;> simp [polar_d5FrameVecE_F_self, polar_d5FrameVecF_E_self]
  exists_aux i j := by
    obtain ⟨k, hki, hkj⟩ :=
      CFSG.LieType.Universal.Spin.exists_ne_and_ne (by norm_num : 3 ≤ 5) i j
    refine ⟨d5FrameVecE E k + d5FrameVecF E k, ?_, fun s => ⟨?_, ?_⟩⟩
    · have h : normHypForm E 4 (d5FrameVecE E k + d5FrameVecF E k) = 1 := by
        rw [QuadraticMap.map_add (normHypForm E 4), d5_E_Q, d5_F_Q,
          polar_d5FrameVecE_F_self]
        simp
      rw [h]
      exact isUnit_one
    · cases s
      · rw [if_neg (by decide : ¬ ((false : Bool) = true)), polar_add_right,
          polar_d5FrameVecF_E E i k hki.symm, polar_d5FrameVecF_F E i k hki.symm]
        simp
      · rw [if_pos rfl, polar_add_right, polar_d5FrameVecE_E E i k hki.symm,
          polar_d5FrameVecE_F E i k hki.symm]
        simp
    · cases s
      · rw [if_neg (by decide : ¬ ((false : Bool) = true)), polar_add_right,
          polar_d5FrameVecF_E E j k hkj.symm, polar_d5FrameVecF_F E j k hkj.symm]
        simp
      · rw [if_pos rfl, polar_add_right, polar_d5FrameVecE_E E j k hkj.symm,
          polar_d5FrameVecE_F E j k hkj.symm]
        simp

include E in
private noncomputable def d5FrameLin :
    (Fin 5 ⊕ Fin 5 → F) →ₗ[F] (F × F) × (Fin 4 → K) :=
  ∑ a : Fin 5, ((LinearMap.proj (Sum.inl a)).smulRight ((d5HypFrame E).vec a true) +
    (LinearMap.proj (Sum.inr a)).smulRight ((d5HypFrame E).vec a false))

private theorem d5FrameLin_apply (x : Fin 5 ⊕ Fin 5 → F) :
    d5FrameLin E x = ∑ a : Fin 5,
      (x (Sum.inl a) • (d5HypFrame E).vec a true +
        x (Sum.inr a) • (d5HypFrame E).vec a false) := by
  simp [d5FrameLin, LinearMap.sum_apply]

private theorem d5FrameLin_plusVec (k : Fin 5) (s : Bool) :
    d5FrameLin E (plusVec 5 F k s) = (d5HypFrame E).vec k s := by
  rw [d5FrameLin_apply]
  cases s
  · simp only [plusVec_false]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  · simp only [plusVec_true]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp

private theorem d5FrameLin_isometry (x : Fin 5 ⊕ Fin 5 → F) :
    normHypForm E 4 (d5FrameLin E x) = quadPlus 5 F x := by
  rw [d5FrameLin_apply, quadPlus_apply]
  have h := CFSG.QuadraticMap.map_sum_of_polar_eq_zero (Q := normHypForm E 4) Finset.univ
      (fun a : Fin 5 => x (Sum.inl a) • (d5HypFrame E).vec a true +
        x (Sum.inr a) • (d5HypFrame E).vec a false)
      (fun i _ j _ hij => (d5HypFrame E).polar_smul_vec_add_smul_vec hij _ _ _ _)
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  exact (d5HypFrame E).map_smul_vec_add_smul_vec a _ _

private theorem d5FrameLin_polar (x y : Fin 5 ⊕ Fin 5 → F) :
    polar (normHypForm E 4) (d5FrameLin E x) (d5FrameLin E y) =
      polar (quadPlus 5 F) x y := by
  simp only [polar, ← map_add, d5FrameLin_isometry]

private theorem d5FrameLin_injective : Function.Injective (d5FrameLin E) := by
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  apply (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 5 F).1 (x - y)
  intro w
  rw [QuadraticMap.polarBilin_apply_apply]
  have h0 : d5FrameLin E (x - y) = 0 := by rw [map_sub, hxy]
  rw [← d5FrameLin_polar E (x - y) w, h0, QuadraticMap.polar_zero_left]

include E in
private theorem d5Frame_finrank_eq :
    Module.finrank F (Fin 5 ⊕ Fin 5 → F)
      = Module.finrank F ((F × F) × (Fin 4 → K)) := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, Module.finrank_pi_fintype]
  rw [E.finrank_eq]
  norm_num



noncomputable def d5Frame : (quadPlus 5 F).IsometryEquiv (normHypForm E 4) :=
  { toLinearEquiv := LinearEquiv.ofInjectiveOfFinrankEq (d5FrameLin E) (d5FrameLin_injective E)
      (d5Frame_finrank_eq E)
    map_app' := by
      intro v
      change normHypForm E 4 (d5FrameLin E v) = quadPlus 5 F v
      exact d5FrameLin_isometry E v }

theorem d5Frame_plusVec (k : Fin 5) (s : Bool) :
    d5Frame E (plusVec 5 F k s) = if s then d5FrameVecE E k else d5FrameVecF E k := by
  change d5FrameLin E (plusVec 5 F k s) =
    if s then d5FrameVecE E k else d5FrameVecF E k
  rw [show d5FrameLin E (plusVec 5 F k s) = (d5HypFrame E).vec k s from
    d5FrameLin_plusVec E k s]
  cases s <;> simp [d5HypFrame]

include E in
theorem two_eq_zero_of_quadExt : (2 : F) = 0 := by
  have _ := E.finrank_eq
  have _ : Finite K := inferInstance
  exact @CharP.cast_eq_zero F _ 2
    (RingHom.charP (algebraMap F K) (algebraMap F K).injective 2)

@[expose] noncomputable def d5Equiv : spinGroup (quadPlus 5 F) ≃* normOmega E 4 :=
  (commutatorEquivSpinPlusOfIsometry (d5Frame E).symm (by norm_num)
    (two_eq_zero_of_quadExt E)).symm

@[expose] noncomputable def hypPairH1 : HypPair (normHypForm E 4) where
  e := d5FrameVecE E 3
  f := d5FrameVecF E 3
  Q_e := by
    rw [show d5FrameVecE E 3 = ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) by
        simp [d5FrameVecE]]
    have hQ : normHypForm E 4 ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) =
        Qn E 4 (d5PlaneVec 0 1 (1 : K) 1) := by
      simp [normHypForm, CFSG.Timmesfeld.ClassicalOrders.hypSum_apply]
    rw [hQ]
    have hQn : Qn E 4 (d5PlaneVec 0 1 (1 : K) 1) = normQuad E 1 + normQuad E 1 := by
      rw [Qn_apply, Fin.sum_univ_four]
      simp [d5PlaneVec]
    rw [hQn, normQuad_one]
    apply (algebraMap F K).injective
    rw [map_add, map_one, map_zero]
    exact CharTwo.add_self_eq_zero (1 : K)
  Q_f := by
    rw [show d5FrameVecF E 3 =
        ((0 : F × F), d5PlaneVec 0 1
          (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) by
        simp [d5FrameVecF]]
    have hQ : normHypForm E 4 ((0 : F × F), d5PlaneVec 0 1
          (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) =
        Qn E 4 (d5PlaneVec 0 1
          (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) := by
      simp [normHypForm, CFSG.Timmesfeld.ClassicalOrders.hypSum_apply]
    rw [hQ]
    have hQn : Qn E 4 (d5PlaneVec 0 1
          (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) =
        normQuad E (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) +
          normQuad E (d5Tau E ^ 2) := by
      rw [Qn_apply, Fin.sum_univ_four]
      simp [d5PlaneVec]
    rw [hQn]
    apply (algebraMap F K).injective
    rw [map_add, map_zero, algebraMap_normQuad, algebraMap_normQuad]
    simp only [map_mul, map_pow, E.isUnitary.invol]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (d5Tau E ^ 2 * (unitaryInvolution K 2 f (d5Tau E)) ^ 2) * h2
  polar_ef := by
    rw [show d5FrameVecE E 3 = ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) by
          simp [d5FrameVecE],
        show d5FrameVecF E 3 =
          ((0 : F × F), d5PlaneVec 0 1
            (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) by
          simp [d5FrameVecF]]
    have hpol : polar (normHypForm E 4) ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1)
          ((0 : F × F), d5PlaneVec 0 1
            (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) =
        polar (Qn E 4) (d5PlaneVec 0 1 (1 : K) 1)
          (d5PlaneVec 0 1
            (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) := by
      simp [normHypForm, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum]
    rw [hpol]
    apply (algebraMap F K).injective
    rw [map_one, algebraMap_polar_Qn]
    have hp0 : ∀ a b : K, d5PlaneVec 0 1 a b 0 = a := fun a b => by simp [d5PlaneVec]
    have hp1 : ∀ a b : K, d5PlaneVec 0 1 a b 1 = b := fun a b => by simp [d5PlaneVec]
    have hp2 : ∀ a b : K, d5PlaneVec 0 1 a b 2 = 0 := fun a b => by simp [d5PlaneVec]
    have hp3 : ∀ a b : K, d5PlaneVec 0 1 a b 3 = 0 := fun a b => by simp [d5PlaneVec]
    have hsum : (∑ i, d5PlaneVec 0 1 (1 : K) 1 i *
          unitaryInvolution K 2 f
            (d5PlaneVec 0 1
              (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2) i)) =
        unitaryInvolution K 2 f (d5Tau E) * d5Tau E +
          (unitaryInvolution K 2 f (d5Tau E)) ^ 2 := by
      rw [Fin.sum_univ_four]
      simp only [hp0, hp1, hp2, hp3, one_mul, zero_mul, add_zero, map_mul,
        map_pow, E.isUnitary.invol]
    rw [hsum]
    simp only [map_add, map_mul, map_pow, E.isUnitary.invol]
    linear_combination
      (unitaryInvolution K 2 f (d5Tau E) + d5Tau E + 1) * d5Tau_add_sigma E

@[expose] noncomputable def hypPairH2 : HypPair (normHypForm E 4) where
  e := d5FrameVecE E 2
  f := d5FrameVecF E 2
  Q_e := by
    rw [show d5FrameVecE E 2 = ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) by
        simp [d5FrameVecE]]
    have hQ : normHypForm E 4 ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) =
        Qn E 4 (d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) := by
      simp [normHypForm, CFSG.Timmesfeld.ClassicalOrders.hypSum_apply]
    rw [hQ]
    have hQn : Qn E 4 (d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) =
        normQuad E (d5Tau E) + normQuad E (d5Tau E) := by
      rw [Qn_apply, Fin.sum_univ_four]
      simp [d5PlaneVec]
    rw [hQn]
    apply (algebraMap F K).injective
    rw [map_add, map_zero, algebraMap_normQuad]
    exact CharTwo.add_self_eq_zero
      (d5Tau E * unitaryInvolution K 2 f (d5Tau E))
  Q_f := by
    rw [show d5FrameVecF E 2 =
        ((0 : F × F), d5PlaneVec 0 1
          (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) by
        simp [d5FrameVecF]]
    have hQ : normHypForm E 4 ((0 : F × F), d5PlaneVec 0 1
          (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) =
        Qn E 4 (d5PlaneVec 0 1
          (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) := by
      simp [normHypForm, CFSG.Timmesfeld.ClassicalOrders.hypSum_apply]
    rw [hQ]
    have hQn : Qn E 4 (d5PlaneVec 0 1
          (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) =
        normQuad E (unitaryInvolution K 2 f (d5Tau E)) + normQuad E (d5Tau E) := by
      rw [Qn_apply, Fin.sum_univ_four]
      simp [d5PlaneVec]
    rw [hQn]
    apply (algebraMap F K).injective
    rw [map_add, map_zero, algebraMap_normQuad, algebraMap_normQuad]
    simp only [E.isUnitary.invol]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) * h2
  polar_ef := by
    rw [show d5FrameVecE E 2 = ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) by
          simp [d5FrameVecE],
        show d5FrameVecF E 2 =
          ((0 : F × F), d5PlaneVec 0 1
            (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) by
          simp [d5FrameVecF]]
    have hpol : polar (normHypForm E 4) ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E))
          ((0 : F × F), d5PlaneVec 0 1
            (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) =
        polar (Qn E 4) (d5PlaneVec 0 1 (d5Tau E) (d5Tau E))
          (d5PlaneVec 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) := by
      simp [normHypForm, CFSG.Timmesfeld.ClassicalOrders.polar_hypSum]
    rw [hpol]
    apply (algebraMap F K).injective
    rw [map_one, algebraMap_polar_Qn]
    have hp0 : ∀ a b : K, d5PlaneVec 0 1 a b 0 = a := fun a b => by simp [d5PlaneVec]
    have hp1 : ∀ a b : K, d5PlaneVec 0 1 a b 1 = b := fun a b => by simp [d5PlaneVec]
    have hp2 : ∀ a b : K, d5PlaneVec 0 1 a b 2 = 0 := fun a b => by simp [d5PlaneVec]
    have hp3 : ∀ a b : K, d5PlaneVec 0 1 a b 3 = 0 := fun a b => by simp [d5PlaneVec]
    have hsum : (∑ i, d5PlaneVec 0 1 (d5Tau E) (d5Tau E) i *
          unitaryInvolution K 2 f
            (d5PlaneVec 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E) i)) =
        d5Tau E * d5Tau E + d5Tau E * unitaryInvolution K 2 f (d5Tau E) := by
      rw [Fin.sum_univ_four]
      simp only [hp0, hp1, hp2, hp3, zero_mul, add_zero, E.isUnitary.invol]
    rw [hsum]
    simp only [map_add, map_mul, E.isUnitary.invol]
    linear_combination
      (unitaryInvolution K 2 f (d5Tau E) + d5Tau E + 1) * d5Tau_add_sigma E

@[expose] noncomputable def hypH1 : Submodule F ((F × F) × (Fin 4 → K)) :=
  Submodule.span F {(hypPairH1 E).e, (hypPairH1 E).f}

@[expose] noncomputable def hypH2 : Submodule F ((F × F) × (Fin 4 → K)) :=
  Submodule.span F {(hypPairH2 E).e, (hypPairH2 E).f}

private theorem d5_H1e_mem :
    ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) ∈ hypH1 E := by
  have he : (hypPairH1 E).e = ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) := by
    simp [hypPairH1, d5FrameVecE]
  rw [← he, hypH1]
  exact Submodule.subset_span (by left; rfl)

private theorem d5_H1f_mem :
    ((0 : F × F), d5PlaneVec 0 1
      (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) ∈ hypH1 E := by
  have hf : (hypPairH1 E).f = ((0 : F × F), d5PlaneVec 0 1
      (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) := by
    simp [hypPairH1, d5FrameVecF]
  rw [← hf, hypH1]
  exact Submodule.subset_span (by right; rfl)

private theorem d5_H2e_mem :
    ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) ∈ hypH2 E := by
  have he : (hypPairH2 E).e = ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) := by
    simp [hypPairH2, d5FrameVecE]
  rw [← he, hypH2]
  exact Submodule.subset_span (by left; rfl)

private theorem d5_H2f_mem :
    ((0 : F × F), d5PlaneVec 0 1
      (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) ∈ hypH2 E := by
  have hf : (hypPairH2 E).f = ((0 : F × F), d5PlaneVec 0 1
      (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) := by
    simp [hypPairH2, d5FrameVecF]
  rw [← hf, hypH2]
  exact Submodule.subset_span (by right; rfl)

private theorem d5_sigma_tau :
    unitaryInvolution K 2 f (d5Tau E) = 1 + d5Tau E := by
  have h1 : unitaryInvolution K 2 f (d5Tau E) = 1 - d5Tau E := by
    linear_combination d5Tau_add_sigma E
  rw [h1, CharTwo.sub_eq_add]

private theorem d5_tau_mul_sigma_tau :
    d5Tau E * unitaryInvolution K 2 f (d5Tau E) = d5Tau E + d5Tau E ^ 2 := by
  rw [d5_sigma_tau E]
  ring

private theorem d5Tau_add_iterate :
    d5Tau E + iterateFrobenius K 2 f (d5Tau E) = 1 :=
  d5Tau_add_sigma E

private theorem d5_tau_mul_iterate :
    d5Tau E * iterateFrobenius K 2 f (d5Tau E) = d5Tau E + d5Tau E ^ 2 :=
  d5_tau_mul_sigma_tau E

private theorem d5_add_smul_tau_fixed (x : K) (b : F)
    (hb : algebraMap F K b = x + unitaryInvolution K 2 f x) :
    unitaryInvolution K 2 f (x + algebraMap F K b * d5Tau E) =
      x + algebraMap F K b * d5Tau E := by
  rw [map_add, map_mul, E.fix, d5_sigma_tau E]
  have hbx : unitaryInvolution K 2 f x = x + algebraMap F K b := by
    rw [hb, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [hbx, mul_add, mul_one, add_assoc,
    ← add_assoc (algebraMap F K b) (algebraMap F K b) (algebraMap F K b * d5Tau E),
    CharTwo.add_self_eq_zero, zero_add]

private theorem d5_exists_decomp (x : K) :
    ∃ a b : F, x = algebraMap F K a + algebraMap F K b * d5Tau E := by
  obtain ⟨b, hb⟩ := CFSG.ClassicalInvolution.PhanDn.exists_trace_eq E x
  obtain ⟨a, ha⟩ := E.exists_of_fix (x + algebraMap F K b * d5Tau E)
    (d5_add_smul_tau_fixed E x b hb)
  exact ⟨a, b, by rw [ha, add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩

private theorem d5_single_0_one_eq :
    ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) +
        ((0 : F × F), d5PlaneVec 0 1
          (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) =
      ((0 : F × F), Pi.single 0 (1 : K)) := by
  apply Prod.ext
  · simp
  · funext k
    fin_cases k
    · simpa [d5PlaneVec] using d5Tau_add_iterate E
    · simpa [d5PlaneVec] using CharTwo.add_self_eq_zero (d5Tau E)
    · simp [d5PlaneVec]
    · simp [d5PlaneVec]

private theorem d5_single_1_one_eq :
    ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) +
        ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) +
        ((0 : F × F), d5PlaneVec 0 1
          (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) =
      ((0 : F × F), Pi.single 1 (1 : K)) := by
  apply Prod.ext
  · simp
  · funext k
    fin_cases k
    · simp [d5PlaneVec]
      linear_combination d5Tau_add_iterate E +
        (CharTwo.two_eq_zero : (2 : K) = 0)
    · simp [d5PlaneVec]
      linear_combination (d5Tau E) * (CharTwo.two_eq_zero : (2 : K) = 0)
    · simp [d5PlaneVec]
    · simp [d5PlaneVec]

private theorem d5_single_0_tau_eq (n : F)
    (hn : algebraMap F K n = d5Tau E * unitaryInvolution K 2 f (d5Tau E)) :
    ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) +
        ((0 : F × F), d5PlaneVec 0 1
          (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) +
        n • ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) =
      ((0 : F × F), Pi.single 0 (d5Tau E)) := by
  apply Prod.ext
  · simp
  · funext k
    fin_cases k
    · simp [d5PlaneVec, hn, d5_tau_mul_iterate E, Algebra.smul_def]
      linear_combination (d5Tau E + d5Tau E ^ 2) *
        (CharTwo.two_eq_zero : (2 : K) = 0)
    · simp [d5PlaneVec, hn, d5_tau_mul_iterate E, Algebra.smul_def]
      linear_combination (d5Tau E + d5Tau E ^ 2) *
        (CharTwo.two_eq_zero : (2 : K) = 0)
    · simp [d5PlaneVec]
    · simp [d5PlaneVec]

private theorem d5_single_1_tau_eq (n : F)
    (hn : algebraMap F K n = d5Tau E * unitaryInvolution K 2 f (d5Tau E)) :
    ((0 : F × F), d5PlaneVec 0 1
        (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) +
        n • ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) =
      ((0 : F × F), Pi.single 1 (d5Tau E)) := by
  apply Prod.ext
  · simp
  · funext k
    fin_cases k
    · simp [d5PlaneVec, hn, d5_tau_mul_iterate E, Algebra.smul_def]
      linear_combination (d5Tau E + d5Tau E ^ 2) *
        (CharTwo.two_eq_zero : (2 : K) = 0)
    · simp [d5PlaneVec, hn, d5_tau_mul_iterate E, Algebra.smul_def]
      linear_combination (d5Tau E ^ 2) * (CharTwo.two_eq_zero : (2 : K) = 0)
    · simp [d5PlaneVec]
    · simp [d5PlaneVec]

private theorem d5_single_0_one_mem :
    ((0 : F × F), Pi.single 0 (1 : K)) ∈ hypH1 E ⊔ hypH2 E := by
  rw [← d5_single_0_one_eq E]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right (d5_H2e_mem E))
    (Submodule.mem_sup_right (d5_H2f_mem E))

private theorem d5_single_0_tau_mem :
    ((0 : F × F), Pi.single 0 (d5Tau E)) ∈ hypH1 E ⊔ hypH2 E := by
  obtain ⟨n, hn⟩ := E.exists_of_fix (d5Tau E * unitaryInvolution K 2 f (d5Tau E))
    (by rw [map_mul, E.isUnitary.invol, mul_comm])
  rw [← d5_single_0_tau_eq E n hn]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.mem_sup_right (d5_H2e_mem E))
      (Submodule.mem_sup_left (d5_H1f_mem E)))
    (Submodule.smul_mem _ n (Submodule.mem_sup_left (d5_H1e_mem E)))

private theorem d5_single_1_one_mem :
    ((0 : F × F), Pi.single 1 (1 : K)) ∈ hypH1 E ⊔ hypH2 E := by
  rw [← d5_single_1_one_eq E]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.mem_sup_left (d5_H1e_mem E))
      (Submodule.mem_sup_right (d5_H2e_mem E)))
    (Submodule.mem_sup_right (d5_H2f_mem E))

private theorem d5_single_1_tau_mem :
    ((0 : F × F), Pi.single 1 (d5Tau E)) ∈ hypH1 E ⊔ hypH2 E := by
  obtain ⟨n, hn⟩ := E.exists_of_fix (d5Tau E * unitaryInvolution K 2 f (d5Tau E))
    (by rw [map_mul, E.isUnitary.invol, mul_comm])
  rw [← d5_single_1_tau_eq E n hn]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (d5_H1f_mem E))
    (Submodule.smul_mem _ n (Submodule.mem_sup_left (d5_H1e_mem E)))

omit [Finite K] [CharP K 2] in
private theorem d5PlaneVec_mem_coord_sup (a b : K) :
    ((0 : F × F), d5PlaneVec 0 1 a b) ∈
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 := by
  rw [Submodule.mem_sup]
  refine ⟨((0 : F × F), Pi.single 0 a), ?_, ((0 : F × F), Pi.single 1 b), ?_, ?_⟩
  · rw [mem_coordPlane]; exact ⟨a, rfl⟩
  · rw [mem_coordPlane]; exact ⟨b, rfl⟩
  · rw [d5PlaneVec]
    simp

theorem hypH1_sup_hypH2 :
    hypH1 E ⊔ hypH2 E =
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 := by
  apply le_antisymm
  · apply sup_le
    · rw [hypH1]
      apply Submodule.span_le.mpr
      intro v hv
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · have he : (hypPairH1 E).e = ((0 : F × F), d5PlaneVec 0 1 (1 : K) 1) := by
          simp [hypPairH1, d5FrameVecE]
        rw [he]
        exact d5PlaneVec_mem_coord_sup (1 : K) 1
      · have hf : (hypPairH1 E).f = ((0 : F × F), d5PlaneVec 0 1
            (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) := by
          simp [hypPairH1, d5FrameVecF]
        rw [hf]
        exact d5PlaneVec_mem_coord_sup _ _
    · rw [hypH2]
      apply Submodule.span_le.mpr
      intro v hv
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · have he : (hypPairH2 E).e =
            ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) := by
          simp [hypPairH2, d5FrameVecE]
        rw [he]
        exact d5PlaneVec_mem_coord_sup _ _
      · have hf : (hypPairH2 E).f = ((0 : F × F), d5PlaneVec 0 1
            (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) := by
          simp [hypPairH2, d5FrameVecF]
        rw [hf]
        exact d5PlaneVec_mem_coord_sup _ _
  · apply sup_le
    · intro v hv
      rw [mem_coordPlane] at hv
      obtain ⟨x, rfl⟩ := hv
      show ((0 : F × F), Pi.single 0 x) ∈ hypH1 E ⊔ hypH2 E
      obtain ⟨a, b, rfl⟩ := d5_exists_decomp E x
      rw [Pi.single_add]
      have hvec : (((0 : F × F),
            Pi.single (0 : Fin 4) (algebraMap F K a) +
              Pi.single (0 : Fin 4) (algebraMap F K b * d5Tau E)) :
            (F × F) × (Fin 4 → K)) =
          a • ((0 : F × F), Pi.single (0 : Fin 4) (1 : K)) +
            b • ((0 : F × F), Pi.single (0 : Fin 4) (d5Tau E)) := by
        apply Prod.ext
        · simp
        · funext k
          fin_cases k <;> simp [Algebra.smul_def]
      rw [hvec]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ a (d5_single_0_one_mem E))
        (Submodule.smul_mem _ b (d5_single_0_tau_mem E))
    · intro v hv
      rw [mem_coordPlane] at hv
      obtain ⟨x, rfl⟩ := hv
      show ((0 : F × F), Pi.single 1 x) ∈ hypH1 E ⊔ hypH2 E
      obtain ⟨a, b, rfl⟩ := d5_exists_decomp E x
      rw [Pi.single_add]
      have hvec : (((0 : F × F),
            Pi.single (1 : Fin 4) (algebraMap F K a) +
              Pi.single (1 : Fin 4) (algebraMap F K b * d5Tau E)) :
            (F × F) × (Fin 4 → K)) =
          a • ((0 : F × F), Pi.single (1 : Fin 4) (1 : K)) +
            b • ((0 : F × F), Pi.single (1 : Fin 4) (d5Tau E)) := by
        apply Prod.ext
        · simp
        · funext k
          fin_cases k <;> simp [Algebra.smul_def]
      rw [hvec]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ a (d5_single_1_one_mem E))
        (Submodule.smul_mem _ b (d5_single_1_tau_mem E))

@[expose] noncomputable def crossAnchor : Submodule F ((F × F) × (Fin 4 → K)) :=
  coordAnchor (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) ⊔ hypH1 E

@[expose] noncomputable def crossPure : Submodule F ((F × F) × (Fin 4 → K)) :=
  hypH2 E ⊔ (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
    coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
