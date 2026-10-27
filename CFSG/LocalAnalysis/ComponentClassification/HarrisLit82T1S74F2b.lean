module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F2Card
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Rad

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

abbrev VEnd (K : Type) [Field K] : Type :=
  (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)

theorem spinAction_qOne : spinAction (quadOdd 3 K) (qOne K) =
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) := by
  rw [qOne, HypFrame.longSL2_upperSL2, HypFrame.spinAction_longRoot_eq_eichler, one_smul]
  rfl

theorem commute_radU_eichler {u : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hu : u ∈ radU K) :
    u * eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) =
      eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) * u := by
  have hO : u ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hu.1
  have h := eichler_conj hO (oddVec 3 K 1 true) (oddVec 3 K 0 true)
  rw [hu.2.2.1, hu.2.1] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem spinAction_spinZ (h2 : (2 : K) ≠ 0) : spinAction (quadOdd 3 K) (spinZ K) = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  exact MonoidHom.mem_ker.mp ((mem_ker_spinAction_iff (quadOdd 3 K) (nondegenerate_quadOdd 3 K)
    _).mpr (Or.inr rfl))

theorem lift_mem_centralizer (h2 : (2 : K) ≠ 0) {x : spinGroup (quadOdd 3 K)}
    (hx : Odd (orderOf x)) (hu : spinAction (quadOdd 3 K) x ∈ radU K) :
    x ∈ centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K))) := by
  rw [mem_centralizer_singleton_iff]
  refine (mul_comm_of_spinAction h2 hx ?_).symm
  rw [spinAction_qOne]
  exact (commute_radU_eichler hu).symm

noncomputable abbrev frameJThree (K : Type) [Field K] : Frame (quadOdd 3 K) :=
  (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false

theorem spinAction_JThree_apply (B : SL(2, K)) :
    spinAction (quadOdd 3 K) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B)
        (oddVec 3 K 0 true) =
      (B : Matrix (Fin 2) (Fin 2) K) 0 0 • oddVec 3 K 0 true +
        (B : Matrix (Fin 2) (Fin 2) K) 1 0 • oddVec 3 K 1 true ∧
    spinAction (quadOdd 3 K) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B)
        (oddVec 3 K 1 true) =
      (B : Matrix (Fin 2) (Fin 2) K) 0 1 • oddVec 3 K 0 true +
        (B : Matrix (Fin 2) (Fin 2) K) 1 1 • oddVec 3 K 1 true := by
  rw [spinAction_longSL2]
  have he0 : oddVec 3 K 0 true = (frameJThree K).incl !![1, 0; 0, 0] :=
    CFSG.ClassicalInvolution.ModelFacts.Frame.e₁_eq_incl (frameJThree K)
  have he1 : oddVec 3 K 1 true = (frameJThree K).incl !![0, 0; 1, 0] :=
    CFSG.ClassicalInvolution.ModelFacts.Frame.f₂_eq_incl (frameJThree K)
  have hv : (frameJThree K).e₁ = oddVec 3 K 0 true ∧ (frameJThree K).f₂ = oddVec 3 K 1 true :=
    ⟨rfl, rfl⟩
  have m0 : (B : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, 0] =
      !![(B : Matrix (Fin 2) (Fin 2) K) 0 0, 0; (B : Matrix (Fin 2) (Fin 2) K) 1 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have m1 : (B : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 1, 0] =
      !![(B : Matrix (Fin 2) (Fin 2) K) 0 1, 0; (B : Matrix (Fin 2) (Fin 2) K) 1 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · conv_lhs => rw [he0, Frame.La_apply_incl, m0, Frame.incl_apply, hv.1, hv.2]
    simp
  · conv_lhs => rw [he1, Frame.La_apply_incl, m1, Frame.incl_apply, hv.1, hv.2]
    simp

theorem JThree_eq_of_apply_eq {B B' : SL(2, K)}
    (h0 : spinAction (quadOdd 3 K)
        ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B) (oddVec 3 K 0 true) =
      spinAction (quadOdd 3 K)
        ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B') (oddVec 3 K 0 true))
    (h1 : spinAction (quadOdd 3 K)
        ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B) (oddVec 3 K 1 true) =
      spinAction (quadOdd 3 K)
        ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B') (oddVec 3 K 1 true)) :
    B = B' := by
  rw [(spinAction_JThree_apply B).1, (spinAction_JThree_apply B').1] at h0
  rw [(spinAction_JThree_apply B).2, (spinAction_JThree_apply B').2] at h1
  have a := congrFun h0 (.inl 0)
  have b := congrFun h0 (.inl 1)
  have c := congrFun h1 (.inl 0)
  have d := congrFun h1 (.inl 1)
  simp at a b c d
  ext i j
  fin_cases i <;> fin_cases j
  · exact a
  · exact c
  · exact b
  · exact d

theorem JThree_mem_centralizer [Finite K] (h4 : 4 ≤ Nat.card K) (B : SL(2, K)) :
    (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B ∈
      centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K))) :=
  mem_centralizer_singleton_iff.mpr
    (commute_spinJ₂_spinJ₃ h4 ⟨upperSL2 1, rfl⟩ ⟨B, rfl⟩).symm

@[expose] noncomputable def fixW (K : Type) [Field K] : Subgroup (spinGroup (quadOdd 3 K)) where
  carrier := {g | ∀ (i : Fin 3) (s : Bool), i ≠ 2 →
    spinAction (quadOdd 3 K) g (oddVec 3 K i s) = oddVec 3 K i s}
  mul_mem' := by
    intro a b ha hb i s hi
    rw [map_mul, LinearEquiv.mul_apply, hb i s hi, ha i s hi]
  one_mem' := fun i s _ => by rw [map_one]; rfl
  inv_mem' := by
    intro a ha i s hi
    rw [map_inv]
    exact (LinearEquiv.symm_apply_eq _).mpr (ha i s hi).symm

theorem mem_fixW {g : spinGroup (quadOdd 3 K)} :
    g ∈ fixW K ↔ ∀ (i : Fin 3) (s : Bool), i ≠ 2 →
      spinAction (quadOdd 3 K) g (oddVec 3 K i s) = oddVec 3 K i s :=
  Iff.rfl

theorem shortSeven_mem_fixW (A : SL(2, K)) : shortSeven K A ∈ fixW K := by
  have hfix : ∀ (s : Bool) (c : K), (oddFrame 3 K).shortRoot 2 s (.ofAdd c) ∈ fixW K := by
    intro s c i r hi
    rw [OddFrame.spinAction_shortRoot_eq_eichler]
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [oddFrame_vec, polar_quadOdd_oddVec, ite_eq_right_iff]
      exact fun h => absurd h.1 hi
    · rw [polar_smul_right, oddFrame_z, polar_quadOdd_oddVec_oddZ, smul_zero]
  refine Frame.sl2_apply_mem (shortSeven K) (fixW K) (fun c => ?_) (fun c => ?_) A
  · rw [← CFSG.ClassicalInvolution.ModelFacts.coe_upperSL2_eq_transvection,
      OddFrame.shortSL2_upperSL2]
    exact hfix true c
  · rw [← CFSG.ClassicalInvolution.ModelFacts.coe_lowerSL2_eq_transvection,
      OddFrame.shortSL2_lowerSL2]
    exact hfix _ _

theorem shortSeven_mem_centralizer (A : SL(2, K)) :
    shortSeven K A ∈ centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K))) :=
  mem_centralizer_singleton_iff.mpr (commute_spinJ₁_spinJ₂ ⟨A, rfl⟩ ⟨upperSL2 1, rfl⟩)

theorem eq_one_of_mem_radU_of_mem_fixW {g : spinGroup (quadOdd 3 K)} (hg : g ∈ fixW K)
    (hu : spinAction (quadOdd 3 K) g ∈ radU K) : spinAction (quadOdd 3 K) g = 1 :=
  eq_one_of_mem_radU hu (hg 0 false (by decide)) (hg 1 false (by decide))

variable [Finite K]

theorem exists_odd_lift (hodd : Odd (Nat.card K))
    {u : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)} (hu : u ∈ radU K) :
    ∃ x : spinGroup (quadOdd 3 K), spinAction (quadOdd 3 K) x = u ∧ Odd (orderOf x) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hrange : u ∈ (spinAction (quadOdd 3 K)).range := by
    rw [range_spinAction_quadOdd h2 (le_refl 3), ← uMap_pairCoords hu]
    exact mul_mem (eichler_mem_elementaryGroup _ _ _) (eichler_mem_elementaryGroup _ _ _)
  obtain ⟨y, rfl⟩ := hrange
  have hm : Odd (orderOf (spinAction (quadOdd 3 K) y)) :=
    (hodd.pow (n := 7)).of_dvd_nat (by rw [← card_radU]; exact (radU K).orderOf_dvd_natCard hu)
  have hym : spinAction (quadOdd 3 K) (y ^ orderOf (spinAction (quadOdd 3 K) y)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  rcases eq_one_or_eq_spinZ h2 hym with h | h
  · exact ⟨y, rfl, hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h)⟩
  · refine ⟨spinZ K * y, by rw [map_mul, spinAction_spinZ h2, one_mul],
      hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)⟩
    rw [Commute.mul_pow (spinZ_commute y), h, ← pow_succ]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [orderOf_spinZ h2]; exact hm.add_one.two_dvd)

theorem f2b_holds : F2b := by
  intro K _ _ hodd h5
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Finite (spinGroup (quadOdd 3 K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  choose lift hlift using fun u : radU K => exists_odd_lift hodd u.2
  let Φ : radU K × SL(2, K) × SL(2, K) →
      centralizer ({qOne K} : Set (spinGroup (quadOdd 3 K))) := fun p =>
    ⟨lift p.1 * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false p.2.1 *
      shortSeven K p.2.2, mul_mem (mul_mem (lift_mem_centralizer h2 (hlift p.1).2
        ((hlift p.1).1 ▸ p.1.2)) (JThree_mem_centralizer (by omega) _))
          (shortSeven_mem_centralizer _)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨u, B, A⟩ ⟨u', B', A'⟩ h
    have h' := congrArg Subtype.val h
    simp only [Φ] at h'
    have hπ := congrArg (spinAction (quadOdd 3 K)) h'
    simp only [map_mul, (hlift u).1, (hlift u').1] at hπ
    have hL0 : ∀ (v : radU K) (C D : SL(2, K)),
        ((v : VEnd K) * spinAction (quadOdd 3 K)
          ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C) *
          spinAction (quadOdd 3 K) (shortSeven K D)) (oddVec 3 K 0 true) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C)
          (oddVec 3 K 0 true) := by
      intro v C D
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, shortSeven_mem_fixW D 0 true (by decide),
        (spinAction_JThree_apply C).1, apply_planeL_of_mem_radU v.2]
    have hL1 : ∀ (v : radU K) (C D : SL(2, K)),
        ((v : VEnd K) * spinAction (quadOdd 3 K)
          ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C) *
          spinAction (quadOdd 3 K) (shortSeven K D)) (oddVec 3 K 1 true) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false C)
          (oddVec 3 K 1 true) := by
      intro v C D
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, shortSeven_mem_fixW D 1 true (by decide),
        (spinAction_JThree_apply C).2, apply_planeL_of_mem_radU v.2]
    have hB : B = B' := JThree_eq_of_apply_eq
      (by rw [← hL0 u B A, ← hL0 u' B' A', hπ])
      (by rw [← hL1 u B A, ← hL1 u' B' A', hπ])
    subst hB
    have hc : ∀ D : SL(2, K), (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B *
        shortSeven K D = shortSeven K D *
          (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B := fun D =>
      (commute_spinJ₁_spinJ₃ ⟨D, rfl⟩ ⟨B, rfl⟩).symm
    rw [mul_assoc, mul_assoc, hc A, hc A', ← mul_assoc, ← mul_assoc] at h'
    have h'' := mul_right_cancel h'
    have hu : u = u' := by
      have hv : (u' : VEnd K)⁻¹ * (u : VEnd K) =
          spinAction (quadOdd 3 K) (shortSeven K A' * (shortSeven K A)⁻¹) := by
        have := congrArg (spinAction (quadOdd 3 K)) h''
        simp only [map_mul, (hlift u).1, (hlift u').1] at this
        rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← this, mul_inv_cancel_right]
      have h1 := eq_one_of_mem_radU_of_mem_fixW (g := shortSeven K A' * (shortSeven K A)⁻¹)
        (mul_mem (shortSeven_mem_fixW _) (inv_mem (shortSeven_mem_fixW _)))
        (hv ▸ mul_mem (inv_mem u'.2) u.2)
      rw [← hv, inv_mul_eq_one] at h1
      exact Subtype.ext h1.symm
    subst hu
    have hA : A = A' := LieType.Steinberg.SpinOdd.shortSL2_injective (oddFrame 3 K) 2 true
      (mul_left_cancel h'')
    subst hA
    rfl
  have hcard : Nat.card (radU K × SL(2, K) × SL(2, K)) =
      Nat.card K ^ 9 * (Nat.card K ^ 2 - 1) ^ 2 := by
    rw [Nat.card_prod, Nat.card_prod, card_radU,
      LieType.Steinberg.card_specialLinearGroup_fin_two]
    ring
  rw [← hcard]
  exact Nat.card_le_card_of_injective Φ hΦ

end CFSG.ComponentClassification.HarrisLit.T1.S74
