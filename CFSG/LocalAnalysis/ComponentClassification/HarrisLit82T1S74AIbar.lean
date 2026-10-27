module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74AInv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RE

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable (K : Type) [Field K]

abbrev vecMinus₀ : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  (oddFrame 3 K).vec 0 true - (oddFrame 3 K).vec 0 false

abbrev vecPlus₂ : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  (oddFrame 3 K).vec 2 true + (oddFrame 3 K).vec 2 false

abbrev vecMinus₂ : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  (oddFrame 3 K).vec 2 true - (oddFrame 3 K).vec 2 false

theorem quadOdd_vecMinus₀ : quadOdd 3 K (vecMinus₀ K) = -1 := by
  have hp : polar (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) ((oddFrame 3 K).vec 0 false) = 1 :=
    (oddFrame 3 K).polar_vec_not 0 true
  rw [vecMinus₀, sub_eq_add_neg, QuadraticMap.map_add (quadOdd 3 K), QuadraticMap.map_neg,
    (oddFrame 3 K).map_vec, (oddFrame 3 K).map_vec, polar_neg_right, hp]
  ring

theorem quadOdd_vecPlus₂ : quadOdd 3 K (vecPlus₂ K) = 1 := by
  have hp : polar (quadOdd 3 K) ((oddFrame 3 K).vec 2 true) ((oddFrame 3 K).vec 2 false) = 1 :=
    (oddFrame 3 K).polar_vec_not 2 true
  rw [vecPlus₂, QuadraticMap.map_add (quadOdd 3 K), (oddFrame 3 K).map_vec,
    (oddFrame 3 K).map_vec, hp]
  ring

theorem quadOdd_vecMinus₂ : quadOdd 3 K (vecMinus₂ K) = -1 := by
  have hp : polar (quadOdd 3 K) ((oddFrame 3 K).vec 2 true) ((oddFrame 3 K).vec 2 false) = 1 :=
    (oddFrame 3 K).polar_vec_not 2 true
  rw [vecMinus₂, sub_eq_add_neg, QuadraticMap.map_add (quadOdd 3 K), QuadraticMap.map_neg,
    (oddFrame 3 K).map_vec, (oddFrame 3 K).map_vec, polar_neg_right, hp]
  ring

theorem polar_vecMinus₀_vec {k : Fin 3} (hk : k ≠ 0) (s : Bool) :
    polar (quadOdd 3 K) (vecMinus₀ K) ((oddFrame 3 K).vec k s) = 0 := by
  rw [vecMinus₀, polar_sub_left, (oddFrame 3 K).polar_vec_of_ne (Ne.symm hk),
    (oddFrame 3 K).polar_vec_of_ne (Ne.symm hk), sub_zero]

theorem polar_vecMinus₀_z : polar (quadOdd 3 K) (vecMinus₀ K) (oddFrame 3 K).z = 0 := by
  rw [vecMinus₀, polar_sub_left, (oddFrame 3 K).polar_vec_z, (oddFrame 3 K).polar_vec_z,
    sub_zero]

theorem polar_vecPlus₂_vec {k : Fin 3} (hk : k ≠ 2) (s : Bool) :
    polar (quadOdd 3 K) (vecPlus₂ K) ((oddFrame 3 K).vec k s) = 0 := by
  rw [vecPlus₂, polar_add_left, (oddFrame 3 K).polar_vec_of_ne (Ne.symm hk),
    (oddFrame 3 K).polar_vec_of_ne (Ne.symm hk), add_zero]

theorem polar_vecMinus₂_vec {k : Fin 3} (hk : k ≠ 2) (s : Bool) :
    polar (quadOdd 3 K) (vecMinus₂ K) ((oddFrame 3 K).vec k s) = 0 := by
  rw [vecMinus₂, polar_sub_left, (oddFrame 3 K).polar_vec_of_ne (Ne.symm hk),
    (oddFrame 3 K).polar_vec_of_ne (Ne.symm hk), sub_zero]

theorem polar_vecPlus₂_z : polar (quadOdd 3 K) (vecPlus₂ K) (oddFrame 3 K).z = 0 := by
  rw [vecPlus₂, polar_add_left, (oddFrame 3 K).polar_vec_z, (oddFrame 3 K).polar_vec_z,
    add_zero]

theorem polar_vecMinus₂_z : polar (quadOdd 3 K) (vecMinus₂ K) (oddFrame 3 K).z = 0 := by
  rw [vecMinus₂, polar_sub_left, (oddFrame 3 K).polar_vec_z, (oddFrame 3 K).polar_vec_z,
    sub_zero]

theorem polar_vecPlus₂_vecMinus₂ : polar (quadOdd 3 K) (vecPlus₂ K) (vecMinus₂ K) = 0 := by
  have h1 : polar (quadOdd 3 K) ((oddFrame 3 K).vec 2 true) ((oddFrame 3 K).vec 2 false) = 1 :=
    (oddFrame 3 K).polar_vec_not 2 true
  have h2 : polar (quadOdd 3 K) ((oddFrame 3 K).vec 2 false) ((oddFrame 3 K).vec 2 true) = 1 :=
    (oddFrame 3 K).polar_vec_not 2 false
  rw [vecPlus₂, vecMinus₂, polar_add_left, polar_sub_right, polar_sub_right,
    HypFrame.polar_vec_self, HypFrame.polar_vec_self, h1, h2]
  ring

theorem polar_vecMinus₀_vecPlus₂ : polar (quadOdd 3 K) (vecMinus₀ K) (vecPlus₂ K) = 0 := by
  rw [vecPlus₂, polar_add_right, polar_vecMinus₀_vec K (by decide), polar_vecMinus₀_vec K
    (by decide), add_zero]

theorem polar_vecMinus₀_vecMinus₂ : polar (quadOdd 3 K) (vecMinus₀ K) (vecMinus₂ K) = 0 := by
  rw [vecMinus₂, polar_sub_right, polar_vecMinus₀_vec K (by decide), polar_vecMinus₀_vec K
    (by decide), sub_zero]

theorem ι_vec_two_true (h2 : (2 : K) ≠ 0) :
    ι (quadOdd 3 K) ((oddFrame 3 K).vec 2 true) =
      (2⁻¹ : K) • (ι (quadOdd 3 K) (vecPlus₂ K) + ι (quadOdd 3 K) (vecMinus₂ K)) := by
  have hv : (oddFrame 3 K).vec 2 true = (2⁻¹ : K) • (vecPlus₂ K + vecMinus₂ K) := by
    rw [vecPlus₂, vecMinus₂, show (oddFrame 3 K).vec 2 true + (oddFrame 3 K).vec 2 false +
      ((oddFrame 3 K).vec 2 true - (oddFrame 3 K).vec 2 false) =
        (2 : K) • (oddFrame 3 K).vec 2 true by module, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hv, map_smul, map_add]

theorem ι_vec_two_false (h2 : (2 : K) ≠ 0) :
    ι (quadOdd 3 K) ((oddFrame 3 K).vec 2 false) =
      (2⁻¹ : K) • (ι (quadOdd 3 K) (vecPlus₂ K) - ι (quadOdd 3 K) (vecMinus₂ K)) := by
  have hv : (oddFrame 3 K).vec 2 false = (2⁻¹ : K) • (vecPlus₂ K - vecMinus₂ K) := by
    rw [vecPlus₂, vecMinus₂, show (oddFrame 3 K).vec 2 true + (oddFrame 3 K).vec 2 false -
      ((oddFrame 3 K).vec 2 true - (oddFrame 3 K).vec 2 false) =
        (2 : K) • (oddFrame 3 K).vec 2 false by module, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hv, map_smul, map_sub]

theorem ι_vecMinus₀ : ι (quadOdd 3 K) (vecMinus₀ K) =
    ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) -
      ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 false) := by
  rw [vecMinus₀, map_sub]

theorem ι_vecMinus₀_mul_e₀ :
    ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) =
      -(ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 false) * ι (quadOdd 3 K) (vecMinus₀ K)) := by
  have h0 := ι_mul_ι_self_eq_zero (quadOdd 3 K) ((oddFrame 3 K).map_vec 0 true)
  have h0' := ι_mul_ι_self_eq_zero (quadOdd 3 K) ((oddFrame 3 K).map_vec 0 false)
  rw [ι_vecMinus₀, sub_mul, mul_sub, h0, h0', zero_sub, sub_zero]

theorem ι_vecMinus₀_mul_f₀ :
    ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 false) =
      -(ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) * ι (quadOdd 3 K) (vecMinus₀ K)) := by
  have h0 := ι_mul_ι_self_eq_zero (quadOdd 3 K) ((oddFrame 3 K).map_vec 0 true)
  have h0' := ι_mul_ι_self_eq_zero (quadOdd 3 K) ((oddFrame 3 K).map_vec 0 false)
  rw [ι_vecMinus₀, sub_mul, mul_sub, h0, h0', sub_zero, zero_sub, neg_neg]

theorem ι_vecMinus₀_mul_vec_one (s : Bool) :
    ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 s) =
      -(ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 s) * ι (quadOdd 3 K) (vecMinus₀ K)) :=
  ι_mul_ι_eq_neg_of_polar_eq_zero _ (polar_vecMinus₀_vec K (by decide) s)

theorem mul_mul_of_anticomm {A : Type*} [Ring A] {u a a' b b' : A} (ha : u * a = -(a' * u))
    (hb : u * b = -(b' * u)) : u * (a * b) = a' * b' * u := by
  rw [← mul_assoc, ha, neg_mul, mul_assoc, hb, mul_neg, neg_neg, ← mul_assoc]

theorem mul_of_commute_of_mul {A : Type*} [Ring A] {u ω X Z : A} (hω : Commute ω X)
    (hu : u * X = Z * u) : u * ω * X = Z * (u * ω) := by
  rw [mul_assoc, hω.eq, ← mul_assoc, hu, mul_assoc]

abbrev omegaTwo : CliffordAlgebra (quadOdd 3 K) :=
  ι (quadOdd 3 K) (vecPlus₂ K) * ι (quadOdd 3 K) (vecMinus₂ K) *
    ι (quadOdd 3 K) (oddFrame 3 K).z

theorem commute_omegaTwo_vec_mul_vec {k l : Fin 3} (hk : k ≠ 2) (hl : l ≠ 2) (s t : Bool) :
    Commute (omegaTwo K) (ι (quadOdd 3 K) ((oddFrame 3 K).vec k s) *
      ι (quadOdd 3 K) ((oddFrame 3 K).vec l t)) :=
  ((commute_ι_ι_mul_ι _ (polar_vecPlus₂_vec K hk s) (polar_vecPlus₂_vec K hl t)).mul_left
    (commute_ι_ι_mul_ι _ (polar_vecMinus₂_vec K hk s) (polar_vecMinus₂_vec K hl t))).mul_left
    (commute_ι_ι_mul_ι _ ((oddFrame 3 K).polar_z_vec k s) ((oddFrame 3 K).polar_z_vec l t))

theorem iBar_mem : ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecPlus₂ K) *
    ι (quadOdd 3 K) (vecMinus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z ∈
      spinGroup (quadOdd 3 K) := by
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  have h1 : ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecMinus₂ K) ∈
      spinGroup (quadOdd 3 K) :=
    ι_mul_ι_mem_spinGroup _ (by rw [quadOdd_vecMinus₀, quadOdd_vecMinus₂]; norm_num)
  have h2 : ι (quadOdd 3 K) (vecPlus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z ∈
      spinGroup (quadOdd 3 K) :=
    ι_mul_ι_mem_spinGroup _ (by rw [quadOdd_vecPlus₂, (oddFrame 3 K).map_z]; norm_num)
  have e : ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecPlus₂ K) *
      ι (quadOdd 3 K) (vecMinus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z =
      (spinGroup.negOne (quadOdd 3 K) hQ : CliffordAlgebra (quadOdd 3 K)) *
        (ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecMinus₂ K)) *
        (ι (quadOdd 3 K) (vecPlus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z) := by
    rw [spinGroup.coe_negOne, mul_assoc (ι (quadOdd 3 K) (vecMinus₀ K)),
      ι_mul_ι_eq_neg_of_polar_eq_zero _ (polar_vecPlus₂_vecMinus₂ K)]
    noncomm_ring
  rw [e]
  exact mul_mem (mul_mem (spinGroup.negOne (quadOdd 3 K) hQ).2 h1) h2

@[expose] def iBar : spinGroup (quadOdd 3 K) := ⟨_, iBar_mem K⟩

theorem coe_iBar : (iBar K : CliffordAlgebra (quadOdd 3 K)) =
    ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecPlus₂ K) *
      ι (quadOdd 3 K) (vecMinus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z := rfl

theorem coe_iBar_eq_mul_omegaTwo :
    (iBar K : CliffordAlgebra (quadOdd 3 K)) = ι (quadOdd 3 K) (vecMinus₀ K) * omegaTwo K := by
  rw [coe_iBar, omegaTwo]
  simp only [mul_assoc]

theorem iBar_mul_self : iBar K * iBar K = 1 := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, coe_iBar, OneMemClass.coe_one]
  have e : ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecPlus₂ K) *
      ι (quadOdd 3 K) (vecMinus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z =
      -((ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecMinus₂ K)) *
        (ι (quadOdd 3 K) (vecPlus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z)) := by
    rw [mul_assoc (ι (quadOdd 3 K) (vecMinus₀ K)),
      ι_mul_ι_eq_neg_of_polar_eq_zero _ (polar_vecPlus₂_vecMinus₂ K)]
    noncomm_ring
  set a := ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) (vecMinus₂ K) with ha
  set b := ι (quadOdd 3 K) (vecPlus₂ K) * ι (quadOdd 3 K) (oddFrame 3 K).z with hb
  have hab : a * b = b * a := (commute_ι_mul_ι _ (polar_vecMinus₀_vecPlus₂ K)
    (polar_vecMinus₀_z K) (by rw [polar_comm]; exact polar_vecPlus₂_vecMinus₂ K)
    (polar_vecMinus₂_z K)).eq
  have ha2 : a * a = -1 := by
    rw [ha, ι_mul_ι_mul_self_of_polar _ (by rw [polar_comm]; exact polar_vecMinus₀_vecMinus₂ K),
      quadOdd_vecMinus₀, quadOdd_vecMinus₂]
    simp
  have hb2 : b * b = -1 := by
    rw [hb, ι_mul_ι_mul_self_of_polar _ (by rw [polar_comm]; exact polar_vecPlus₂_z K),
      quadOdd_vecPlus₂, (oddFrame 3 K).map_z]
    simp
  rw [e]
  calc -(a * b) * -(a * b) = a * (b * a) * b := by noncomm_ring
    _ = a * (a * b) * b := by rw [hab]
    _ = a * a * (b * b) := by noncomm_ring
    _ = 1 := by rw [ha2, hb2]; noncomm_ring

theorem commute_iBar_shortSeven (h2 : (2 : K) ≠ 0) (M : SL(2, K)) :
    Commute (iBar K) (shortSeven K M) := by
  have hpm : polar (quadOdd 3 K) (vecMinus₂ K) (vecPlus₂ K) = 0 := by
    rw [polar_comm]; exact polar_vecPlus₂_vecMinus₂ K
  have hzp : polar (quadOdd 3 K) (oddFrame 3 K).z (vecPlus₂ K) = 0 := by
    rw [polar_comm]; exact polar_vecPlus₂_z K
  have hzm : polar (quadOdd 3 K) (oddFrame 3 K).z (vecMinus₂ K) = 0 := by
    rw [polar_comm]; exact polar_vecMinus₂_z K
  have cp : Commute (ι (quadOdd 3 K) (vecPlus₂ K)) (omegaTwo K) :=
    commute_ι_triple_left (quadOdd 3 K) (polar_vecPlus₂_vecMinus₂ K) (polar_vecPlus₂_z K)
  have cm : Commute (ι (quadOdd 3 K) (vecMinus₂ K)) (omegaTwo K) :=
    commute_ι_triple_mid (quadOdd 3 K) hpm (polar_vecMinus₂_z K)
  have cz : Commute (ι (quadOdd 3 K) (oddFrame 3 K).z) (omegaTwo K) :=
    commute_ι_triple_right (quadOdd 3 K) hzp hzm
  have ce : Commute (ι (quadOdd 3 K) ((oddFrame 3 K).vec 2 true)) (omegaTwo K) := by
    rw [ι_vec_two_true K h2]
    exact (cp.add_left cm).smul_left _
  have cf : Commute (ι (quadOdd 3 K) ((oddFrame 3 K).vec 2 false)) (omegaTwo K) := by
    rw [ι_vec_two_false K h2]
    exact (cp.sub_left cm).smul_left _
  have hX : Commute ((oddFrame 3 K).shortPair 2 true).X
      (iBar K : CliffordAlgebra (quadOdd 3 K)) := by
    rw [coe_iBar_eq_mul_omegaTwo]
    change Commute (ι (quadOdd 3 K) (oddFrame 3 K).z *
      ι (quadOdd 3 K) ((oddFrame 3 K).vec 2 true)) _
    exact (commute_ι_ι_mul_ι (quadOdd 3 K) (polar_vecMinus₀_z K)
      (polar_vecMinus₀_vec K (by decide) true)).symm.mul_right (cz.mul_left ce)
  have hY : Commute ((oddFrame 3 K).shortPair 2 true).Y
      (iBar K : CliffordAlgebra (quadOdd 3 K)) := by
    rw [coe_iBar_eq_mul_omegaTwo]
    change Commute (ι (quadOdd 3 K) ((oddFrame 3 K).vec 2 false) *
      ι (quadOdd 3 K) (oddFrame 3 K).z) _
    exact (commute_ι_ι_mul_ι (quadOdd 3 K) (polar_vecMinus₀_vec K (by decide) false)
      (polar_vecMinus₀_z K)).symm.mul_right (cf.mul_left cz)
  refine commute_of_coe ?_
  rw [OddFrame.coe_shortSL2]
  exact (SL2Pair.commute_toFun_of_commute _ hX hY _).symm

theorem coe_iBar_mul_vec_mul_vec {k l : Fin 3} (hk : k ≠ 2) (hl : l ≠ 2) (s t : Bool)
    {a' b' : CliffordAlgebra (quadOdd 3 K)}
    (ha : ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) ((oddFrame 3 K).vec k s) =
      -(a' * ι (quadOdd 3 K) (vecMinus₀ K)))
    (hb : ι (quadOdd 3 K) (vecMinus₀ K) * ι (quadOdd 3 K) ((oddFrame 3 K).vec l t) =
      -(b' * ι (quadOdd 3 K) (vecMinus₀ K))) :
    (iBar K : CliffordAlgebra (quadOdd 3 K)) * (ι (quadOdd 3 K) ((oddFrame 3 K).vec k s) *
      ι (quadOdd 3 K) ((oddFrame 3 K).vec l t)) = a' * b' * iBar K := by
  rw [coe_iBar_eq_mul_omegaTwo]
  exact mul_of_commute_of_mul (commute_omegaTwo_vec_mul_vec K hk hl s t)
    (mul_mul_of_anticomm ha hb)

end CFSG.ComponentClassification.HarrisLit.T1.S74
