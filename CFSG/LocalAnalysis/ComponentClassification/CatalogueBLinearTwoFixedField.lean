module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoFixed

noncomputable section

open Matrix CFSG.GorensteinWalter

universe u

@[expose] def fixedField (K : Type u) [Field K] (sigma : K ≃+* K) : Subfield K :=
  FixedPoints.subfield (Subgroup.zpowers sigma) K

theorem mem_fixedField_iff (K : Type u) [Field K] (sigma : K ≃+* K) (x : K) :
    x ∈ fixedField K sigma ↔ sigma x = x := by
  constructor
  · intro hx
    exact hx ⟨sigma, Subgroup.mem_zpowers sigma⟩
  · intro hx tau
    rcases Subgroup.mem_zpowers_iff.mp tau.2 with ⟨z, hz⟩
    change (tau : K ≃+* K) x = x
    rw [← hz]
    exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy K sigma from hx) z

theorem fixedField_coe (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : fixedField K sigma) : sigma (x : K) = (x : K) :=
  (mem_fixedField_iff K sigma x).mp x.2

theorem involution_apply_apply (K : Type u) [Field K] (sigma : K ≃+* K)
    (hsigma : orderOf sigma = 2) (x : K) : sigma (sigma x) = x := by
  have h := pow_orderOf_eq_one sigma
  rw [hsigma, pow_two] at h
  exact congrArg (fun e : K ≃+* K => e x) h

theorem involution_exists_moved (K : Type u) [Field K] (sigma : K ≃+* K)
    (hsigma : orderOf sigma = 2) : ∃ x : K, sigma x ≠ x := by
  by_contra h
  have hid : sigma = 1 := by
    apply RingEquiv.ext
    intro x
    exact not_not.mp (not_exists.mp h x)
  have horder : orderOf sigma = 1 := orderOf_eq_one_iff.mpr hid
  omega

theorem card_eq_fixedField_card_sq (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) :
    Nat.card K = Nat.card (fixedField K sigma) ^ 2 := by
  simpa only [fixedField, hsigma] using
    nat_card_eq_fixedSubfield_card_pow_orderOf K sigma

theorem exists_scalar_hilbert90 (K : Type u) [Field K] (sigma : K ≃+* K)
    (hsigma : orderOf sigma = 2) (c : K) (hnorm : c * sigma c = 1) :
    ∃ b : K, b ≠ 0 ∧ sigma b = c⁻¹ * b := by
  have hc : c ≠ 0 := by
    intro hc
    simp [hc] at hnorm
  have hsc : sigma c = c⁻¹ := by
    apply (mul_left_cancel₀ hc)
    rw [hnorm, mul_inv_cancel₀ hc]
  by_cases hminus : c = -1
  · obtain ⟨x, hx⟩ := involution_exists_moved K sigma hsigma
    refine ⟨x - sigma x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
    rw [map_sub, involution_apply_apply K sigma hsigma, hminus]
    simp only [inv_neg, inv_one, neg_one_mul]
    ring
  · refine ⟨1 + c, ?_, ?_⟩
    · intro hzero
      apply hminus
      linear_combination hzero
    · rw [map_add, map_one, hsc]
      field_simp
      ring

theorem exists_unit_hilbert90 (K : Type u) [Field K] (sigma : K ≃+* K)
    (hsigma : orderOf sigma = 2) (c : Kˣ)
    (hnorm : c * Units.map sigma.toMonoidHom c = 1) :
    ∃ b : Kˣ, Units.map sigma.toMonoidHom b = c⁻¹ * b := by
  have hn : (c : K) * sigma (c : K) = 1 := congrArg Units.val hnorm
  obtain ⟨b, hb, hsb⟩ := exists_scalar_hilbert90 K sigma hsigma c hn
  refine ⟨Units.mk0 b hb, ?_⟩
  apply Units.ext
  simpa using hsb

theorem exists_fixedField_GL (K : Type u) [Field K] (sigma : K ≃+* K)
    (A : GL (Fin 2) K) (hA : ∀ i j, sigma (A i j) = A i j) :
    ∃ B : GL (Fin 2) (fixedField K sigma),
      Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype B = A := by
  let M : Matrix (Fin 2) (Fin 2) (fixedField K sigma) :=
    fun i j => ⟨A i j, (mem_fixedField_iff K sigma (A i j)).mpr (hA i j)⟩
  have hM : (fixedField K sigma).subtype.mapMatrix M = A.val := rfl
  have hdet : M.det ≠ 0 := by
    intro hz
    apply A.det_ne_zero
    have h := congrArg (fixedField K sigma).subtype hz
    rw [map_zero, RingHom.map_det, hM] at h
    exact h
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

end

end CFSG.ComponentClassification.CatalogueBLinearTwoFixed
