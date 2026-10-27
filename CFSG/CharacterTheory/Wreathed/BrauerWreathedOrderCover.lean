module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderLinear
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderUnits

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed.BrauerWreathedOrder

open Matrix CFSG.DesarguesianPlanes CFSG.BrauerLinearThree CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.WreathedCentralCover

theorem det_nonsquareMatrix' {F : Type} [Field F] (b : Fˣ) :
    GeneralLinearGroup.det (nonsquareMatrix F b) = b := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, nonsquareMatrix_val, Matrix.det_fin_two_of]
  ring

theorem det_scalar_two {F : Type} [Field F] (a : Fˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) F) = a ^ 2 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  simp [GeneralLinearGroup.scalar, sq]

theorem eq_one_of_odd_of_sq_eq_one {M : Type*} [Monoid M] {a : M} (ha : Odd (orderOf a))
    (h : a ^ 2 = 1) : a = 1 := by
  have hdvd := orderOf_dvd_of_pow_eq_one h
  have h1 : orderOf a = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at ha
      exact absurd ha (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem ringChar_ne_two_of {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro h
  apply h2
  have := ringChar.Nat.cast_ringChar (R := F)
  rw [h] at this
  exact_mod_cast this

variable {G : Type} [Group G] [Finite G] {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
  {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  (φ : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) ≃*
    GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hq3 : 3 ≤ Nat.card F)

@[expose] def quotHom : GL (Fin 2) F →* centralizerOddCoreQuotient n S e :=
  (centralizerOddCoreMap n S e).comp (centralizerHom φ)

omit [Finite G] [Finite F] in
theorem quotHom_apply (A : GL (Fin 2) F) :
    quotHom φ A = centralizerOddCoreMap n S e (centralizerHom φ A) := rfl

omit [Finite G] [Finite F] in
theorem quotHom_surjective : Function.Surjective (quotHom φ) :=
  (centralizerOddCoreMap_surjective n S e).comp (centralizerHom_surjective φ)

omit [Finite G] in
include hZ hZodd h2 hq3 in
theorem quotHom_eq_one_iff (A : GL (Fin 2) F) :
    quotHom φ A = 1 ↔ ∃ a : Fˣ, Odd (orderOf a) ∧ A = GeneralLinearGroup.scalar (Fin 2) a := by
  rw [← centralizerHom_mem_oddCore_iff φ hZ hZodd h2 hq3 A]
  exact QuotientGroup.eq_one_iff _

omit [Finite G] in
include hZ hZodd h2 hq3 in
theorem quotHom_scalar_of_odd {a : Fˣ} (ha : Odd (orderOf a)) :
    quotHom φ (GeneralLinearGroup.scalar (Fin 2) a) = 1 :=
  (quotHom_eq_one_iff φ hZ hZodd h2 hq3 _).mpr ⟨a, ha, rfl⟩

@[expose] def coverInclusion : SpecialLinearGroup (Fin 2) F →* centralizerOddCoreQuotient n S e :=
  (quotHom φ).comp SpecialLinearGroup.toGL

@[expose] def coverTau (b : Fˣ) : centralizerOddCoreQuotient n S e :=
  quotHom φ (nonsquareMatrix F b)

omit [Finite G] in
include hZ hZodd h2 hq3 in
theorem coverInclusion_injective : Function.Injective (coverInclusion φ) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  obtain ⟨a, ha, hXa⟩ := (quotHom_eq_one_iff φ hZ hZodd h2 hq3 _).mp hX
  have hdet := congrArg GeneralLinearGroup.det hXa
  rw [det_scalar_two] at hdet
  have hdet1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL X) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact X.2
  rw [hdet1] at hdet
  have ha1 := eq_one_of_odd_of_sq_eq_one ha hdet.symm
  rw [ha1, map_one] at hXa
  exact SpecialLinearGroup.toGL_injective (hXa.trans (map_one _).symm)

omit [Finite G] [Finite F] in
theorem coverInclusion_beta (b : Fˣ) (X : SpecialLinearGroup (Fin 2) F) :
    coverInclusion φ (beta F b X) = coverTau φ b * coverInclusion φ X * (coverTau φ b)⁻¹ := by
  rw [coverInclusion, MonoidHom.comp_apply, beta_toGL, map_mul, map_mul, map_inv]
  rfl

variable {d : ℕ} (hqd : Nat.card F - 1 = 2 ^ n * d) (hd : Odd d) (hn : 2 ≤ n)

omit [Finite G] in
include hZ hZodd h2 hq3 hqd hd in
theorem coverTau_pow (b : Fˣ) : coverTau φ b ^ (2 * 2 ^ n) = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hqd
  rw [coverTau, ← map_pow, pow_mul, nonsquareMatrix_square, ← map_pow]
  exact quotHom_scalar_of_odd φ hZ hZodd h2 hq3 (odd_orderOf_pow_two_pow hqd hd _)

omit [Finite G] in
include hZ hZodd h2 hq3 hqd hd hn in
theorem coverInclusion_minus (b : Fˣ) (hnb : ¬ IsSquare (-b)) :
    coverInclusion φ (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      coverTau φ b ^ 2 ^ n := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hqd
  obtain ⟨u, hu, hpow⟩ := exists_pow_two_pow_pred_eq_neg (ringChar_ne_two_of h2) hqd hd
    (by omega) hnb
  have hm : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hminus : SpecialLinearGroup.toGL (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      GeneralLinearGroup.scalar (Fin 2) (-1) := by
    apply Units.ext
    change (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F : Matrix (Fin 2) (Fin 2) F) = _
    rw [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar]
  rw [coverInclusion, MonoidHom.comp_apply, hminus, coverTau, ← map_pow, hm, pow_mul,
    nonsquareMatrix_square, ← map_pow, hpow]
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
  apply quotHom_scalar_of_odd φ hZ hZodd h2 hq3
  rw [show (-1 : Fˣ) * (-u)⁻¹ = u⁻¹ by rw [inv_neg, neg_one_mul, neg_neg], orderOf_inv]
  exact hu

omit [Finite G] in
include hZ hZodd h2 hq3 hqd in
theorem coverTau_intersection (b : Fˣ) (hb : ¬ IsSquare b) (j : ℕ) (hj : j < 2 * 2 ^ n)
    (hmem : coverTau φ b ^ j ∈ (coverInclusion φ).range) : j = 0 ∨ j = 2 ^ n := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hqd
  obtain ⟨X, hX⟩ := hmem
  have h1 : quotHom φ (nonsquareMatrix F b ^ j * (SpecialLinearGroup.toGL X)⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv]
    rw [coverInclusion, MonoidHom.comp_apply] at hX
    rw [hX]
    exact mul_inv_cancel _
  obtain ⟨z, hz, hzA⟩ := (quotHom_eq_one_iff φ hZ hZodd h2 hq3 _).mp h1
  have hdet := congrArg GeneralLinearGroup.det hzA
  have hdet1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL X) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact X.2
  rw [map_mul, map_pow, map_inv, hdet1, inv_one, mul_one, det_nonsquareMatrix',
    det_scalar_two] at hdet
  have hodd : Odd (orderOf (b ^ j)) := by
    rw [hdet]
    exact hz.of_dvd_nat (orderOf_pow_dvd 2)
  obtain ⟨k, hk⟩ := two_pow_dvd_of_odd_orderOf_pow hqd hb hodd
  have hk2 : k < 2 := by
    by_contra hk2
    push Not at hk2
    have : 2 ^ n * 2 ≤ 2 ^ n * k := Nat.mul_le_mul_left _ hk2
    omega
  interval_cases k
  · left
    omega
  · right
    omega

omit [Finite G] in
include hZ hZodd h2 hq3 hqd hd in
theorem pairToCover_surjective (b : Fˣ) (hb : ¬ IsSquare b) :
    Function.Surjective (pairToCover F b (2 ^ n) (wreathModulus_pos n) (coverInclusion φ)
      (coverTau φ b) (coverTau_pow φ hZ hZodd h2 hq3 hqd hd b) (coverInclusion_beta φ b)) := by
  let _ : Fintype F := Fintype.ofFinite F
  have hqd' := hqd
  rw [Nat.card_eq_fintype_card] at hqd'
  intro h
  obtain ⟨A, rfl⟩ := quotHom_surjective φ h
  obtain ⟨k, w, hw, hdetA⟩ := exists_eq_pow_mul_odd hqd' hd hb (GeneralLinearGroup.det A)
  obtain ⟨z, hz, rfl⟩ := exists_eq_sq_of_odd_orderOf hw
  set Y : GL (Fin 2) F := A * (nonsquareMatrix F b ^ k)⁻¹ *
    (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ with hY
  have hYdet : GeneralLinearGroup.det Y = 1 := by
    rw [hY, map_mul, map_mul, map_inv, map_inv, map_pow, det_nonsquareMatrix', det_scalar_two,
      hdetA, mul_comm (b ^ k) (z ^ 2), mul_inv_cancel_right, mul_inv_cancel]
  let X : SpecialLinearGroup (Fin 2) F := ⟨(Y : Matrix (Fin 2) (Fin 2) F), by
    have := congrArg Units.val hYdet
    rwa [GeneralLinearGroup.val_det_apply] at this⟩
  have hXY : SpecialLinearGroup.toGL X = Y := Units.ext rfl
  refine ⟨pair F b (2 ^ n) (wreathModulus_pos n) X (k : ZMod (2 * 2 ^ n)), ?_⟩
  rw [pairToCover_pair]
  have hval : coverTau φ b ^ (k : ZMod (2 * 2 ^ n)).val = coverTau φ b ^ k := by
    have : NeZero (2 * 2 ^ n) := ⟨by positivity⟩
    rw [ZMod.val_natCast]
    exact (pow_eq_pow_mod k (coverTau_pow φ hZ hZodd h2 hq3 hqd hd b)).symm
  rw [hval, coverInclusion, MonoidHom.comp_apply, hXY, coverTau, ← map_pow, ← map_mul, hY]
  rw [mul_assoc (A * _), ((scalar_commute z (nonsquareMatrix F b ^ k)).inv_left).eq,
    ← mul_assoc, inv_mul_cancel_right]
  rw [map_mul, map_inv, quotHom_scalar_of_odd φ hZ hZodd h2 hq3 hz, inv_one, mul_one]

include hZ hZodd h2 hq3 hqd hd hn in
@[expose] def coverEquiv (b : Fˣ) (hb : ¬ IsSquare b) (hnb : ¬ IsSquare (-b)) :
    CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ≃*
      centralizerOddCoreQuotient n S e :=
  quotientCoverEquiv F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
    (coverInclusion φ) (coverInclusion_injective φ hZ hZodd h2 hq3)
    (coverTau φ b) (coverTau_pow φ hZ hZodd h2 hq3 hqd hd b) (coverInclusion_beta φ b)
    (coverInclusion_minus φ hZ hZodd h2 hq3 hqd hd hn b hnb)
    (coverTau_intersection φ hZ hZodd h2 hq3 hqd b hb)
    (pairToCover_surjective φ hZ hZodd h2 hq3 hqd hd b hb)

omit [Finite F] in
theorem bot_fixes (b : Fˣ) : ∀ σ ∈ (⊥ : Subgroup (F ≃+* F)), σ (b : F) = b := by
  intro σ hσ
  rw [Subgroup.mem_bot] at hσ
  rw [hσ]
  rfl

omit [Finite F] in
@[expose] def botInclusionEquiv (b : Fˣ) :
    CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ≃*
      SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ⊥
        (bot_fixes b) :=
  MulEquiv.ofBijective SemidirectProduct.inl
    ⟨SemidirectProduct.inl_injective, fun g => ⟨g.left,
      SemidirectProduct.ext rfl (Subsingleton.elim _ _)⟩⟩

include hZ hZodd h2 hq3 hqd hd in
@[expose] def semilinearEquiv (b : Fˣ) (hb : ¬ IsSquare b) (hnb : ¬ IsSquare (-b)) :
    SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ⊥
        (bot_fixes b) ≃* centralizerOddCoreQuotient n S e :=
  (botInclusionEquiv hn b).symm.trans (coverEquiv φ hZ hZodd h2 hq3 hqd hd hn b hb hnb)

omit [Finite G] in
theorem semilinearEquiv_apply (b : Fˣ) (hb : ¬ IsSquare b) (hnb : ¬ IsSquare (-b))
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (σ : (⊥ : Subgroup (F ≃+* F))) :
    semilinearEquiv φ hZ hZodd h2 hq3 hqd hd hn b hb hnb
        ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X j, σ⟩ =
      quotHom φ (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val) := by
  have h : (botInclusionEquiv hn b).symm
      ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X j, σ⟩ =
        quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X j := by
    rw [MulEquiv.symm_apply_eq]
    exact SemidirectProduct.ext rfl (Subsingleton.elim _ _)
  rw [semilinearEquiv, MulEquiv.trans_apply, h, map_mul, map_pow]
  rfl

end CFSG.Wreathed.BrauerWreathedOrder
