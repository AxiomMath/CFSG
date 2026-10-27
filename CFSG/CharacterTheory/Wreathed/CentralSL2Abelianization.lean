module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.CharacterTheory.Wreathed.CyclicCentralSL2Extension
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction

public noncomputable section
namespace CFSG.Wreathed.CentralSL2Abelianization
open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
universe u v
variable (F : Type u) [Field F]

variable {F} in
theorem mem_diagonal_iff {b : Fˣ} {m : ℕ} {hm : 0 < m}
    (heven : Even m) {g : PairGroup F b m hm} :
    g ∈ diagonalKernel F b m hm heven ↔ g = 1 ∨ g = diagonalInvolution F b m hm := by
  classical
  have hfinite : IsOfFinOrder (diagonalInvolution F b m hm) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, diagonalInvolution_square F b m hm heven⟩
  rw [diagonalKernel, hfinite.mem_zpowers_iff_mem_range_orderOf,
    diagonalInvolution_order F b m hm heven]
  constructor
  · rintro hg
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
    have hj' : j < 2 := Finset.mem_range.mp hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact Or.inl (pow_zero _)
    · exact Or.inr (pow_one _)
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), pow_zero _⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), pow_one _⟩

theorem specialInclusion_injective (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    Function.Injective (specialInclusion F b m hm heven) := by
  apply (injective_iff_map_eq_one _).mpr
  intro X hX
  have hmem : pair F b m hm X 0 ∈ diagonalKernel F b m hm heven :=
    (QuotientGroup.eq_one_iff _).mp hX
  rcases (mem_diagonal_iff heven).mp hmem with hone | hdiag
  · exact congrArg SemidirectProduct.left hone
  · have hright := congrArg (fun g : PairGroup F b m hm => g.right.toAdd) hdiag
    have hval := congrArg ZMod.val hright
    change (0 : ZMod (2 * m)).val = (m : ZMod (2 * m)).val at hval
    rw [ZMod.val_zero, ZMod.val_natCast_of_lt (by omega)] at hval
    omega

@[expose] def residueReduction (m : ℕ) :
    Multiplicative (ZMod (2 * m)) →* Multiplicative (ZMod m) :=
  (ZMod.castHom (dvd_mul_left m 2) (ZMod m)).toAddMonoidHom.toMultiplicative

@[expose] def pairResidue (b : Fˣ) (m : ℕ) (hm : 0 < m) :
    PairGroup F b m hm →* Multiplicative (ZMod m) :=
  (residueReduction m).comp SemidirectProduct.rightHom

theorem pairResidue_pair (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    pairResidue F b m hm (pair F b m hm X j) =
      Multiplicative.ofAdd (ZMod.castHom (dvd_mul_left m 2) (ZMod m) j) := rfl

theorem diagonal_le_pairResidue_ker (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    diagonalKernel F b m hm heven ≤ (pairResidue F b m hm).ker := by
  apply Subgroup.zpowers_le.mpr
  change pairResidue F b m hm (pair F b m hm _ (m : ZMod (2 * m))) = 1
  rw [pairResidue_pair, map_natCast, ZMod.natCast_self]
  rfl

@[expose] def baseResidue (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    CentralExtension F b m hm heven →* Multiplicative (ZMod m) :=
  QuotientGroup.lift (diagonalKernel F b m hm heven) (pairResidue F b m hm)
    (diagonal_le_pairResidue_ker F b m hm heven)

theorem baseResidue_quotientClass (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    baseResidue F b m hm heven (quotientClass F b m hm heven X j) =
      Multiplicative.ofAdd (ZMod.castHom (dvd_mul_left m 2) (ZMod m) j) := rfl

theorem baseResidue_specialInclusion (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (X : SpecialLinearGroup (Fin 2) F) :
    baseResidue F b m hm heven (specialInclusion F b m hm heven X) = 1 := by
  rw [specialInclusion_apply, baseResidue_quotientClass, map_zero]
  rfl

theorem quotientClass_mid (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (X : SpecialLinearGroup (Fin 2) F) :
    quotientClass F b m hm heven X (m : ZMod (2 * m)) =
      specialInclusion F b m hm heven
        (X * CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) := by
  apply (QuotientGroup.mk'_eq_mk' (diagonalKernel F b m hm heven)).mpr
  refine ⟨diagonalInvolution F b m hm, Subgroup.mem_zpowers _, ?_⟩
  have hmid : cyclicAction F b m hm (Multiplicative.ofAdd (m : ZMod (2 * m))) = 1 := by
    rw [cyclicAction_natCast]
    obtain ⟨k, hk⟩ := heven
    rw [hk, ← two_mul, pow_mul, beta_square, one_pow]
  apply SemidirectProduct.ext
  · change X * cyclicAction F b m hm (Multiplicative.ofAdd (m : ZMod (2 * m))) _ = _
    rw [hmid, MulAut.one_apply]
    rfl
  · apply Multiplicative.toAdd.injective
    change (m : ZMod (2 * m)) + m = 0
    simpa only [two_mul, Nat.cast_add] using ZMod.natCast_self (2 * m)

theorem baseResidue_ker (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    (baseResidue F b m hm heven).ker = (specialInclusion F b m hm heven).range := by
  ext q
  constructor
  · induction q using QuotientGroup.induction_on with
    | H v =>
      intro hq
      change baseResidue F b m hm heven
        (quotientClass F b m hm heven v.left v.right.toAdd) = 1 at hq
      rw [baseResidue_quotientClass] at hq
      have hj : ZMod.castHom (dvd_mul_left m 2) (ZMod m) v.right.toAdd = 0 :=
        congrArg Multiplicative.toAdd hq
      let : NeZero (2 * m) := ⟨by omega⟩
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hj
      have hjlt := v.right.toAdd.val_lt
      have hjcases : v.right.toAdd.val = 0 ∨ v.right.toAdd.val = m := by
        obtain ⟨k, hk⟩ := hj
        have hklt : k < 2 := (Nat.mul_lt_mul_left hm).mp
          (by simpa only [hk, Nat.mul_comm] using hjlt)
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · left; simpa using hk
        · right; simpa using hk
      rcases hjcases with hz | hmj
      · have hz' : v.right.toAdd = 0 := (ZMod.val_eq_zero _).mp hz
        refine ⟨v.left, ?_⟩
        change quotientClass F b m hm heven v.left 0 =
          quotientClass F b m hm heven v.left v.right.toAdd
        rw [hz']
      · have hmj' : v.right.toAdd = (m : ZMod (2 * m)) := by
          apply ZMod.val_injective
          rw [hmj, ZMod.val_natCast_of_lt (by omega)]
        refine ⟨v.left * CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F, ?_⟩
        change _ = quotientClass F b m hm heven v.left v.right.toAdd
        rw [hmj', quotientClass_mid]
  · rintro ⟨X, rfl⟩
    exact baseResidue_specialInclusion F b m hm heven X

theorem baseResidue_surjective (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    Function.Surjective (baseResidue F b m hm heven) := by
  intro j
  obtain ⟨k, hk⟩ := ZMod.castHom_surjective (dvd_mul_left m 2) j.toAdd
  refine ⟨quotientClass F b m hm heven 1 k, ?_⟩
  rw [baseResidue_quotientClass, hk]
  rfl

section SemilinearResidue

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)

@[expose] def matrixInclusion :
    SpecialLinearGroup (Fin 2) F →* SemilinearExtension F b m hm heven Sigma hSigma :=
  SemidirectProduct.inl.comp (specialInclusion F b m hm heven)

@[expose] def matrixLayer : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
  (matrixInclusion F b m hm heven Sigma hSigma).range

theorem matrixInclusion_injective :
    Function.Injective (matrixInclusion F b m hm heven Sigma hSigma) :=
  SemidirectProduct.inl_injective.comp (specialInclusion_injective F b m hm heven)

theorem baseResidue_fieldAction (sigma : Sigma) (q : CentralExtension F b m hm heven) :
    baseResidue F b m hm heven (fieldAction F b m hm heven Sigma hSigma sigma q) =
      baseResidue F b m hm heven q := by
  induction q using QuotientGroup.induction_on with
  | H v =>
    change baseResidue F b m hm heven (fieldAction F b m hm heven Sigma hSigma sigma
      (quotientClass F b m hm heven v.left v.right.toAdd)) = _
    rw [fieldAction_quotientClass, baseResidue_quotientClass]
    rfl

@[expose] def psi : SemilinearExtension F b m hm heven Sigma hSigma →*
    Multiplicative (ZMod m) × Sigma where
  toFun h := (baseResidue F b m hm heven h.left, h.right)
  map_one' := by apply Prod.ext <;> simp
  map_mul' h k := by
    apply Prod.ext
    · change baseResidue F b m hm heven
        (h.left * fieldAction F b m hm heven Sigma hSigma h.right k.left) = _
      rw [map_mul, baseResidue_fieldAction]
      rfl
    · rfl

theorem psi_formula (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (sigma : Sigma) :
    psi F b m hm heven Sigma hSigma
      ⟨quotientClass F b m hm heven X j, sigma⟩ =
      (Multiplicative.ofAdd (ZMod.castHom (dvd_mul_left m 2) (ZMod m) j), sigma) := rfl

theorem psi_surjective : Function.Surjective (psi F b m hm heven Sigma hSigma) := by
  rintro ⟨j, sigma⟩
  obtain ⟨q, hq⟩ := baseResidue_surjective F b m hm heven j
  exact ⟨⟨q, sigma⟩, Prod.ext hq rfl⟩

theorem psi_ker : (psi F b m hm heven Sigma hSigma).ker =
    matrixLayer F b m hm heven Sigma hSigma := by
  ext h
  constructor
  · intro hh
    have hleft : baseResidue F b m hm heven h.left = 1 := congrArg Prod.fst hh
    have hright : h.right = 1 := congrArg Prod.snd hh
    have hmem : h.left ∈ (specialInclusion F b m hm heven).range :=
      (baseResidue_ker F b m hm heven) ▸ hleft
    obtain ⟨X, hX⟩ := hmem
    exact ⟨X, SemidirectProduct.ext hX (by change 1 = h.right; exact hright.symm)⟩
  · rintro ⟨X, rfl⟩
    exact Prod.ext (baseResidue_specialInclusion F b m hm heven X) rfl

instance matrixLayer_normal : (matrixLayer F b m hm heven Sigma hSigma).Normal := by
  rw [← psi_ker]
  infer_instance

end SemilinearResidue

section DerivedGroup

@[expose] def weyl : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

theorem beta_upper (b : Fˣ) (t : F) :
    beta F b (SpecialLinearGroup.transvection zero_ne_one t) =
      SpecialLinearGroup.transvection one_ne_zero (-t / (b : F)) := by
  apply SpecialLinearGroup.toGL_injective
  rw [beta_toGL, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonsquareMatrix_val, SpecialLinearGroup.toGL, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, div_mul_cancel₀ _ b.ne_zero]

theorem weyl_lower (t : F) :
    weyl F * SpecialLinearGroup.transvection one_ne_zero t * (weyl F)⁻¹ =
      SpecialLinearGroup.transvection zero_ne_one (-t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (weyl F : Matrix (Fin 2) (Fin 2) F) *
      ((SpecialLinearGroup.transvection one_ne_zero t : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
    ((SpecialLinearGroup.transvection zero_ne_one (-t) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) *
      (weyl F : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two]

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)

theorem cyclicGenerator_conjugation (X : SpecialLinearGroup (Fin 2) F) :
    cyclicGenerator F b m hm heven * specialInclusion F b m hm heven X *
      (cyclicGenerator F b m hm heven)⁻¹ =
      specialInclusion F b m hm heven (beta F b X) := by
  have h := congrArg (QuotientGroup.mk' (diagonalKernel F b m hm heven))
    (SemidirectProduct.inl_aut
      (φ := cyclicAction F b m hm) (Multiplicative.ofAdd (1 : ZMod (2 * m))) X)
  have ha : cyclicAction F b m hm (Multiplicative.ofAdd (1 : ZMod (2 * m))) =
      beta F b := by
    simpa only [Nat.cast_one, pow_one] using cyclicAction_natCast F b m hm 1
  rw [ha, map_mul, map_mul, map_inv] at h
  exact h.symm

@[expose] def uInH : SemilinearExtension F b m hm heven Sigma hSigma :=
  SemidirectProduct.inl (cyclicGenerator F b m hm heven)

theorem uInH_conjugation (X : SpecialLinearGroup (Fin 2) F) :
    uInH F b m hm heven Sigma hSigma * matrixInclusion F b m hm heven Sigma hSigma X *
      (uInH F b m hm heven Sigma hSigma)⁻¹ =
      matrixInclusion F b m hm heven Sigma hSigma (beta F b X) := by
  have h := congrArg (SemidirectProduct.inl : CentralExtension F b m hm heven →*
    SemilinearExtension F b m hm heven Sigma hSigma)
    (cyclicGenerator_conjugation F b m hm heven X)
  rw [map_mul, map_mul, map_inv] at h
  exact h

theorem hom_conjugation {G : Type u} [Group G] {T : Type v} [CommGroup T]
    (f : G →* T) (g x : G) : f (g * x * g⁻¹) = f x := by
  rw [map_mul, map_mul, map_inv, mul_comm (f g) (f x), mul_assoc,
    mul_inv_cancel, mul_one]

theorem matrixInclusion_trivial_in_abelian_image {T : Type v} [CommGroup T]
    (hb : b ≠ 1)
    (f : SemilinearExtension F b m hm heven Sigma hSigma →* T)
    (X : SpecialLinearGroup (Fin 2) F) :
    f (matrixInclusion F b m hm heven Sigma hSigma X) = 1 := by
  let i := matrixInclusion F b m hm heven Sigma hSigma
  have hconj (g Y : SpecialLinearGroup (Fin 2) F) :
      f (i (g * Y * g⁻¹)) = f (i Y) := by
    exact hom_conjugation (f.comp i) g Y
  have hbeta (Y : SpecialLinearGroup (Fin 2) F) : f (i (beta F b Y)) = f (i Y) := by
    rw [← uInH_conjugation]
    exact hom_conjugation f _ _
  have hupper (t : F) : f (i (SpecialLinearGroup.transvection zero_ne_one t)) = 1 := by
    have heq (c : F) :
        f (i (SpecialLinearGroup.transvection zero_ne_one (c / (b : F)))) =
          f (i (SpecialLinearGroup.transvection zero_ne_one c)) := by
      calc
        _ = f (i (weyl F * SpecialLinearGroup.transvection one_ne_zero
              (-c / (b : F)) * (weyl F)⁻¹)) := by
            rw [weyl_lower]
            simp only [neg_div, neg_neg]
        _ = f (i (SpecialLinearGroup.transvection one_ne_zero (-c / (b : F)))) := hconj _ _
        _ = f (i (beta F b (SpecialLinearGroup.transvection zero_ne_one c))) := by
            rw [beta_upper]
        _ = _ := hbeta _
    have hbval : (b : F) ≠ 1 := by
      intro h; apply hb; exact Units.ext h
    have hscale : (1 : F) - (b : F)⁻¹ ≠ 0 := by
      intro h
      apply hbval
      exact (inv_eq_one.mp (sub_eq_zero.mp h).symm)
    let c := t / (1 - (b : F)⁻¹)
    have hcoef : c + -(c / (b : F)) = t := by
      dsimp [c]
      field_simp
      ring
    have hprod : f (i (SpecialLinearGroup.transvection zero_ne_one
        (c + -(c / (b : F))))) = 1 := by
      rw [SpecialLinearGroup.transvection_add, map_mul, map_mul,
        ← SpecialLinearGroup.transvection_inv, map_inv, map_inv, heq]
      exact mul_inv_cancel _
    rwa [hcoef] at hprod
  have hlower (t : F) : f (i (SpecialLinearGroup.transvection one_ne_zero t)) = 1 := by
    have h := hconj (weyl F) (SpecialLinearGroup.transvection one_ne_zero t)
    rw [weyl_lower, hupper] at h
    exact h.symm
  apply Matrix.SL2.transvection_induction (fun X => f (i X) = 1)
  · intro j k hjk t
    fin_cases j
    · have hk : k = 1 := by fin_cases k <;> tauto
      subst k
      exact hupper t
    · have hk : k = 0 := by fin_cases k <;> tauto
      subst k
      exact hlower t
  · intro X Y hX hY
    rw [map_mul, map_mul, hX, hY, one_mul]

end DerivedGroup


section ExactDerivedQuotient

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)

theorem matrixLayer_le_commutator (hb : b ≠ 1) :
    matrixLayer F b m hm heven Sigma hSigma ≤
      commutator (SemilinearExtension F b m hm heven Sigma hSigma) := by
  rintro h ⟨X, rfl⟩
  rw [← Abelianization.ker_of]
  exact matrixInclusion_trivial_in_abelian_image F b m hm heven Sigma hSigma hb
    Abelianization.of X

theorem fieldSubgroup_isCyclic [Finite F] : IsCyclic Sigma := by
  let : IsCyclic (F ≃+* F) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  infer_instance

theorem commutator_le_matrixLayer [Finite F] :
    commutator (SemilinearExtension F b m hm heven Sigma hSigma) ≤
      matrixLayer F b m hm heven Sigma hSigma := by
  let : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
  rw [← psi_ker]
  exact Abelianization.commutator_subset_ker (psi F b m hm heven Sigma hSigma)

theorem derived_eq_matrixLayer [Finite F] (hb : b ≠ 1) :
    commutator (SemilinearExtension F b m hm heven Sigma hSigma) =
      matrixLayer F b m hm heven Sigma hSigma :=
  le_antisymm (commutator_le_matrixLayer F b m hm heven Sigma hSigma)
    (matrixLayer_le_commutator F b m hm heven Sigma hSigma hb)

@[expose] def matrixQuotientEquiv :
    (SemilinearExtension F b m hm heven Sigma hSigma ⧸
        matrixLayer F b m hm heven Sigma hSigma) ≃*
      Multiplicative (ZMod m) × Sigma :=
  QuotientGroup.liftEquiv _ (psi_surjective F b m hm heven Sigma hSigma)
    (psi_ker F b m hm heven Sigma hSigma).symm

theorem matrixQuotientEquiv_mk (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    matrixQuotientEquiv F b m hm heven Sigma hSigma (QuotientGroup.mk h) =
      psi F b m hm heven Sigma hSigma h := rfl

@[expose] def abelianizationEquiv [Finite F] (hb : b ≠ 1) :
    Abelianization (SemilinearExtension F b m hm heven Sigma hSigma) ≃*
      Multiplicative (ZMod m) × Sigma :=
  QuotientGroup.liftEquiv _ (psi_surjective F b m hm heven Sigma hSigma)
    ((derived_eq_matrixLayer F b m hm heven Sigma hSigma hb).trans
      (psi_ker F b m hm heven Sigma hSigma).symm)

theorem abelianizationEquiv_of [Finite F] (hb : b ≠ 1)
    (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    abelianizationEquiv F b m hm heven Sigma hSigma hb (Abelianization.of h) =
      psi F b m hm heven Sigma hSigma h := rfl

theorem abelianization_card [Finite F] (hb : b ≠ 1) :
    Nat.card (Abelianization (SemilinearExtension F b m hm heven Sigma hSigma)) =
      m * Nat.card Sigma := by
  let : NeZero m := ⟨by omega⟩
  rw [Nat.card_congr (abelianizationEquiv F b m hm heven Sigma hSigma hb).toEquiv,
    Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod m) ≃ ZMod m),
    Nat.card_eq_fintype_card, ZMod.card]

theorem abelianization_isCyclic [Finite F] (hb : b ≠ 1)
    (hcop : Nat.Coprime m (Nat.card Sigma)) :
    IsCyclic (Abelianization (SemilinearExtension F b m hm heven Sigma hSigma)) := by
  let : NeZero m := ⟨by omega⟩
  let : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
  apply (abelianizationEquiv F b m hm heven Sigma hSigma hb).isCyclic.mpr
  apply Group.isCyclic_prod_iff.mpr
  refine ⟨inferInstance, inferInstance, ?_⟩
  simpa only [Nat.card_congr
    (Multiplicative.toAdd : Multiplicative (ZMod m) ≃ ZMod m),
    Nat.card_eq_fintype_card, ZMod.card] using hcop

theorem abelianization_isCyclic_of_two_power [Finite F] (hb : b ≠ 1)
    (a : ℕ) (hm2 : m = 2 ^ a) (hd : Odd (Nat.card Sigma)) :
    IsCyclic (Abelianization (SemilinearExtension F b m hm heven Sigma hSigma)) := by
  apply abelianization_isCyclic F b m hm heven Sigma hSigma hb
  rw [hm2]
  exact hd.coprime_two_left.pow_left a

end ExactDerivedQuotient


instance fieldSubgroup_finite [Finite F] (Sigma : Subgroup (F ≃+* F)) : Finite Sigma :=
  Finite.of_injective (fun sigma : Sigma => (sigma.val : F → F)) (by
    intro a b hab
    apply Subtype.ext
    apply RingEquiv.ext
    exact congrFun hab)

section CyclicScalarCharacters

@[expose] def scalarResidueHom (n : ℕ) (hn : 0 < n) (z : ℂˣ) (hz : z ^ n = 1) :
    Multiplicative (ZMod n) →* ℂˣ := by
  let : NeZero n := ⟨hn.ne'⟩
  refine {
    toFun := fun j => z ^ j.toAdd.val
    map_one' := by simp
    map_mul' := ?_ }
  intro j k
  simp only [toAdd_mul, ZMod.val_add]
  rw [← pow_eq_pow_mod _ hz, pow_add]

theorem scalarResidueHom_natCast (n : ℕ) (hn : 0 < n) (z : ℂˣ) (hz : z ^ n = 1)
    (j : ℕ) :
    scalarResidueHom n hn z hz (Multiplicative.ofAdd (j : ZMod n)) = z ^ j := by
  let : NeZero n := ⟨hn.ne'⟩
  change z ^ (j : ZMod n).val = _
  rw [ZMod.val_natCast]
  exact (pow_eq_pow_mod j hz).symm

@[expose] def primitiveUnit (n : ℕ) (hn : 0 < n) (zeta : ℂ)
    (hroot : IsPrimitiveRoot zeta n) : ℂˣ :=
  Units.mk0 zeta (hroot.ne_zero hn.ne')

theorem primitiveUnit_pow (n : ℕ) (hn : 0 < n) (zeta : ℂ)
    (hroot : IsPrimitiveRoot zeta n) : primitiveUnit n hn zeta hroot ^ n = 1 := by
  apply Units.ext
  exact hroot.pow_eq_one

@[expose] def rootCharacter (n : ℕ) (hn : 0 < n) (zeta : ℂ)
    (hroot : IsPrimitiveRoot zeta n) (r : ℕ) : Multiplicative (ZMod n) →* ℂˣ :=
  scalarResidueHom n hn (primitiveUnit n hn zeta hroot ^ r) (by
    rw [← pow_mul, Nat.mul_comm r n, pow_mul, primitiveUnit_pow, one_pow])

theorem rootCharacter_natCast (n : ℕ) (hn : 0 < n) (zeta : ℂ)
    (hroot : IsPrimitiveRoot zeta n) (r j : ℕ) :
    (rootCharacter n hn zeta hroot r (Multiplicative.ofAdd (j : ZMod n)) : ℂ) =
      zeta ^ (r * j) := by
  rw [rootCharacter, scalarResidueHom_natCast]
  simp only [Units.val_pow_eq_pow_val, primitiveUnit, Units.val_mk0, pow_mul]

end CyclicScalarCharacters

section OriginalLinearCharacters

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
variable [Finite F]
variable (sigma0 : Sigma) (hgen : ∀ sigma : Sigma, sigma ∈ Subgroup.zpowers sigma0)
variable (zetaM zetaD : ℂ) (hrootM : IsPrimitiveRoot zetaM m)
variable (hrootD : IsPrimitiveRoot zetaD (Nat.card Sigma))

@[expose] def fieldGeneratorEquiv : Multiplicative (ZMod (Nat.card Sigma)) ≃* Sigma :=
  zmodMulEquivOfGenerator hgen rfl

@[expose] def quotientLinearCharacter (r : Fin m) (s : Fin (Nat.card Sigma)) :
    Multiplicative (ZMod m) × Sigma →* ℂˣ :=
  ((rootCharacter m hm zetaM hrootM r.val).comp
      (MonoidHom.fst (Multiplicative (ZMod m)) Sigma)) *
    (((rootCharacter (Nat.card Sigma) Nat.card_pos zetaD hrootD s.val).comp
      (fieldGeneratorEquiv F Sigma sigma0 hgen).symm.toMonoidHom).comp
      (MonoidHom.snd (Multiplicative (ZMod m)) Sigma))

@[expose] def linearCharacter (r : Fin m) (s : Fin (Nat.card Sigma)) :
    SemilinearExtension F b m hm heven Sigma hSigma →* ℂˣ :=
  (quotientLinearCharacter F m hm Sigma sigma0 hgen zetaM zetaD hrootM hrootD r s).comp
    (psi F b m hm heven Sigma hSigma)

end OriginalLinearCharacters


section OriginalCharacterFormulas

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
variable [Finite F]
variable (sigma0 : Sigma) (hgen : ∀ sigma : Sigma, sigma ∈ Subgroup.zpowers sigma0)
variable (zetaM zetaD : ℂ) (hrootM : IsPrimitiveRoot zetaM m)
variable (hrootD : IsPrimitiveRoot zetaD (Nat.card Sigma))

omit [Finite F] in
theorem fieldGeneratorEquiv_symm_pow (k : ℕ) :
    (fieldGeneratorEquiv F Sigma sigma0 hgen).symm (sigma0 ^ k) =
      Multiplicative.ofAdd (k : ZMod (Nat.card Sigma)) := by
  rw [map_pow, fieldGeneratorEquiv,
    zmodMulEquivOfGenerator_symm_apply_generator, ← ofAdd_nsmul]
  congr 1
  simp only [nsmul_eq_mul, mul_one]

theorem quotientLinearCharacter_formula (r : Fin m) (s : Fin (Nat.card Sigma))
    (j k : ℕ) :
    (quotientLinearCharacter F m hm Sigma sigma0 hgen zetaM zetaD hrootM hrootD r s
      (Multiplicative.ofAdd (j : ZMod m), sigma0 ^ k) : ℂ) =
      zetaM ^ (r.val * j) * zetaD ^ (s.val * k) := by
  change (rootCharacter m hm zetaM hrootM r.val (Multiplicative.ofAdd (j : ZMod m)) : ℂ) *
    (rootCharacter (Nat.card Sigma) Nat.card_pos zetaD hrootD s.val
      ((fieldGeneratorEquiv F Sigma sigma0 hgen).symm (sigma0 ^ k)) : ℂ) = _
  rw [fieldGeneratorEquiv_symm_pow, rootCharacter_natCast, rootCharacter_natCast]

theorem linearCharacter_formula (r : Fin m) (s : Fin (Nat.card Sigma))
    (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ) :
    (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen zetaM zetaD hrootM hrootD r s
      ⟨quotientClass F b m hm heven X (j : ZMod (2 * m)), sigma0 ^ k⟩ : ℂ) =
      zetaM ^ (r.val * j) * zetaD ^ (s.val * k) := by
  simp only [linearCharacter, MonoidHom.comp_apply, psi_formula, map_natCast]
  exact quotientLinearCharacter_formula F m hm Sigma sigma0 hgen zetaM zetaD
    hrootM hrootD r s j k

theorem linearCharacter_u (r : Fin m) (s : Fin (Nat.card Sigma)) :
    (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen zetaM zetaD hrootM hrootD r s
      (uInH F b m hm heven Sigma hSigma) : ℂ) = zetaM ^ r.val := by
  change (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen
    zetaM zetaD hrootM hrootD r s
      ⟨quotientClass F b m hm heven 1 1, (1 : Sigma)⟩ : ℂ) = _
  have h := linearCharacter_formula F b m hm heven Sigma hSigma sigma0 hgen
    zetaM zetaD hrootM hrootD r s 1 1 0
  simpa only [Nat.cast_one, pow_zero, Nat.mul_one, Nat.mul_zero, mul_one] using h

theorem linearCharacter_sigma0 (r : Fin m) (s : Fin (Nat.card Sigma)) :
    (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen zetaM zetaD hrootM hrootD r s
      (SemidirectProduct.inr sigma0) : ℂ) = zetaD ^ s.val := by
  change (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen
    zetaM zetaD hrootM hrootD r s
      ⟨quotientClass F b m hm heven 1 0, sigma0⟩ : ℂ) = _
  have h := linearCharacter_formula F b m hm heven Sigma hSigma sigma0 hgen
    zetaM zetaD hrootM hrootD r s 1 0 1
  simpa only [Nat.cast_zero, pow_one, Nat.mul_zero, Nat.mul_one, pow_zero, one_mul] using h

theorem linearCharacter_values_injective :
    Function.Injective (fun rs : Fin m × Fin (Nat.card Sigma) =>
      fun h : SemilinearExtension F b m hm heven Sigma hSigma =>
        (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen
          zetaM zetaD hrootM hrootD rs.1 rs.2 h : ℂ)) := by
  rintro ⟨r,s⟩ ⟨r',s'⟩ heq
  apply Prod.ext
  · apply Fin.ext
    apply hrootM.pow_inj r.isLt r'.isLt
    have h := congrFun heq (uInH F b m hm heven Sigma hSigma)
    simpa only [linearCharacter_u] using h
  · apply Fin.ext
    apply hrootD.pow_inj s.isLt s'.isLt
    have h := congrFun heq (SemidirectProduct.inr sigma0)
    simpa only [linearCharacter_sigma0] using h

end OriginalCharacterFormulas


section OriginalCharacterExhaustion

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
variable [Finite F]
variable (sigma0 : Sigma) (hgen : ∀ sigma : Sigma, sigma ∈ Subgroup.zpowers sigma0)
variable (zetaM zetaD : ℂ) (hrootM : IsPrimitiveRoot zetaM m)
variable (hrootD : IsPrimitiveRoot zetaD (Nat.card Sigma))

theorem linearHom_factors (hb : b ≠ 1)
    (f : SemilinearExtension F b m hm heven Sigma hSigma →* ℂˣ) :
    ∃ g : Multiplicative (ZMod m) × Sigma →* ℂˣ,
      g.comp (psi F b m hm heven Sigma hSigma) = f := by
  let e := abelianizationEquiv F b m hm heven Sigma hSigma hb
  refine ⟨(Abelianization.lift f).comp e.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro h
  change Abelianization.lift f (e.symm (psi F b m hm heven Sigma hSigma h)) = f h
  rw [← abelianizationEquiv_of F b m hm heven Sigma hSigma hb,
    MulEquiv.symm_apply_apply, Abelianization.lift_apply_of]

theorem residue_generator (n : ℕ) :
    ∀ j : Multiplicative (ZMod n),
      j ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) := by
  intro j
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective j.toAdd
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  rw [← ofAdd_zsmul]
  apply Multiplicative.toAdd.injective
  change k • (1 : ZMod n) = j.toAdd
  simpa only [zsmul_eq_mul, mul_one] using hk

theorem quotientLinearCharacter_exhaustive
    (g : Multiplicative (ZMod m) × Sigma →* ℂˣ) :
    ∃ r : Fin m, ∃ s : Fin (Nat.card Sigma),
      quotientLinearCharacter F m hm Sigma sigma0 hgen zetaM zetaD hrootM hrootD r s = g := by
  let : NeZero m := ⟨hm.ne'⟩
  have ha : (Multiplicative.ofAdd (1 : ZMod m)) ^ m = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    change m • (1 : ZMod m) = 0
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_self]
  have hgA : (g (Multiplicative.ofAdd (1 : ZMod m), (1 : Sigma)) : ℂ) ^ m = 1 := by
    have h := congrArg g (Prod.ext ha (one_pow m) :
      (Multiplicative.ofAdd (1 : ZMod m), (1 : Sigma)) ^ m = 1)
    have hv := congrArg Units.val h
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using hv
  have hgD : (g ((1 : Multiplicative (ZMod m)), sigma0) : ℂ) ^ Nat.card Sigma = 1 := by
    have h := congrArg g (Prod.ext (one_pow (Nat.card Sigma))
      (pow_card_eq_one' (x := sigma0)) :
      ((1 : Multiplicative (ZMod m)), sigma0) ^ Nat.card Sigma = 1)
    have hv := congrArg Units.val h
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using hv
  obtain ⟨r, hr, hAr⟩ := hrootM.eq_pow_of_pow_eq_one hgA
  obtain ⟨s, hs, hDs⟩ := hrootD.eq_pow_of_pow_eq_one hgD
  refine ⟨⟨r,hr⟩,⟨s,hs⟩,?_⟩
  let q := quotientLinearCharacter F m hm Sigma sigma0 hgen zetaM zetaD
    hrootM hrootD ⟨r,hr⟩ ⟨s,hs⟩
  have hqA : q.comp (MonoidHom.inl (Multiplicative (ZMod m)) Sigma) =
      g.comp (MonoidHom.inl (Multiplicative (ZMod m)) Sigma) := by
    apply (MonoidHom.eq_iff_eq_on_generator (residue_generator m) _ _).mpr
    apply Units.ext
    change (q (Multiplicative.ofAdd (1 : ZMod m), 1) : ℂ) =
      (g (Multiplicative.ofAdd (1 : ZMod m), 1) : ℂ)
    have h := quotientLinearCharacter_formula F m hm Sigma sigma0 hgen zetaM zetaD
      hrootM hrootD ⟨r,hr⟩ ⟨s,hs⟩ 1 0
    simpa only [Nat.cast_one, pow_zero, Nat.mul_one, Nat.mul_zero, mul_one] using
      h.trans (by simpa only [Nat.mul_one, Nat.mul_zero, pow_zero, mul_one] using hAr)
  have hqD : q.comp (MonoidHom.inr (Multiplicative (ZMod m)) Sigma) =
      g.comp (MonoidHom.inr (Multiplicative (ZMod m)) Sigma) := by
    apply (MonoidHom.eq_iff_eq_on_generator hgen _ _).mpr
    apply Units.ext
    change (q (1, sigma0) : ℂ) = (g (1, sigma0) : ℂ)
    have h := quotientLinearCharacter_formula F m hm Sigma sigma0 hgen zetaM zetaD
      hrootM hrootD ⟨r,hr⟩ ⟨s,hs⟩ 0 1
    have h' : (q (1, sigma0) : ℂ) = zetaD ^ s := by
      change (quotientLinearCharacter F m hm Sigma sigma0 hgen zetaM zetaD
        hrootM hrootD ⟨r,hr⟩ ⟨s,hs⟩ (Multiplicative.ofAdd (0 : ZMod m), sigma0) : ℂ) = _
      simpa only [Nat.cast_zero, pow_one, Nat.mul_zero, Nat.mul_one, pow_zero, one_mul] using h
    exact h'.trans hDs
  apply MonoidHom.ext
  intro x
  rcases x with ⟨j,sigma⟩
  change q (j,sigma) = g (j,sigma)
  have hprod : (j,sigma) = (j,1) * (1,sigma) := by simp
  rw [hprod, map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hqA j) (DFunLike.congr_fun hqD sigma)

theorem linearCharacter_exhaustive (hb : b ≠ 1)
    (f : SemilinearExtension F b m hm heven Sigma hSigma →* ℂˣ) :
    ∃ r : Fin m, ∃ s : Fin (Nat.card Sigma),
      linearCharacter F b m hm heven Sigma hSigma sigma0 hgen
        zetaM zetaD hrootM hrootD r s = f := by
  obtain ⟨g,hg⟩ := linearHom_factors F b m hm heven Sigma hSigma hb f
  obtain ⟨r,s,hrs⟩ := quotientLinearCharacter_exhaustive F m hm Sigma sigma0 hgen
    zetaM zetaD hrootM hrootD g
  refine ⟨r,s,?_⟩
  rw [linearCharacter, hrs, hg]

end OriginalCharacterExhaustion


section OneDimensionalRepresentations

theorem representation_isIrreducible_of_finrank_one {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] (rho : Representation ℂ G V)
    (hdim : Module.finrank ℂ V = 1) : rho.IsIrreducible := by
  let : IsSimpleOrder (Submodule ℂ V) :=
    is_simple_module_of_finrank_eq_one (K := ℂ) (A := ℂ) hdim
  have hnontrivial : (⊥ : Subrepresentation rho) ≠ ⊤ := by
    intro heq
    exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule heq)
  let : Nontrivial (Subrepresentation rho) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro W
  rcases eq_bot_or_eq_top W.toSubmodule with hbot | htop
  · exact Or.inl (Subrepresentation.ext hbot)
  · exact Or.inr (Subrepresentation.ext htop)

@[expose] def standardLineRepresentation {G : Type u} [Group G] (f : G →* ℂˣ) :
    Representation ℂ G (Fin 1 → ℂ) where
  toFun g := (f g : ℂ) • 1
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Units.val_mul, smul_mul_smul_comm, one_mul]

theorem standardLineRepresentation_character {G : Type u} [Group G] (f : G →* ℂˣ)
    (g : G) : (standardLineRepresentation f).character g = (f g : ℂ) := by
  change LinearMap.trace ℂ (Fin 1 → ℂ) ((f g : ℂ) • 1) = _
  rw [map_smul, LinearMap.trace_one]
  simp only [Module.finrank_pi, Fintype.card_fin, Nat.cast_one, smul_eq_mul, mul_one]

theorem standardLineRepresentation_isIrreducible {G : Type u} [Group G] (f : G →* ℂˣ) :
    (standardLineRepresentation f).IsIrreducible :=
  representation_isIrreducible_of_finrank_one _ (by
    rw [Module.finrank_pi, Fintype.card_fin])

theorem scalarCharacter_isLinearCharacter {G : Type u} [Group G] (f : G →* ℂˣ) :
    CFSG.Theory.Character.IsLinearCharacter (fun g => (f g : ℂ)) := by
  refine ⟨⟨1, standardLineRepresentation f, standardLineRepresentation_isIrreducible f, ?_⟩,
    ?_⟩
  · funext g
    exact (standardLineRepresentation_character f g).symm
  · simp only [map_one, Units.val_one]

theorem exists_scalarHom_of_isLinearCharacter {G : Type u} [Group G]
    (chi : G → ℂ) (hchi : CFSG.Theory.Character.IsLinearCharacter chi) :
    ∃ f : G →* ℂˣ, ∀ g, (f g : ℂ) = chi g := by
  rcases hchi with ⟨⟨n,rho,_hirr,hchar⟩,hdegree⟩
  let data : CFSG.TwoRankLowerBound.Helpers.FiniteComplexRepresentation.{u,0} G :=
    { vector := Fin n → ℂ, representation := rho }
  have hd : data.character 1 = 1 := by
    change rho.character 1 = 1
    rw [← hchar]
    exact hdegree
  refine ⟨CFSG.Semidihedral.Principal.degreeOneCharacterUnits data hd, ?_⟩
  intro g
  rw [CFSG.Semidihedral.Principal.degreeOneCharacterUnits_val]
  change rho.character g = chi g
  rw [← hchar]

end OneDimensionalRepresentations

section CompleteLinearCharacterFamily

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
variable [Finite F]
variable (sigma0 : Sigma) (hgen : ∀ sigma : Sigma, sigma ∈ Subgroup.zpowers sigma0)
variable (zetaM zetaD : ℂ) (hrootM : IsPrimitiveRoot zetaM m)
variable (hrootD : IsPrimitiveRoot zetaD (Nat.card Sigma))

theorem linearCharacter_isLinearCharacter (r : Fin m) (s : Fin (Nat.card Sigma)) :
    CFSG.Theory.Character.IsLinearCharacter (fun h =>
      (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen
        zetaM zetaD hrootM hrootD r s h : ℂ)) :=
  scalarCharacter_isLinearCharacter _

theorem degree_one_irreducible_character_exhaustive (hb : b ≠ 1)
    (chi : SemilinearExtension F b m hm heven Sigma hSigma → ℂ)
    (hchi : CFSG.Theory.Character.IsLinearCharacter chi) :
    ∃! rs : Fin m × Fin (Nat.card Sigma), ∀ h,
      (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen
        zetaM zetaD hrootM hrootD rs.1 rs.2 h : ℂ) = chi h := by
  obtain ⟨f,hf⟩ := exists_scalarHom_of_isLinearCharacter chi hchi
  obtain ⟨r,s,hrs⟩ := linearCharacter_exhaustive F b m hm heven Sigma hSigma sigma0 hgen
    zetaM zetaD hrootM hrootD hb f
  refine ⟨(r,s), ?_, ?_⟩
  · intro h
    rw [hrs]
    exact hf h
  · intro rs hrs'
    apply linearCharacter_values_injective F b m hm heven Sigma hSigma sigma0 hgen
      zetaM zetaD hrootM hrootD
    funext h
    change (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen zetaM zetaD
      hrootM hrootD rs.1 rs.2 h : ℂ) =
        (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen zetaM zetaD
          hrootM hrootD r s h : ℂ)
    exact (hrs' h).trans (by rw [hrs]; exact (hf h).symm)

@[expose] def linearCharacterEquiv (hb : b ≠ 1) :
    (Fin m × Fin (Nat.card Sigma)) ≃
      {chi : SemilinearExtension F b m hm heven Sigma hSigma → ℂ //
        CFSG.Theory.Character.IsLinearCharacter chi} :=
  Equiv.ofBijective (fun rs =>
    ⟨fun h => (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen
      zetaM zetaD hrootM hrootD rs.1 rs.2 h : ℂ),
      linearCharacter_isLinearCharacter F b m hm heven Sigma hSigma sigma0 hgen
        zetaM zetaD hrootM hrootD rs.1 rs.2⟩) (by
    constructor
    · intro a a' heq
      exact linearCharacter_values_injective F b m hm heven Sigma hSigma sigma0 hgen
        zetaM zetaD hrootM hrootD (congrArg Subtype.val heq)
    · rintro ⟨chi,hchi⟩
      obtain ⟨rs,hrs,_hunique⟩ := degree_one_irreducible_character_exhaustive F b m hm heven
        Sigma hSigma sigma0 hgen zetaM zetaD hrootM hrootD hb chi hchi
      exact ⟨rs, Subtype.ext (funext hrs)⟩)

include sigma0 hgen zetaM zetaD hrootM hrootD in
theorem degree_one_irreducible_character_card (hb : b ≠ 1) :
    Nat.card {chi : SemilinearExtension F b m hm heven Sigma hSigma → ℂ //
      CFSG.Theory.Character.IsLinearCharacter chi} = m * Nat.card Sigma := by
  rw [Nat.card_congr (linearCharacterEquiv F b m hm heven Sigma hSigma sigma0 hgen
    zetaM zetaD hrootM hrootD hb).symm, Nat.card_prod,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin]

end CompleteLinearCharacterFamily


section AllOriginalRepresentativeValues

theorem scalarResidueHom_intCast (n : ℕ) (hn : 0 < n) (z : ℂˣ) (hz : z ^ n = 1)
    (j : ℤ) :
    scalarResidueHom n hn z hz (Multiplicative.ofAdd (j : ZMod n)) = z ^ j := by
  have hone : scalarResidueHom n hn z hz (Multiplicative.ofAdd (1 : ZMod n)) = z := by
    simpa only [Nat.cast_one, pow_one] using scalarResidueHom_natCast n hn z hz 1
  have hj : Multiplicative.ofAdd (j : ZMod n) =
      (Multiplicative.ofAdd (1 : ZMod n)) ^ j := by
    rw [← ofAdd_zsmul]
    apply Multiplicative.toAdd.injective
    change (j : ZMod n) = j • (1 : ZMod n)
    simp only [zsmul_eq_mul, mul_one]
  rw [hj, map_zpow, hone]

theorem rootCharacter_intCast (n : ℕ) (hn : 0 < n) (zeta : ℂ)
    (hroot : IsPrimitiveRoot zeta n) (r : ℕ) (j : ℤ) :
    (rootCharacter n hn zeta hroot r (Multiplicative.ofAdd (j : ZMod n)) : ℂ) =
      zeta ^ ((r : ℤ) * j) := by
  rw [rootCharacter, scalarResidueHom_intCast, Units.val_zpow_eq_zpow_val,
    Units.val_pow_eq_pow_val]
  change (zeta ^ r) ^ j = zeta ^ ((r : ℤ) * j)
  rw [← zpow_natCast, ← _root_.zpow_mul]

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
variable [Finite F]
variable (sigma0 : Sigma) (hgen : ∀ sigma : Sigma, sigma ∈ Subgroup.zpowers sigma0)
variable (zetaM zetaD : ℂ) (hrootM : IsPrimitiveRoot zetaM m)
variable (hrootD : IsPrimitiveRoot zetaD (Nat.card Sigma))

theorem linearCharacter_residue_formula (r : Fin m) (s : Fin (Nat.card Sigma))
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (k : ℕ) :
    (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen zetaM zetaD hrootM hrootD r s
      ⟨quotientClass F b m hm heven X j, sigma0 ^ k⟩ : ℂ) =
      zetaM ^ (r.val * j.val) * zetaD ^ (s.val * k) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  simpa only [ZMod.natCast_zmod_val] using linearCharacter_formula F b m hm heven
    Sigma hSigma sigma0 hgen zetaM zetaD hrootM hrootD r s X j.val k

theorem linearCharacter_integer_formula (r : Fin m) (s : Fin (Nat.card Sigma))
    (X : SpecialLinearGroup (Fin 2) F) (j k : ℤ) :
    (linearCharacter F b m hm heven Sigma hSigma sigma0 hgen zetaM zetaD hrootM hrootD r s
      ⟨quotientClass F b m hm heven X (j : ZMod (2 * m)), sigma0 ^ k⟩ : ℂ) =
      zetaM ^ ((r.val : ℤ) * j) * zetaD ^ ((s.val : ℤ) * k) := by
  have hfield : (fieldGeneratorEquiv F Sigma sigma0 hgen).symm (sigma0 ^ k) =
      Multiplicative.ofAdd (k : ZMod (Nat.card Sigma)) :=
    zmodMulEquivOfGenerator_symm_apply_zpow hgen rfl k
  change (rootCharacter m hm zetaM hrootM r.val
    (Multiplicative.ofAdd (ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      (j : ZMod (2 * m)))) : ℂ) *
    (rootCharacter (Nat.card Sigma) Nat.card_pos zetaD hrootD s.val
      ((fieldGeneratorEquiv F Sigma sigma0 hgen).symm (sigma0 ^ k)) : ℂ) = _
  rw [map_intCast, hfield, rootCharacter_intCast, rootCharacter_intCast]

end AllOriginalRepresentativeValues


section OriginalCanonicalStatement

theorem nonsquare_ne_one (b : Fˣ) (hb : ¬ IsSquare b) : b ≠ 1 := by
  rintro rfl
  exact hb IsSquare.one

omit [Field F] in
theorem finite_of_original_field_card (p f : ℕ) (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) : Finite F :=
  Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero f hp.ne_zero))

theorem central_SL2_model_derived_subgroup_and_linear_characters
    (p f : ℕ) (hp : p.Prime) (_hodd : Odd p) (_hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (b : Fˣ) (hb : ¬ IsSquare b)
    (m : ℕ) (hm : 2 ≤ m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b) :
    let hmpos : 0 < m := by omega
    let H := SemilinearExtension F b m hmpos heven Sigma hSigma
    let M := matrixLayer F b m hmpos heven Sigma hSigma
    Function.Injective (matrixInclusion F b m hmpos heven Sigma hSigma) ∧
    commutator H = M ∧
    Function.Surjective (psi F b m hmpos heven Sigma hSigma) ∧
    (psi F b m hmpos heven Sigma hSigma).ker = M ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (sigma : Sigma),
      psi F b m hmpos heven Sigma hSigma ⟨quotientClass F b m hmpos heven X j, sigma⟩ =
        (Multiplicative.ofAdd (ZMod.castHom (dvd_mul_left m 2) (ZMod m) j), sigma)) ∧
    (∃ e : Abelianization H ≃* Multiplicative (ZMod m) × Sigma,
      ∀ h, e (Abelianization.of h) = psi F b m hmpos heven Sigma hSigma h) ∧
    IsCyclic Sigma ∧
    Nat.card (Abelianization H) = m * Nat.card Sigma ∧
    (Nat.Coprime m (Nat.card Sigma) → IsCyclic (Abelianization H)) ∧
    (∀ a : ℕ, m = 2 ^ a → Odd (Nat.card Sigma) → IsCyclic (Abelianization H)) ∧
    (∀ (sigma0 : Sigma), (∀ sigma : Sigma, sigma ∈ Subgroup.zpowers sigma0) →
      ∀ (zetaM zetaD : ℂ), IsPrimitiveRoot zetaM m →
      IsPrimitiveRoot zetaD (Nat.card Sigma) →
      ∃ family : (Fin m × Fin (Nat.card Sigma)) ≃
          {chi : H → ℂ // CFSG.Theory.Character.IsLinearCharacter chi},
        (∀ (rs : Fin m × Fin (Nat.card Sigma)) (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
          (family rs).val
              ⟨quotientClass F b m hmpos heven X (j : ZMod (2 * m)), sigma0 ^ k⟩ =
            zetaM ^ (rs.1.val * j) * zetaD ^ (rs.2.val * k)) ∧
        Function.Injective (fun rs => (family rs).val) ∧
        Nat.card {chi : H → ℂ // CFSG.Theory.Character.IsLinearCharacter chi} =
          m * Nat.card Sigma) := by
  let : Finite F := finite_of_original_field_card F p f hp hcard
  have hb1 := nonsquare_ne_one F b hb
  dsimp only
  refine ⟨matrixInclusion_injective F b m (by omega) heven Sigma hSigma,
    derived_eq_matrixLayer F b m (by omega) heven Sigma hSigma hb1,
    psi_surjective F b m (by omega) heven Sigma hSigma,
    psi_ker F b m (by omega) heven Sigma hSigma,
    psi_formula F b m (by omega) heven Sigma hSigma,
    ⟨abelianizationEquiv F b m (by omega) heven Sigma hSigma hb1,
      abelianizationEquiv_of F b m (by omega) heven Sigma hSigma hb1⟩,
    fieldSubgroup_isCyclic F Sigma,
    abelianization_card F b m (by omega) heven Sigma hSigma hb1,
    abelianization_isCyclic F b m (by omega) heven Sigma hSigma hb1,
    abelianization_isCyclic_of_two_power F b m (by omega) heven Sigma hSigma hb1, ?_⟩
  intro sigma0 hgen zetaM zetaD hrootM hrootD
  let family := linearCharacterEquiv F b m (by omega) heven Sigma hSigma
    sigma0 hgen zetaM zetaD hrootM hrootD hb1
  refine ⟨family, ?_, ?_, ?_⟩
  · intro rs X j k
    exact linearCharacter_formula F b m (by omega) heven Sigma hSigma sigma0 hgen
      zetaM zetaD hrootM hrootD rs.1 rs.2 X j k
  · exact Subtype.val_injective.comp family.injective
  · exact degree_one_irreducible_character_card F b m (by omega) heven Sigma hSigma
      sigma0 hgen zetaM zetaD hrootM hrootD hb1

end OriginalCanonicalStatement

end CFSG.Wreathed.CentralSL2Abelianization
