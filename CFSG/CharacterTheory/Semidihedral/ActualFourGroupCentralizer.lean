module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupAlignment

public noncomputable section

namespace CFSG.Semidihedral.ActualFourGroupCentralizer

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

universe u v

theorem odd_field_generator_nonsquare (F : Type u) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) :
    ∃ a : Fˣ, (∀ x : Fˣ, x ∈ Subgroup.zpowers a) ∧ ¬IsSquare a := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨a, ha, ?_⟩
  have horder : orderOf a = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers ha
  have heven : 2 ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    have hpos : 0 < Nat.card F := Nat.card_pos
    have ho := Nat.odd_iff.mp hodd
    omega
  rintro ⟨b, hb⟩
  have hab : a = b ^ 2 := by simpa only [pow_two] using hb
  have hbcard : orderOf b = Nat.card Fˣ := by
    apply Nat.dvd_antisymm (orderOf_dvd_natCard b)
    rw [← horder, hab]
    exact orderOf_pow_dvd 2
  have hbdiv : 2 ∣ orderOf b := hbcard.symm ▸ heven
  rw [hab, orderOf_pow_of_dvd (by decide : (2 : ℕ) ≠ 0) hbdiv, hbcard] at horder
  have hpos : 0 < Nat.card Fˣ := Nat.card_pos
  omega

variable (F : Type u) [Field F] (A : Subgroup (F ≃+* F))

theorem fixed_coefficient_action (a : (MatrixCover.FixedField F A)ˣ) (sigma : A) :
    (sigma : F ≃+* F) (MatrixCover.fixedUnit F A a : F) =
      MatrixCover.fixedUnit F A a :=
  (a : MatrixCover.FixedField F A).property sigma

theorem original_coefficient_fixedUnit (a : (MatrixCover.FixedField F A)ˣ) :
    MatrixTorus.originalCoefficient F (MatrixCover.fixedUnit F A a) A
      (fixed_coefficient_action F A a) = a :=
  Units.ext (Subtype.ext rfl)

@[expose] def coefficientModelEquiv (a b : (MatrixCover.FixedField F A)ˣ)
    (hab : a = b) : MatrixCover.MatrixFieldModel F A a ≃*
      MatrixCover.MatrixFieldModel F A b := hab ▸ MulEquiv.refl _

theorem coefficientModelEquiv_coordinates (a b : (MatrixCover.FixedField F A)ˣ)
    (hab : a = b) (x : MatrixCover.MatrixFieldModel F A a) :
    (coefficientModelEquiv F A a b hab x).left.left = x.left.left ∧
      (coefficientModelEquiv F A a b hab x).left.right = x.left.right ∧
      (coefficientModelEquiv F A a b hab x).right = x.right := by
  subst b
  exact ⟨rfl, rfl, rfl⟩

@[expose] def fixedModelEquiv (a : (MatrixCover.FixedField F A)ˣ) :
    MatrixCover.MatrixFieldModel F A a ≃*
      MatrixTorus.OriginalH F (MatrixCover.fixedUnit F A a) A
        (fixed_coefficient_action F A a) :=
  (coefficientModelEquiv F A a
    (MatrixTorus.originalCoefficient F (MatrixCover.fixedUnit F A a) A
      (fixed_coefficient_action F A a)) (original_coefficient_fixedUnit F A a).symm).trans
    (MatrixTorus.originalModelEquiv F (MatrixCover.fixedUnit F A a) A
      (fixed_coefficient_action F A a))

theorem fixedModelEquiv_coordinates (a : (MatrixCover.FixedField F A)ˣ)
    (x : MatrixCover.MatrixFieldModel F A a) :
    (fixedModelEquiv F A a x).left.left = x.left.left ∧
      (fixedModelEquiv F A a x).left.right = x.left.right ∧
      (fixedModelEquiv F A a x).right = x.right := by
  have h := coefficientModelEquiv_coordinates F A a
    (MatrixTorus.originalCoefficient F (MatrixCover.fixedUnit F A a) A
      (fixed_coefficient_action F A a)) (original_coefficient_fixedUnit F A a).symm x
  exact h

theorem fixedModelEquiv_u (a : (MatrixCover.FixedField F A)ˣ) :
    fixedModelEquiv F A a (MatrixTorus.uInH F A a) =
      MatrixTorus.originalU F (MatrixCover.fixedUnit F A a) A
        (fixed_coefficient_action F A a) := by
  apply SemidirectProduct.ext
  · apply SemidirectProduct.ext
    · exact (fixedModelEquiv_coordinates F A a _).1
    · exact (fixedModelEquiv_coordinates F A a _).2.1
  · exact (fixedModelEquiv_coordinates F A a _).2.2

theorem fixedModelEquiv_z (a : (MatrixCover.FixedField F A)ˣ) :
    fixedModelEquiv F A a (MatrixTorus.zInH F A a) =
      MatrixTorus.originalZ F (MatrixCover.fixedUnit F A a) A
        (fixed_coefficient_action F A a) := by
  apply SemidirectProduct.ext
  · apply SemidirectProduct.ext
    · exact (fixedModelEquiv_coordinates F A a _).1
    · exact (fixedModelEquiv_coordinates F A a _).2.1
  · exact (fixedModelEquiv_coordinates F A a _).2.2

theorem original_odd_le_centralizer (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    MatrixTorus.originalOddSemilinear F a A hfix ≤
      Subgroup.centralizer {MatrixTorus.originalU F a A hfix} := by
  rintro x ⟨y, hy, rfl⟩
  have h := Subgroup.mem_centralizer_singleton_iff.mp
    (MatrixTorus.OddSemilinear_le_centralizer F A
      (MatrixTorus.originalCoefficient F a A hfix) hy)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  simpa only [map_mul, MulEquiv.coe_toMonoidHom, MatrixTorus.originalModelEquiv_u] using
    congrArg (MatrixTorus.originalModelEquiv F a A hfix) h

theorem original_odd_card [Finite F] (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    Nat.card (MatrixTorus.originalOddSemilinear F a A hfix) =
      Nat.card A * (MatrixTorus.torusSize (Nat.card F) / 2) := by
  rw [← Nat.card_congr (MatrixTorus.originalOddEquiv F a A hfix).toEquiv,
    ← Nat.card_congr (MatrixTorus.oddFactorEquiv F A
      (MatrixTorus.originalCoefficient F a A hfix)).toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    MatrixTorus.originalCoefficient_literal, MatrixTorus.W_card F a hodd ha]
  exact Nat.mul_comm _ _

theorem original_odd_odd [Finite F] (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    Odd (Nat.card (MatrixTorus.originalOddSemilinear F a A hfix)) := by
  rw [original_odd_card F A a hfix hodd ha]
  exact hA.mul (MatrixTorus.torusSize_half_odd hodd)

theorem original_model_card [Finite F] (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    Nat.card (MatrixTorus.OriginalH F a A hfix) =
      2 * Nat.card A * Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← Nat.card_congr (MatrixTorus.originalModelEquiv F a A hfix).toEquiv]
  exact MatrixTorus.semilinear_card F A (MatrixTorus.originalCoefficient F a A hfix)

theorem original_centralizer_card [Finite F] (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    Nat.card (Subgroup.centralizer {MatrixTorus.originalU F a A hfix}) =
      2 * Nat.card A * MatrixTorus.torusSize (Nat.card F) := by
  rw [← Nat.card_congr (MatrixTorus.originalCentralizerEquiv F a A hfix).toEquiv]
  apply MatrixTorus.semilinear_centralizer_card F A
    (MatrixTorus.originalCoefficient F a A hfix) hodd
  rw [MatrixTorus.originalCoefficient_literal]
  exact ha

@[expose] def centralizerEquiv {P : Type u} {Q : Type v} [Group P] [Group Q]
    (e : P ≃* Q) (x : P) (y : Q) (hxy : e x = y) :
    Subgroup.centralizer {x} ≃* Subgroup.centralizer {y} where
  toFun z := ⟨e z, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg e (Subgroup.mem_centralizer_singleton_iff.mp z.property)
    simpa only [map_mul, hxy] using h⟩
  invFun z := ⟨e.symm z, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, hxy, MulEquiv.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp z.property⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z)
  right_inv z := Subtype.ext (e.apply_symm_apply z)
  map_mul' z w := Subtype.ext (e.map_mul z w)

theorem centralizerEquiv_value {P : Type u} {Q : Type v} [Group P] [Group Q]
    (e : P ≃* Q) (x : P) (y : Q) (hxy : e x = y)
    (z : Subgroup.centralizer {x}) : (centralizerEquiv e x y hxy z : Q) = e z := rfl

@[expose] def intersectionSwapEquiv {P : Type u} [Group P] (J K : Subgroup P) :
    J.subgroupOf K ≃* K.subgroupOf J where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv x := Subtype.ext (Subtype.ext (show x.val.val = x.val.val from rfl))
  right_inv x := Subtype.ext (Subtype.ext (show x.val.val = x.val.val from rfl))
  map_mul' x y := Subtype.ext (Subtype.ext
    (show x.val.val * y.val.val = x.val.val * y.val.val from rfl))

variable {G : Type u} [Group G]

abbrev D {t : G} (s : C t) := KleinFourOddKernel.centralizer s

abbrev V {t : G} (s : C t) := KleinFourOddKernel.fourSubgroup (tInC t) s

abbrev R {t : G} (s : C t) := CFSG.piCore KleinFourOddKernel.oddPrimes (D s)

abbrev N0 {t : G} (s : C t) := (D s).subgroupOf (N t)

abbrev N0InR {t : G} (s : C t) := KleinFourOddKernel.oddKernelIntersection (N t) s

theorem D_map_ambient {t : G} (s : C t) :
    (D s).map (C t).subtype = C t ⊓ Subgroup.centralizer {(s : G)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
  · rintro ⟨hx, hsx⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hsx)), rfl⟩

theorem V_map_ambient {t : G} (s : C t) :
    (V s).map (C t).subtype = Subgroup.zpowers t ⊔ Subgroup.zpowers (s : G) := by
  rw [V, KleinFourOddKernel.fourSubgroup, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

@[expose] def N0EquivCore [Finite G] {t : G} (s : C t) : N0 s ≃* N0InR s :=
  (intersectionSwapEquiv (D s) (N t)).trans
    (Subgroup.subgroupOfEquivOfLe (KleinFourOddKernel.centralizerKernel_le_oddKernel
      (N t) (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) s)).symm

theorem N0_card [Finite G] {t : G} (s : C t) :
    Nat.card (N0InR s) = Nat.card (N0 s) :=
  (Nat.card_congr (N0EquivCore s).toEquiv).symm

theorem N0_index_card {t : G} (s : C t) :
    Nat.card (N t) = Nat.card (N0 s) * (N0 s).index :=
  (N0 s).card_mul_index.symm

@[expose] def originalWAction (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    A →* MulAut (MatrixTorus.W F a) where
  toFun sigma := MatrixTorus.WFieldEquiv F a sigma (hfix sigma)
  map_one' := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    rfl
  map_mul' sigma tau := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    apply Subtype.ext
    exact DFunLike.congr_fun (MatrixCover.slFieldEquiv_mul F sigma tau) X.val.val

abbrev OriginalWProduct (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :=
  SemidirectProduct (MatrixTorus.W F a) A (originalWAction F A a hfix)

@[expose] def originalOddProductEquiv [Finite F] (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    MatrixTorus.originalOddSemilinear F a A hfix ≃* OriginalWProduct F A a hfix := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ :=
    MatrixTorus.nonsquare_matrix_semilinear_involution_centralizer F a A hfix hodd ha
  exact Classical.choice h

@[expose] def B {t : G} (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t) : Subgroup (H t) :=
  (MatrixTorus.originalOddSemilinear F a A hfix).map Psi.toMonoidHom

theorem B_le_centralizer {t : G} (s : C t) (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s) :
    B F A a hfix Psi ≤ Subgroup.centralizer {nu t s} := by
  rintro x ⟨y, hy, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := congrArg Psi (Subgroup.mem_centralizer_singleton_iff.mp
    (original_odd_le_centralizer F A a hfix hy))
  simpa only [map_mul, MulEquiv.coe_toMonoidHom, hPsi] using h

theorem B_card [Finite F] {t : G} (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    Nat.card (B F A a hfix Psi) =
      Nat.card A * (MatrixTorus.torusSize (Nat.card F) / 2) := by
  rw [B, Subgroup.card_map_of_injective (by
    simpa only [MulEquiv.coe_toMonoidHom] using Psi.injective)]
  exact original_odd_card F A a hfix hodd ha

theorem B_odd [Finite F] {t : G} (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    Odd (Nat.card (B F A a hfix Psi)) := by
  rw [B_card F A a hfix Psi hodd ha]
  exact hA.mul (MatrixTorus.torusSize_half_odd hodd)

@[expose] def BOddEquiv [Finite F] {t : G} (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    B F A a hfix Psi ≃* OriginalWProduct F A a hfix :=
  (Subgroup.equivMapOfInjective _ Psi.toMonoidHom (by
    simpa only [MulEquiv.coe_toMonoidHom] using Psi.injective)).symm.trans
      (originalOddProductEquiv F A a hfix hodd ha)

theorem original_quotient_centralizer_card [Finite F] {t : G} (s : C t) (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    Nat.card (Subgroup.centralizer {nu t s}) =
      2 * Nat.card A * MatrixTorus.torusSize (Nat.card F) :=
  (Nat.card_congr (centralizerEquiv Psi (MatrixTorus.originalU F a A hfix)
    (nu t s) hPsi).toEquiv).symm.trans (original_centralizer_card F A a hfix hodd ha)

theorem original_quotient_internal_direct [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    KleinFourOddKernel.IsInternalDirectProduct
      (KleinFourOddKernel.quotientFourInCentralizer (N t) (tInC t) s)
      (KleinFourOddKernel.quotientOddInCentralizer (N t) s (B F A a hfix Psi)) := by
  have hN : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have htC : orderOf (tInC t) = 2 := (Subgroup.orderOf_coe (tInC t)).symm.trans ht
  have hB := B_le_centralizer F A s a hfix Psi hPsi
  have hBodd := B_odd F A a hfix Psi hodd ha hA
  have hfour := KleinFourOddKernel.quotientFourInCentralizer_card
    (N t) hN (tInC t) s (tInC_central t) htC hs hst.symm
  have hoddcard := KleinFourOddKernel.quotientOddInCentralizer_card (N t) s _ hB
  refine ⟨Subgroup.isComplement'_of_coprime ?_ ?_, ?_⟩
  · rw [hfour, hoddcard, B_card F A a hfix Psi hodd ha,
      original_quotient_centralizer_card F A s a hfix Psi hPsi hodd ha]
    nth_rw 2 [MatrixTorus.torusSize_two_mul_half hodd]
    ring
  · rw [hfour, hoddcard]
    exact (show Nat.Coprime (2 ^ 2) (Nat.card (B F A a hfix Psi)) from
      hBodd.coprime_two_left.pow_left 2)
  · intro v b
    exact (Subgroup.mem_center_iff.mp
      (KleinFourOddKernel.quotientFourInCentralizer_central (N t) hN (tInC t) s
        (tInC_central t) htC hs v.property) b).symm

theorem actual_lifted_conclusion [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    KleinFourOddKernel.LiftedCentralizerConclusion (N t) (tInC t) s
      (B F A a hfix Psi) :=
  KleinFourOddKernel.odd_kernel_central_Klein_four_centralizer_lifting (N t)
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) (tInC t) s (tInC_central t)
    ((Subgroup.orderOf_coe (tInC t)).symm.trans ht) hs hst.symm _
    (B_le_centralizer F A s a hfix Psi hPsi) (B_odd F A a hfix Psi hodd ha hA)
    (original_quotient_internal_direct F A ht s hs hst a hfix Psi hPsi hodd ha hA)

@[expose] def originalOddInclusion (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    OriginalWProduct F A a hfix →* MatrixTorus.OriginalH F a A hfix :=
  SemidirectProduct.map (MatrixTorus.WInM F a) (MonoidHom.id A) (by
    intro sigma
    apply MonoidHom.ext
    intro X
    apply SemidirectProduct.ext <;> rfl)

theorem originalOddInclusion_coordinates (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (x : OriginalWProduct F A a hfix) :
    originalOddInclusion F A a hfix x = ⟨⟨x.left.val.val, 1⟩, x.right⟩ := rfl

theorem originalOddInclusion_injective (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    Function.Injective (originalOddInclusion F A a hfix) := by
  intro x y h
  apply SemidirectProduct.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g : MatrixTorus.OriginalH F a A hfix => g.left.left) h
  · exact congrArg (fun g : MatrixTorus.OriginalH F a A hfix => g.right) h

theorem originalOddInclusion_range (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    (originalOddInclusion F A a hfix).range =
      MatrixTorus.originalOddSemilinear F a A hfix := by
  let b := MatrixCover.fixedUnit F A (MatrixTorus.originalCoefficient F a A hfix)
  have hb : b = a := MatrixTorus.originalCoefficient_literal F a A hfix
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    let y : MatrixTorus.Torus F b := ⟨x.left.val.val,
      (congrArg (fun c : Fˣ => x.left.val.val ∈ MatrixTorus.Torus F c) hb).mpr
        x.left.val.property⟩
    have hy : y ∈ MatrixTorus.W F b := by
      apply (MatrixTorus.mem_W_iff F b y).mpr
      apply Subtype.ext
      exact congrArg Subtype.val
        ((MatrixTorus.mem_W_iff F a x.left.val).mp x.left.property)
    let w : MatrixTorus.W F b := ⟨y, hy⟩
    refine ⟨MatrixTorus.oddFactor F A (MatrixTorus.originalCoefficient F a A hfix)
      ⟨w, x.right⟩, ⟨⟨w, x.right⟩, rfl⟩, ?_⟩
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext <;> rfl
    · rfl
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    let z : MatrixTorus.Torus F a := ⟨x.left.val.val,
      (congrArg (fun c : Fˣ => x.left.val.val ∈ MatrixTorus.Torus F c) hb).mp
        x.left.val.property⟩
    have hz : z ∈ MatrixTorus.W F a := by
      apply (MatrixTorus.mem_W_iff F a z).mpr
      apply Subtype.ext
      exact congrArg Subtype.val
        ((MatrixTorus.mem_W_iff F b x.left.val).mp x.left.property)
    let w : MatrixTorus.W F a := ⟨z, hz⟩
    refine ⟨⟨w, x.right⟩, ?_⟩
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext <;> rfl
    · rfl

theorem B_original_range {t : G} (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t) :
    B F A a hfix Psi =
      (Psi.toMonoidHom.comp (originalOddInclusion F A a hfix)).range := by
  rw [B, ← originalOddInclusion_range F A a hfix, MonoidHom.range_comp]

theorem actual_C_card [Finite F] {t : G} (s : C t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t) :
    Nat.card (C t) = 2 * Nat.card (N0 s) * (N0 s).index * Nat.card A *
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hH : Nat.card (H t) = 2 * Nat.card A * Nat.card F * (Nat.card F ^ 2 - 1) :=
    (Nat.card_congr Psi.toEquiv).symm.trans (original_model_card F A a hfix)
  rw [← (N t).card_mul_index, (N t).index_eq_card, N0_index_card s, hH]
  ring

theorem actual_R_card [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    Nat.card (R s) =
      Nat.card (N0 s) * Nat.card A * MatrixTorus.torusSize (Nat.card F) / 2 := by
  have h := (actual_lifted_conclusion F A ht s hs hst a hfix Psi hPsi hodd ha hA).core_order
  rw [N0_card s, B_card F A a hfix Psi hodd ha] at h
  change Nat.card (KleinFourOddKernel.oddKernel s) = _
  rw [h, ← Nat.mul_assoc]
  exact (Nat.mul_div_assoc _
    (show 2 ∣ MatrixTorus.torusSize (Nat.card F) from
      ⟨MatrixTorus.torusSize (Nat.card F) / 2,
        MatrixTorus.torusSize_two_mul_half hodd⟩)).symm

theorem actual_D_card [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    Nat.card (D s) =
      2 * Nat.card (N0 s) * Nat.card A * MatrixTorus.torusSize (Nat.card F) := by
  have h := (actual_lifted_conclusion F A ht s hs hst a hfix Psi hPsi hodd ha hA).centralizer_order
  rw [N0_card s, B_card F A a hfix Psi hodd ha] at h
  rw [h]
  nth_rw 2 [MatrixTorus.torusSize_two_mul_half hodd]
  ring

theorem prime_not_dvd_torusSize (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ¬p ∣ MatrixTorus.torusSize (p ^ f) := by
  have hq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hqpos : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  unfold MatrixTorus.torusSize
  split_ifs
  · intro h
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hq).mpr h)
  · intro h
    exact hp.not_dvd_one ((Nat.dvd_sub_iff_right (by omega) hq).mp h)

theorem prime_not_dvd_square_sub_one (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ¬p ∣ (p ^ f) ^ 2 - 1 := by
  have hq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hq2 : p ∣ (p ^ f) ^ 2 := hq.trans (dvd_pow_self _ (by decide))
  have hqpos : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hsq : 1 ≤ (p ^ f) ^ 2 := by nlinarith
  intro h
  exact hp.not_dvd_one ((Nat.dvd_sub_iff_right hsq hq2).mp h)

theorem four_group_order_valuations (p f a b h : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    padicValNat p (2 * a * b * h * p ^ f * ((p ^ f) ^ 2 - 1)) =
      padicValNat p a + padicValNat p b + padicValNat p h + f ∧
    padicValNat p (2 * a * h * MatrixTorus.torusSize (p ^ f)) =
      padicValNat p a + padicValNat p h := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h
    exact (by decide : ¬Odd (2 : ℕ)) (h ▸ hpodd)
  have ht : padicValNat p 2 = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp
      Nat.prime_two).mp h))
  have hqpos : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hq : p ^ f ≠ 0 := by omega
  have hsq : (p ^ f) ^ 2 - 1 ≠ 0 := by
    have h : 1 < (p ^ f) ^ 2 := by nlinarith
    omega
  have htor : MatrixTorus.torusSize (p ^ f) ≠ 0 := by
    unfold MatrixTorus.torusSize
    split_ifs <;> omega
  have hvq : padicValNat p (p ^ f) = f := padicValNat.prime_pow f
  have hvsq : padicValNat p ((p ^ f) ^ 2 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (prime_not_dvd_square_sub_one p f hp hf)
  have hvtor : padicValNat p (MatrixTorus.torusSize (p ^ f)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (prime_not_dvd_torusSize p f hp hf)
  constructor
  · simp only [padicValNat.mul (by positivity :
      2 * a * b * h * p ^ f ≠ 0) hsq,
      padicValNat.mul (by positivity : 2 * a * b * h ≠ 0) hq,
      padicValNat.mul (by positivity : 2 * a * b ≠ 0) hh,
      padicValNat.mul (by positivity : 2 * a ≠ 0) hb,
      padicValNat.mul (by decide : (2 : ℕ) ≠ 0) ha, ht, hvq, hvsq,
      zero_add, add_zero]
  · simp only [padicValNat.mul (by positivity : 2 * a * h ≠ 0) htor,
      padicValNat.mul (by positivity : 2 * a ≠ 0) hh,
      padicValNat.mul (by decide : (2 : ℕ) ≠ 0) ha, ht, hvtor, zero_add, add_zero]

theorem four_group_order_valuation_identity (p f a b h : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    3 * padicValNat p (2 * a * b * h * p ^ f * ((p ^ f) ^ 2 - 1)) -
      2 * padicValNat p (2 * a * h * MatrixTorus.torusSize (p ^ f)) =
        padicValNat p a + 3 * padicValNat p b + padicValNat p h + 3 * f := by
  obtain ⟨hC, hD⟩ := four_group_order_valuations p f a b h hp hpodd hf ha hb hh
  rw [hC, hD]
  omega

theorem actual_valuation_identity [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) :
    3 * padicValNat p (Nat.card (C t)) - 2 * padicValNat p (Nat.card (D s)) =
      padicValNat p (Nat.card (N0 s)) + 3 * padicValNat p (N0 s).index +
        padicValNat p (Nat.card A) + 3 * f := by
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  rw [actual_C_card F A s a hfix Psi,
    actual_D_card F A ht s hs hst a hfix Psi hPsi hodd ha hA, hcard]
  exact four_group_order_valuation_identity p f (Nat.card (N0 s)) (N0 s).index
    (Nat.card A) hp hpodd hf (Nat.card_pos.ne') Subgroup.index_ne_zero_of_finite
    (by have ho := Nat.odd_iff.mp hA; omega)

abbrev QuotientV {t : G} (s : C t) := (V s).map (nu t)

@[expose] def actualQuotientDirectEquiv [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    QuotientV s × B F A a hfix Psi ≃* Subgroup.centralizer {nu t s} :=
  ((Subgroup.subgroupOfEquivOfLe
    (KleinFourOddKernel.quotientFour_le_centralizer (N t) (tInC t) s
      (tInC_central t))).symm.prodCongr
    (Subgroup.subgroupOfEquivOfLe (B_le_centralizer F A s a hfix Psi hPsi)).symm).trans
      (OddFieldLift.internalDirectEquiv _ _
        (KleinFourOddKernel.quotientFourInCentralizer_central (N t)
          (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) (tInC t) s
          (tInC_central t) ((Subgroup.orderOf_coe (tInC t)).symm.trans ht) hs)
        (original_quotient_internal_direct F A ht s hs hst a hfix Psi hPsi hodd ha hA).1)

theorem actualQuotientDirectEquiv_value [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (v : QuotientV s) (b : B F A a hfix Psi) :
    (actualQuotientDirectEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA (v, b) : H t) =
      (v : H t) * b := rfl

theorem N0InR_map_ambient [Finite G] {t : G} (s : C t) :
    (N0InR s).map ((D s).subtype.comp (R s).subtype) = N t ⊓ D s :=
  KleinFourOddKernel.oddKernelIntersection_map (N t)
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) s

@[expose] def actualRestrictedNu [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    R s →* B F A a hfix Psi :=
  KleinFourOddKernel.toQuotientOdd (N t)
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) (tInC t) s (tInC_central t)
    ((Subgroup.orderOf_coe (tInC t)).symm.trans ht) hs hst.symm _
    (B_le_centralizer F A s a hfix Psi hPsi) (B_odd F A a hfix Psi hodd ha hA)
    (original_quotient_internal_direct F A ht s hs hst a hfix Psi hPsi hodd ha hA)

theorem actualRestrictedNu_properties [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    Function.Surjective (actualRestrictedNu F A ht s hs hst a hfix Psi hPsi hodd ha hA) ∧
    (actualRestrictedNu F A ht s hs hst a hfix Psi hPsi hodd ha hA).ker = N0InR s ∧
    ∀ r : R s,
      (actualRestrictedNu F A ht s hs hst a hfix Psi hPsi hodd ha hA r : H t) =
        nu t ((r : D s) : C t) := by
  have hN : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have htC : orderOf (tInC t) = 2 := (Subgroup.orderOf_coe (tInC t)).symm.trans ht
  have hB := B_le_centralizer F A s a hfix Psi hPsi
  have hBo := B_odd F A a hfix Psi hodd ha hA
  have hdir := original_quotient_internal_direct F A ht s hs hst a hfix Psi hPsi hodd ha hA
  exact ⟨KleinFourOddKernel.toQuotientOdd_surjective (N t) hN (tInC t) s
      (tInC_central t) htC hs hst.symm _ hB hBo hdir,
    KleinFourOddKernel.toQuotientOdd_ker (N t) hN (tInC t) s
      (tInC_central t) htC hs hst.symm _ hB hBo hdir, fun _ => rfl⟩

@[expose] def actualOddQuotientEquiv [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    R s ⧸ N0InR s ≃* B F A a hfix Psi :=
  KleinFourOddKernel.oddKernelQuotientEquiv (N t)
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) (tInC t) s (tInC_central t)
    ((Subgroup.orderOf_coe (tInC t)).symm.trans ht) hs hst.symm _
    (B_le_centralizer F A s a hfix Psi hPsi) (B_odd F A a hfix Psi hodd ha hA)
    (original_quotient_internal_direct F A ht s hs hst a hfix Psi hPsi hodd ha hA)

theorem actualOddQuotientEquiv_mk [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) (r : R s) :
    (actualOddQuotientEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA
      (QuotientGroup.mk' (N0InR s) r) : H t) = nu t ((r : D s) : C t) :=
  KleinFourOddKernel.oddKernelQuotientEquiv_mk (N t)
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) (tInC t) s (tInC_central t)
    ((Subgroup.orderOf_coe (tInC t)).symm.trans ht) hs hst.symm _
    (B_le_centralizer F A s a hfix Psi hPsi) (B_odd F A a hfix Psi hodd ha hA)
    (original_quotient_internal_direct F A ht s hs hst a hfix Psi hPsi hodd ha hA) r

@[expose] def originalWImageEquiv {t : G} (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t) :
    OriginalWProduct F A a hfix ≃* B F A a hfix Psi :=
  (MulEquiv.ofBijective
    (Psi.toMonoidHom.comp (originalOddInclusion F A a hfix)).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
      (Psi.injective.comp (originalOddInclusion_injective F A a hfix)),
      MonoidHom.rangeRestrict_surjective _⟩).trans
        (MulEquiv.subgroupCongr (B_original_range F A a hfix Psi).symm)

theorem originalWImageEquiv_value {t : G} (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (x : OriginalWProduct F A a hfix) :
    (originalWImageEquiv F A a hfix Psi x : H t) =
      Psi (originalOddInclusion F A a hfix x) := rfl

@[expose] def actualOddQuotientOriginalEquiv [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    R s ⧸ N0InR s ≃* OriginalWProduct F A a hfix :=
  (actualOddQuotientEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA).trans
    (originalWImageEquiv F A a hfix Psi).symm

theorem actualOddQuotientOriginalEquiv_mk [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) (r : R s) :
    Psi (originalOddInclusion F A a hfix
      (actualOddQuotientOriginalEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA
        (QuotientGroup.mk' (N0InR s) r))) = nu t ((r : D s) : C t) := by
  have h := congrArg Subtype.val ((originalWImageEquiv F A a hfix Psi).apply_symm_apply
    (actualOddQuotientEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA
      (QuotientGroup.mk' (N0InR s) r)))
  exact h.trans (actualOddQuotientEquiv_mk F A ht s hs hst a hfix Psi hPsi hodd ha hA r)

@[expose] def actualQuotientOriginalDirectEquiv [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    QuotientV s × OriginalWProduct F A a hfix ≃* Subgroup.centralizer {nu t s} :=
  ((MulEquiv.refl (QuotientV s)).prodCongr (originalWImageEquiv F A a hfix Psi)).trans
    (actualQuotientDirectEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA)

theorem actualQuotientOriginalDirectEquiv_value [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (v : QuotientV s) (w : OriginalWProduct F A a hfix) :
    (actualQuotientOriginalDirectEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA
      (v, w) : H t) = (v : H t) * Psi (originalOddInclusion F A a hfix w) := rfl

theorem N0_mem_iff {t : G} (s : C t) (x : N t) :
    x ∈ N0 s ↔ s * (x : C t) = (x : C t) * s :=
  Subgroup.mem_centralizer_singleton_iff.trans eq_comm

theorem N0EquivCore_value [Finite G] {t : G} (s : C t) (x : N0 s) :
    (N0EquivCore s x).val.val.val = x.val.val := rfl

@[expose] def torusSign (q : ℕ) : ℤ := if q % 4 = 1 then 1 else -1

theorem torusSize_signed {q : ℕ} (hq : 1 ≤ q) :
    (MatrixTorus.torusSize q : ℤ) = (q : ℤ) + torusSign q := by
  unfold MatrixTorus.torusSize torusSign
  split_ifs
  · simp
  · rw [Nat.cast_sub hq]
    ring

theorem actual_valuation_identity_int [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) :
    3 * (padicValNat p (Nat.card (C t)) : ℤ) -
      2 * (padicValNat p (Nat.card (D s)) : ℤ) =
        padicValNat p (Nat.card (N0 s)) + 3 * (padicValNat p (N0 s).index : ℤ) +
          padicValNat p (Nat.card A) + 3 * (f : ℤ) := by
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hA0 : Nat.card A ≠ 0 := by have ho := Nat.odd_iff.mp hA; omega
  obtain ⟨hC, hD⟩ := four_group_order_valuations p f (Nat.card (N0 s)) (N0 s).index
    (Nat.card A) hp hpodd hf Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite hA0
  rw [actual_C_card F A s a hfix Psi,
    actual_D_card F A ht s hs hst a hfix Psi hPsi hodd ha hA, hcard, hC, hD]
  push_cast
  ring

theorem original_actions (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    (∀ (sigma : A) (x : MatrixCoverData.M F a),
      MatrixTorus.originalFieldAction F a A hfix sigma x =
        ⟨Matrix.SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom x.left, x.right⟩) ∧
    (∀ sigma : A, MatrixTorus.originalFieldAction F a A hfix sigma
      (MatrixCoverData.u F a) = MatrixCoverData.u F a) ∧
    (∀ (sigma : A) (X : MatrixTorus.W F a),
      ((originalWAction F A a hfix sigma X).val.val : Matrix (Fin 2) (Fin 2) F) =
        (sigma : F ≃+* F).toRingHom.mapMatrix (X.val.val : Matrix (Fin 2) (Fin 2) F)) := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl⟩
  intro sigma
  apply SemidirectProduct.ext
  · exact (MatrixCover.slFieldEquiv F (sigma : F ≃+* F)).map_one
  · rfl

structure OriginalTorusData [Finite F] (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) : Prop where
  coordinates : ∀ X : MatrixCoverData.SL F, X ∈ MatrixTorus.Torus F a ↔ ∃ x y : F,
    (X : Matrix (Fin 2) (Fin 2) F) = MatrixTorus.torusMatrix F a x y ∧
      x ^ 2 + (a : F) * y ^ 2 = 1
  cyclic : IsCyclic (MatrixTorus.Torus F a)
  card : Nat.card (MatrixTorus.Torus F a) = MatrixTorus.torusSize (Nat.card F)
  unique_involution : ∀ X : MatrixTorus.Torus F a,
    orderOf X = 2 ↔ X = MatrixTorus.z F a
  odd_characteristic : (MatrixTorus.W F a).Characteristic
  odd_cyclic : IsCyclic (MatrixTorus.W F a)
  odd_card : Nat.card (MatrixTorus.W F a) = MatrixTorus.torusSize (Nat.card F) / 2
  odd_membership : ∀ X : MatrixTorus.Torus F a, X ∈ MatrixTorus.W F a ↔ Odd (orderOf X)
  odd_invariant : ∀ (sigma : A) (X : MatrixTorus.W F a),
    MatrixTorus.torusFieldEquiv F a sigma (hfix sigma) X.val ∈ MatrixTorus.W F a
  odd_action : ∀ (sigma : A) (X : MatrixTorus.W F a),
    ((originalWAction F A a hfix sigma X).val.val : Matrix (Fin 2) (Fin 2) F) =
      (sigma : F ≃+* F).toRingHom.mapMatrix (X.val.val : Matrix (Fin 2) (Fin 2) F)

theorem original_torus_data [Finite F] (a : Fˣ)
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) : OriginalTorusData F A a hfix :=
  { coordinates := MatrixTorus.torus_coordinates F a
    cyclic := MatrixTorus.torus_cyclic F a hodd ha
    card := MatrixTorus.torus_card F a hodd ha
    unique_involution := MatrixTorus.torus_unique_involution F a hodd
    odd_characteristic := MatrixTorus.W_characteristic F a
    odd_cyclic := MatrixTorus.W_cyclic F a hodd ha
    odd_card := MatrixTorus.W_card F a hodd ha
    odd_membership := MatrixTorus.mem_W_iff_odd_order F a hodd ha
    odd_invariant := fun sigma X => MatrixTorus.W_field_invariant F a sigma (hfix sigma) X
    odd_action := fun _ _ => rfl }

structure OriginalCentralizerData [Finite G] [Finite F] {t : G} (s : C t) (p f : ℕ)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t) : Prop where
  odd_factor_range : B F A a hfix Psi =
    (Psi.toMonoidHom.comp (originalOddInclusion F A a hfix)).range
  odd_factor_card : Nat.card (B F A a hfix Psi) =
    Nat.card A * (MatrixTorus.torusSize (p ^ f) / 2)
  odd_factor_odd : Odd (Nat.card (B F A a hfix Psi))
  quotient_internal_direct : KleinFourOddKernel.IsInternalDirectProduct
    (KleinFourOddKernel.quotientFourInCentralizer (N t) (tInC t) s)
    (KleinFourOddKernel.quotientOddInCentralizer (N t) s (B F A a hfix Psi))
  quotient_direct : ∃ e : QuotientV s × B F A a hfix Psi ≃*
    Subgroup.centralizer {nu t s},
      ∀ v b, (e (v, b) : H t) = (v : H t) * b
  quotient_original_direct : ∃ e : QuotientV s × OriginalWProduct F A a hfix ≃*
    Subgroup.centralizer {nu t s},
      ∀ v w, (e (v, w) : H t) = (v : H t) * Psi (originalOddInclusion F A a hfix w)
  lifted : KleinFourOddKernel.LiftedCentralizerConclusion (N t) (tInC t) s (B F A a hfix Psi)
  actual_core : R s = CFSG.piCore KleinFourOddKernel.oddPrimes (D s)
  kernel_normal : (N0InR s).Normal
  kernel_original : (N0InR s).map ((D s).subtype.comp (R s).subtype) = N t ⊓ D s
  kernel_equiv : ∃ e : N0 s ≃* N0InR s, ∀ x, (e x).val.val.val = x.val.val
  restricted_nu : ∃ g : R s →* B F A a hfix Psi,
    Function.Surjective g ∧ g.ker = N0InR s ∧
      ∀ r, (g r : H t) = nu t ((r : D s) : C t)
  first_iso : ∃ e : R s ⧸ N0InR s ≃* B F A a hfix Psi,
    ∀ r, (e (QuotientGroup.mk' (N0InR s) r) : H t) = nu t ((r : D s) : C t)
  original_quotient : ∃ e : R s ⧸ N0InR s ≃* OriginalWProduct F A a hfix,
    ∀ r, Psi (originalOddInclusion F A a hfix
      (e (QuotientGroup.mk' (N0InR s) r))) = nu t ((r : D s) : C t)
  C_card : Nat.card (C t) =
    2 * Nat.card (N0 s) * (N0 s).index * Nat.card A * p ^ f * ((p ^ f) ^ 2 - 1)
  D_card : Nat.card (D s) = 2 * Nat.card (N0 s) * Nat.card A * MatrixTorus.torusSize (p ^ f)
  R_card : Nat.card (R s) = Nat.card (N0 s) * Nat.card A * MatrixTorus.torusSize (p ^ f) / 2
  valuation : 3 * padicValNat p (Nat.card (C t)) - 2 * padicValNat p (Nat.card (D s)) =
    padicValNat p (Nat.card (N0 s)) + 3 * padicValNat p (N0 s).index +
      padicValNat p (Nat.card A) + 3 * f
  valuation_int : 3 * (padicValNat p (Nat.card (C t)) : ℤ) -
    2 * (padicValNat p (Nat.card (D s)) : ℤ) =
      padicValNat p (Nat.card (N0 s)) + 3 * (padicValNat p (N0 s).index : ℤ) +
        padicValNat p (Nat.card A) + 3 * (f : ℤ)

theorem original_centralizer_data [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : OriginalCentralizerData F A s p f a hfix Psi := by
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  exact
    { odd_factor_range := B_original_range F A a hfix Psi
      odd_factor_card := by rw [← hcard]; exact B_card F A a hfix Psi hodd ha
      odd_factor_odd := B_odd F A a hfix Psi hodd ha hA
      quotient_internal_direct :=
        original_quotient_internal_direct F A ht s hs hst a hfix Psi hPsi hodd ha hA
      quotient_direct := ⟨actualQuotientDirectEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA,
        actualQuotientDirectEquiv_value F A ht s hs hst a hfix Psi hPsi hodd ha hA⟩
      quotient_original_direct :=
        ⟨actualQuotientOriginalDirectEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA,
          actualQuotientOriginalDirectEquiv_value F A ht s hs hst a hfix Psi hPsi hodd ha hA⟩
      lifted := actual_lifted_conclusion F A ht s hs hst a hfix Psi hPsi hodd ha hA
      actual_core := rfl
      kernel_normal := inferInstance
      kernel_original := N0InR_map_ambient s
      kernel_equiv := ⟨N0EquivCore s, N0EquivCore_value s⟩
      restricted_nu := ⟨actualRestrictedNu F A ht s hs hst a hfix Psi hPsi hodd ha hA,
        actualRestrictedNu_properties F A ht s hs hst a hfix Psi hPsi hodd ha hA⟩
      first_iso := ⟨actualOddQuotientEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA,
        actualOddQuotientEquiv_mk F A ht s hs hst a hfix Psi hPsi hodd ha hA⟩
      original_quotient :=
        ⟨actualOddQuotientOriginalEquiv F A ht s hs hst a hfix Psi hPsi hodd ha hA,
          actualOddQuotientOriginalEquiv_mk F A ht s hs hst a hfix Psi hPsi hodd ha hA⟩
      C_card := by rw [← hcard]; exact actual_C_card F A s a hfix Psi
      D_card := by rw [← hcard]; exact actual_D_card F A ht s hs hst a hfix Psi hPsi hodd ha hA
      R_card := by rw [← hcard]; exact actual_R_card F A ht s hs hst a hfix Psi hPsi hodd ha hA
      valuation := actual_valuation_identity F A ht s hs hst a hfix Psi hPsi ha hA p f
        hp hpodd hf hcard
      valuation_int := actual_valuation_identity_int F A ht s hs hst a hfix Psi hPsi ha hA
        p f hp hpodd hf hcard }

theorem exists_original_matrix_data {G : Type} [Group G]
    (t : G) (n p f : ℕ) (F : Type) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (hpodd : Odd p) (data : ActualMatrixData t n p f F A rho) :
    ∃ (a : (MatrixCover.FixedField F A)ˣ)
      (Psi0 : MatrixTorus.OriginalH F (MatrixCover.fixedUnit F A a) A
        (fixed_coefficient_action F A a) ≃* H t),
      (∀ x : (MatrixCover.FixedField F A)ˣ, x ∈ Subgroup.zpowers a) ∧
      ¬IsSquare a ∧ ¬IsSquare (MatrixCover.fixedUnit F A a) ∧
      Psi0 (MatrixTorus.originalZ F (MatrixCover.fixedUnit F A a) A
        (fixed_coefficient_action F A a)) = nu t (tInC t) := by
  have hfixedodd : Odd (Nat.card (MatrixCover.FixedField F A)) := by
    rw [data.fixed_field_card]
    exact hpodd.pow
  obtain ⟨a, hgen, ha⟩ := odd_field_generator_nonsquare (MatrixCover.FixedField F A) hfixedodd
  obtain ⟨haF, phi, hz, _, _⟩ := data.every_coefficient a ha
  let Psi0 := (fixedModelEquiv F A a).symm.trans phi
  refine ⟨a, Psi0, hgen, ha, haF, ?_⟩
  change phi ((fixedModelEquiv F A a).symm
    (MatrixTorus.originalZ F (MatrixCover.fixedUnit F A a) A
      (fixed_coefficient_action F A a))) = nu t (tInC t)
  rw [← fixedModelEquiv_z, MulEquiv.symm_apply_apply]
  exact hz

theorem torusSign_mod_four {q : ℕ} (hq : Odd q) :
    (q % 4 = 1 ∧ torusSign q = 1) ∨ (q % 4 = 3 ∧ torusSign q = -1) := by
  have hm := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq)
  rcases hm with hm | hm
  · exact Or.inl ⟨hm, ite_eq_left hm⟩
  · exact Or.inr ⟨hm, ite_eq_right (by omega)⟩

structure SignedOrderData [Finite G] [Finite F] {t : G} (s : C t) (p f : ℕ) (a : Fˣ) :
    Prop where
  sign : (p ^ f % 4 = 1 ∧ torusSign (p ^ f) = 1) ∨
    (p ^ f % 4 = 3 ∧ torusSign (p ^ f) = -1)
  W_card : (Nat.card (MatrixTorus.W F a) : ℤ) =
    ((p ^ f : ℕ) + torusSign (p ^ f)) / 2
  C_card : (Nat.card (C t) : ℤ) =
    2 * Nat.card (N0 s) * (N0 s).index * Nat.card A * (p ^ f : ℕ) *
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1)
  D_card : (Nat.card (D s) : ℤ) =
    2 * Nat.card (N0 s) * Nat.card A * ((p ^ f : ℕ) + torusSign (p ^ f))
  R_card : (Nat.card (R s) : ℤ) =
    (Nat.card (N0 s) * Nat.card A * ((p ^ f : ℕ) + torusSign (p ^ f))) / 2

theorem signed_order_data [Finite G] [Finite F] {t : G}
    (ht : orderOf t = 2) (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (a : Fˣ) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (Psi : MatrixTorus.OriginalH F a A hfix ≃* H t)
    (hPsi : Psi (MatrixTorus.originalU F a A hfix) = nu t s)
    (ha : ¬IsSquare a) (hA : Odd (Nat.card A))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : SignedOrderData F A s p f a := by
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hq : 1 ≤ p ^ f := (Nat.one_lt_pow (by omega) hp.one_lt).le
  have hsq : 1 ≤ (p ^ f) ^ 2 := by nlinarith
  have h := original_centralizer_data F A ht s hs hst a hfix Psi hPsi ha hA
    p f hp hpodd hf hcard
  refine
    { sign := torusSign_mod_four hpodd.pow
      W_card := ?_
      C_card := ?_
      D_card := ?_
      R_card := ?_ }
  · rw [MatrixTorus.W_card F a hodd ha, hcard, Int.natCast_ediv, torusSize_signed hq]
    norm_num
  · rw [h.C_card]
    push_cast
    rw [Nat.cast_sub hsq]
    push_cast
    rfl
  · rw [h.D_card]
    push_cast
    rw [torusSize_signed hq, Nat.cast_pow]
  · rw [h.R_card, Int.natCast_ediv]
    push_cast
    rw [torusSize_signed hq, Nat.cast_pow]

theorem original_ambient_subgroups {t : G} (s : C t) :
    (D s).map (C t).subtype = C t ⊓ Subgroup.centralizer {(s : G)} ∧
    (V s).map (C t).subtype = Subgroup.zpowers t ⊔ Subgroup.zpowers (s : G) ∧
    ∀ x : N t, x ∈ N0 s ↔ s * (x : C t) = (x : C t) * s :=
  ⟨D_map_ambient s, V_map_ambient s, N0_mem_iff s⟩

theorem actual_simple_layer_four_group_centralizer_odd_core
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (∃ s : C t, orderOf s = 2 ∧ s ≠ tInC t) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F))
      (a : (MatrixCover.FixedField F A)ˣ),
      Nat.card F = p ^ f ∧ Odd (Nat.card A) ∧ Nat.card A ∣ f ∧
      Nat.card (MatrixCover.FixedField F A) = p ^ (f / Nat.card A) ∧
      Nat.card F = (p ^ (f / Nat.card A)) ^ Nat.card A ∧
      (∀ x : (MatrixCover.FixedField F A)ˣ, x ∈ Subgroup.zpowers a) ∧
      ¬IsSquare a ∧ ¬IsSquare (MatrixCover.fixedUnit F A a) ∧
      (∀ (sigma : A) (x : MatrixCoverData.M F (MatrixCover.fixedUnit F A a)),
        MatrixTorus.originalFieldAction F (MatrixCover.fixedUnit F A a) A
          (fixed_coefficient_action F A a) sigma x =
            ⟨Matrix.SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom x.left, x.right⟩) ∧
      (∀ sigma : A,
        MatrixTorus.originalFieldAction F (MatrixCover.fixedUnit F A a) A
          (fixed_coefficient_action F A a) sigma (MatrixCoverData.u F (MatrixCover.fixedUnit F A a)) =
            MatrixCoverData.u F (MatrixCover.fixedUnit F A a)) ∧
      OriginalTorusData F A (MatrixCover.fixedUnit F A a) (fixed_coefficient_action F A a) ∧
      ∀ (s : C t), orderOf s = 2 → s ≠ tInC t →
        ∃ Psi : MatrixTorus.OriginalH F (MatrixCover.fixedUnit F A a) A
          (fixed_coefficient_action F A a) ≃* H t,
          Psi (MatrixTorus.originalZ F (MatrixCover.fixedUnit F A a) A
            (fixed_coefficient_action F A a)) = nu t (tInC t) ∧
          Psi (MatrixTorus.originalU F (MatrixCover.fixedUnit F A a) A
            (fixed_coefficient_action F A a)) = nu t s ∧
          OriginalCentralizerData F A s p f (MatrixCover.fixedUnit F A a)
            (fixed_coefficient_action F A a) Psi ∧
          SignedOrderData F A s p f (MatrixCover.fixedUnit F A a) ∧
          (D s).map (C t).subtype = C t ⊓ Subgroup.centralizer {(s : G)} ∧
          (V s).map (C t).subtype = Subgroup.zpowers t ⊔ Subgroup.zpowers (s : G) ∧
          ∀ x : N t, x ∈ N0 s ↔ s * (x : C t) = (x : C t) * s := by
  have hex : ∃ s : C t, orderOf s = 2 ∧ s ≠ tInC t := by
    exact ActualFourGroupAlignment.exists_actual_noncentral_involution n hn S0 f0 hG t ht
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  obtain ⟨a, Psi0, hgen, ha, haF, hz⟩ :=
    exists_original_matrix_data t n p f F A rho hpodd data
  have hodd : Odd (Nat.card F) := by rw [data.field_card]; exact hpodd.pow
  obtain ⟨hentry, hu, _⟩ := original_actions F A (MatrixCover.fixedUnit F A a)
    (fixed_coefficient_action F A a)
  refine ⟨hex, F, hfield, hfinite, A, a, data.field_card, data.field_group_odd,
    data.field_group_dvd, data.fixed_field_card, data.field_power, hgen, ha, haF,
    hentry, hu, original_torus_data F A (MatrixCover.fixedUnit F A a)
      (fixed_coefficient_action F A a) hodd haF, ?_⟩
  intro s hs hst
  obtain ⟨c, Psi, hPsiZ, hPsiU, _⟩ := ActualFourGroupAlignment.exists_original_aligned_equiv
    F (MatrixCover.fixedUnit F A a) A (fixed_coefficient_action F A a)
      n hn S0 f0 hG t ht Psi0 hz s hs hst
  refine ⟨Psi, hPsiZ, hPsiU, ?_, ?_, D_map_ambient s, V_map_ambient s, N0_mem_iff s⟩
  · exact original_centralizer_data F A ht s hs hst (MatrixCover.fixedUnit F A a)
      (fixed_coefficient_action F A a) Psi hPsiU haF data.field_group_odd
      p f hp hpodd hf data.field_card
  · exact signed_order_data F A ht s hs hst (MatrixCover.fixedUnit F A a)
      (fixed_coefficient_action F A a) Psi hPsiU haF data.field_group_odd
      p f hp hpodd hf data.field_card


end CFSG.Semidihedral.ActualFourGroupCentralizer
