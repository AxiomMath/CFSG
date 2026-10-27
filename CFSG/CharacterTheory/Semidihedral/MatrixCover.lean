module

public import CFSG.CharacterTheory.Semidihedral.ProjectiveNonsquareInvolutions
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders

public section

namespace CFSG.Semidihedral.MatrixCover

noncomputable section

open Matrix
open CFSG.Semidihedral.MatrixCoverData
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u v

variable (F : Type u) [Field F]

abbrev FixedField (A : Subgroup (F ≃+* F)) := FixedPoints.subfield A F

@[expose] def fixedUnit (A : Subgroup (F ≃+* F)) : (FixedField F A)ˣ →* Fˣ :=
  Units.map (FixedField F A).subtype.toMonoidHom

theorem fixedUnit_coe (A : Subgroup (F ≃+* F)) (a : (FixedField F A)ˣ) :
    (fixedUnit F A a : F) = ((a : FixedField F A) : F) := rfl

theorem square_root_fixed [Finite F] (A : Subgroup (F ≃+* F))
    (hA : Odd (Nat.card A)) (a : FixedField F A) (b : F) (hb : b ^ 2 = (a : F)) :
    ∀ sigma : A, (sigma : F ≃+* F) b = b := by
  intro sigma
  have ha : (sigma : F ≃+* F) (a : F) = (a : F) := a.property sigma
  have hs : ((sigma : F ≃+* F) b) ^ 2 = b ^ 2 := by
    rw [← map_pow, hb, ha]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
  · exact hs
  · have iter (n : ℕ) : (((sigma : A) ^ n : A) : F ≃+* F) b = (-1 : F) ^ n * b := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Subgroup.coe_mul]
        change (sigma : F ≃+* F) (((sigma ^ n : A) : F ≃+* F) b) = _
        rw [ih, map_mul, map_pow, map_neg, map_one, hs]
        ring
    have hi := iter (Nat.card A)
    rw [pow_card_eq_one', Subgroup.coe_one, hA.neg_one_pow, neg_one_mul] at hi
    change b = -b at hi
    exact hs.trans hi.symm

theorem fixed_nonsquare_retained [Finite F] (A : Subgroup (F ≃+* F))
    (hA : Odd (Nat.card A)) (a : (FixedField F A)ˣ) (ha : ¬IsSquare a) :
    ¬IsSquare (fixedUnit F A a) := by
  intro hs
  obtain ⟨b, hb⟩ := (CFSG.Semidihedral.SemilinearOuterQuotient.isSquare_unit_iff _).mp hs
  have hfix := square_root_fixed F A hA (a : FixedField F A) b (by
    simpa only [pow_two, fixedUnit_coe] using hb.symm)
  let b0 : FixedField F A := ⟨b, hfix⟩
  have hb0 : IsSquare (a : FixedField F A) :=
    ⟨b0, Subtype.ext (by simpa only [b0, Subfield.coe_mul, fixedUnit_coe] using hb)⟩
  exact ha ((CFSG.Semidihedral.SemilinearOuterQuotient.isSquare_unit_iff a).mpr hb0)

@[expose] def slFieldEquiv (sigma : F ≃+* F) : MulAut (SL F) where
  toFun := SpecialLinearGroup.map sigma.toRingHom
  invFun := SpecialLinearGroup.map sigma.symm.toRingHom
  left_inv X := by
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  right_inv X := by
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  map_mul' := (SpecialLinearGroup.map sigma.toRingHom).map_mul

theorem slFieldEquiv_apply (sigma : F ≃+* F) (X : SL F) :
    (slFieldEquiv F sigma X : Matrix (Fin 2) (Fin 2) F) =
      sigma.toRingHom.mapMatrix (X : Matrix (Fin 2) (Fin 2) F) := rfl

theorem slFieldEquiv_mul (sigma tau : F ≃+* F) :
    slFieldEquiv F (sigma * tau) = slFieldEquiv F sigma * slFieldEquiv F tau := by
  apply MulEquiv.ext
  intro X
  apply Subtype.ext
  ext i j
  rfl

theorem field_action_commutes (sigma : F ≃+* F) (a : Fˣ)
    (ha : sigma (a : F) = a) (e : C2) (X : SL F) :
    slFieldEquiv F sigma (MatrixCoverData.action F a e X) =
      MatrixCoverData.action F a e (slFieldEquiv F sigma X) := by
  have h := exponent_lt_two e
  interval_cases hv : exponent e
  · change SpecialLinearGroup.map sigma.toRingHom
      (((beta F a) ^ exponent e) X) =
        ((beta F a) ^ exponent e) (SpecialLinearGroup.map sigma.toRingHom X)
    simp [hv]
  · change SpecialLinearGroup.map sigma.toRingHom
      (((beta F a) ^ exponent e) X) =
        ((beta F a) ^ exponent e) (SpecialLinearGroup.map sigma.toRingHom X)
    simpa only [hv, pow_one] using field_map_beta_of_fix F sigma a ha X

@[expose] def matrixFieldEquiv (sigma : F ≃+* F) (a : Fˣ)
    (ha : sigma (a : F) = a) : MulAut (M F a) where
  toFun x := ⟨slFieldEquiv F sigma x.left, x.right⟩
  invFun x := ⟨(slFieldEquiv F sigma).symm x.left, x.right⟩
  left_inv x := SemidirectProduct.ext ((slFieldEquiv F sigma).symm_apply_apply x.left) rfl
  right_inv x := SemidirectProduct.ext ((slFieldEquiv F sigma).apply_symm_apply x.left) rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change slFieldEquiv F sigma (x.left * MatrixCoverData.action F a x.right y.left) =
        slFieldEquiv F sigma x.left *
          MatrixCoverData.action F a x.right (slFieldEquiv F sigma y.left)
      rw [map_mul, field_action_commutes F sigma a ha]
    · rfl

@[expose] def matrixFieldAction (A : Subgroup (F ≃+* F)) (a : (FixedField F A)ˣ) :
    A →* MulAut (M F (fixedUnit F A a)) where
  toFun sigma := matrixFieldEquiv F sigma (fixedUnit F A a) (by
    rw [fixedUnit_coe]
    exact (a : FixedField F A).property sigma)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply SemidirectProduct.ext
    · apply Subtype.ext
      ext i j
      rfl
    · rfl
  map_mul' sigma tau := by
    apply MulEquiv.ext
    intro x
    apply SemidirectProduct.ext
    · exact DFunLike.congr_fun (slFieldEquiv_mul F sigma tau) x.left
    · rfl

theorem matrixFieldAction_pair (A : Subgroup (F ≃+* F)) (a : (FixedField F A)ˣ)
    (sigma : A) (x : M F (fixedUnit F A a)) :
    matrixFieldAction F A a sigma x = ⟨SpecialLinearGroup.map
      (sigma : F ≃+* F).toRingHom x.left, x.right⟩ := rfl

abbrev MatrixFieldModel (A : Subgroup (F ≃+* F)) (a : (FixedField F A)ˣ) :=
  SemidirectProduct (M F (fixedUnit F A a)) A (matrixFieldAction F A a)


theorem semidihedral_reflection (n : ℕ) (hn : 4 ≤ n) :
    orderOf (CFSG.Semidihedral.s n) = 2 ∧
      CFSG.Semidihedral.s n ∉ Subgroup.center (CFSG.Open.SemidihedralGroup n) := by
  refine ⟨CFSG.Semidihedral.orderOf_s n (by omega), ?_⟩
  intro hs
  have h := (CFSG.Semidihedral.element_mem_center_iff n hn 0 1).mp
    (CFSG.Semidihedral.s_eq_element n (by omega) ▸ hs)
  exact one_ne_zero h.1

theorem layer_unique_involution {H : Type v} [Group H]
    (N : Subgroup H) (eta : N ≃* SL F) (z : N)
    (heta : eta z = OddFieldSL2.minusIdentity F) (h2 : (2 : F) ≠ 0)
    (x : N) (hx : orderOf x = 2) : x = z := by
  apply eta.injective
  rw [heta]
  apply (OddFieldSL2.orderOf_eq_two_iff F h2 (eta x)).mp
  rw [eta.orderOf_eq, hx]

theorem glProjective_surjective : Function.Surjective (glProjective F) := by
  intro d
  have hd : (d : Equiv.Perm (Omega F)) ∈
      ((coordinatePGLAction F).comp Matrix.ProjGenLinGroup.mk).range := by
    rw [coordinateGLAction_range_eq_D]
    exact d.property
  obtain ⟨X, hX⟩ := hd
  exact ⟨X, Subtype.ext hX⟩

theorem slProjective_range :
    (slProjective F).range = (coordinateG F).subgroupOf (coordinateD F) := by
  ext d
  constructor
  · rintro ⟨X, rfl⟩
    change coordinatePGLAction F (Matrix.ProjGenLinGroup.mk
      (SpecialLinearGroup.toGL X)) ∈ coordinateG F
    rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL,
      ← coordinatePSLAction_range_eq_G]
    exact ⟨_, rfl⟩
  · intro hd
    change (d : Equiv.Perm (Omega F)) ∈ coordinateG F at hd
    rw [← coordinatePSLAction_range_eq_G] at hd
    obtain ⟨x, hx⟩ := hd
    obtain ⟨X, hX⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin 2) F)) x
    refine ⟨X, Subtype.ext ?_⟩
    change coordinatePGLAction F (Matrix.ProjGenLinGroup.mk
      (SpecialLinearGroup.toGL X)) = d
    rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      coordinatePGLAction_toPGL]
    change coordinatePSLAction F (QuotientGroup.mk' _ X) = d
    rw [hX]
    exact hx


theorem determinantClass_eq_one_iff [Finite F] (d : coordinateD F) :
    SemilinearOuterQuotient.determinantClass F d = 1 ↔
      (d : Equiv.Perm (Omega F)) ∈ coordinateG F := by
  obtain ⟨V, rfl⟩ := glProjective_surjective F d
  rw [SemilinearOuterQuotient.determinantClass_matrix F _ V rfl,
    SemilinearOuterQuotient.squareClassMap_eq_one,
    ProjectiveNonsquareInvolutions.projective_mem_G_iff]

theorem outer_factor [Finite F] (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (a : Fˣ) (ha : ¬IsSquare a) (d : coordinateD F)
    (hd : (d : Equiv.Perm (Omega F)) ∉ coordinateG F) :
    ∃ X : SL F, d = slProjective F X * jProjective F a := by
  have hj := (ProjectiveNonsquareInvolutions.jProjective_outer_involution F a ha).1
  have hclasses := SemilinearOuterQuotient.eq_of_nonone_of_card_two
    (SemilinearOuterQuotient.squareClass_card_two F hF)
    (fun h => hd ((determinantClass_eq_one_iff F d).mp h))
    (fun h => hj ((determinantClass_eq_one_iff F (jProjective F a)).mp h))
  have hmem : d * (jProjective F a)⁻¹ ∈ (coordinateG F).subgroupOf (coordinateD F) := by
    change ((d * (jProjective F a)⁻¹ : coordinateD F) : Equiv.Perm (Omega F)) ∈ coordinateG F
    apply (determinantClass_eq_one_iff F _).mp
    rw [map_mul, map_inv, hclasses, mul_inv_cancel]
  rw [← slProjective_range F] at hmem
  obtain ⟨X, hX⟩ := hmem
  exact ⟨X, by rw [hX]; group⟩

theorem cover_pi_surjective [Finite F]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (a : Fˣ) (ha : ¬IsSquare a) : Function.Surjective (MatrixCoverData.pi F a) := by
  intro d
  by_cases hd : (d : Equiv.Perm (Omega F)) ∈ coordinateG F
  · have hd' : d ∈ (slProjective F).range := by rw [slProjective_range F]; exact hd
    obtain ⟨X, rfl⟩ := hd'
    exact ⟨inclusion F a X, pi_inclusion F a X⟩
  · obtain ⟨X, hX⟩ := outer_factor F hF a ha d hd
    refine ⟨inclusion F a X * u F a, ?_⟩
    rw [map_mul, pi_inclusion, pi_u, hX]


theorem slProjective_coordinate (X : SL F) :
    (slProjective F X : Equiv.Perm (Omega F)) = OddFieldLift.slCoordinateAction F X := by
  change coordinatePGLAction F (Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL X)) = _
  rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL]
  rfl

theorem slConjugation_projective (V : GL2 F) (X : SL F) :
    OddFieldLift.slCoordinateAction F (slConjugation F V X) =
      (glProjective F V : Equiv.Perm (Omega F)) * OddFieldLift.slCoordinateAction F X *
        (glProjective F V : Equiv.Perm (Omega F))⁻¹ := by
  rw [← slProjective_coordinate, ← slProjective_coordinate]
  change (glProjective F (SpecialLinearGroup.toGL (slConjugation F V X)) :
    Equiv.Perm (Omega F)) = _
  rw [slConjugation_toGL, map_mul, map_mul, map_inv]
  rfl

theorem compatible_matrix_conjugation {H : Type v} [Group H]
    (p : ℕ) [CharP F p] (hp : Odd p) (N : Subgroup H) [N.Normal]
    (eta : N ≃* SL F) (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ x : N, OddFieldLift.slCoordinateAction F (eta x) = chi x)
    (t : H) (V : GL2 F) (ht : chi t = (glProjective F V : Equiv.Perm (Omega F)))
    (x : N) : eta (MulAut.conjNormal t x) = slConjugation F V (eta x) := by
  let alpha : SL F →* SL F := eta.toMonoidHom.comp
    ((MulAut.conjNormal t).toMonoidHom.comp eta.symm.toMonoidHom)
  have hproj : ∀ X : SL F, OddFieldLift.slCoordinateAction F (alpha X) =
      OddFieldLift.slCoordinateAction F (slConjugation F V X) := by
    intro X
    change OddFieldLift.slCoordinateAction F (eta (MulAut.conjNormal t (eta.symm X))) = _
    rw [heta, MulAut.conjNormal_apply, map_mul, map_mul, map_inv, ht,
      ← heta (eta.symm X), eta.apply_symm_apply]
    exact (slConjugation_projective F V X).symm
  have h := DFunLike.congr_fun (OddFieldLift.hom_eq_of_projective_eq p hp alpha
    (slConjugation F V).toMonoidHom hproj) (eta x)
  simpa only [alpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    eta.symm_apply_apply] using h

@[expose] def layerLift {H : Type v} [Group H] (N : Subgroup H) (eta : N ≃* SL F) :
    SL F →* H := N.subtype.comp eta.symm.toMonoidHom

theorem layerLift_apply {H : Type v} [Group H] (N : Subgroup H) (eta : N ≃* SL F)
    (X : SL F) : layerLift F N eta X = (eta.symm X : H) := rfl

theorem layerLift_injective {H : Type v} [Group H] (N : Subgroup H) (eta : N ≃* SL F) :
    Function.Injective (layerLift F N eta) := Subtype.val_injective.comp eta.symm.injective

@[expose] def involutionFactor {H : Type v} [Group H] (t : H) (ht : t ^ 2 = 1) : C2 →* H :=
  QuaternionAutomorphismLifting.coordinatePowerHom 2 t ht

theorem involutionFactor_apply {H : Type v} [Group H] (t : H) (ht : t ^ 2 = 1) (e : C2) :
    involutionFactor t ht e = t ^ exponent e := rfl

@[expose] def pairLift {H : Type v} [Group H]
    (N : Subgroup H) (eta : N ≃* SL F) (a : Fˣ) (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F N eta (beta F a X) =
      t * layerLift F N eta X * t⁻¹) : M F a →* H :=
  SemidirectProduct.lift (layerLift F N eta) (involutionFactor t ht) (by
    intro e
    apply MonoidHom.ext
    intro X
    have he := exponent_lt_two e
    interval_cases he' : exponent e
    · change layerLift F N eta (((beta F a) ^ exponent e) X) =
        t ^ exponent e * layerLift F N eta X * (t ^ exponent e)⁻¹
      simp [he']
    · change layerLift F N eta (((beta F a) ^ exponent e) X) =
        t ^ exponent e * layerLift F N eta X * (t ^ exponent e)⁻¹
      simpa only [he', pow_one] using hconj X)

theorem pairLift_formula {H : Type v} [Group H]
    (N : Subgroup H) (eta : N ≃* SL F) (a : Fˣ) (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F N eta (beta F a X) =
      t * layerLift F N eta X * t⁻¹) (x : M F a) :
    pairLift F N eta a t ht hconj x = (eta.symm x.left : H) * t ^ exponent x.right := rfl


theorem c2_eq_one_of_exponent_zero (e : C2) (he : exponent e = 0) : e = 1 := by
  apply (Multiplicative.toAdd : C2 ≃ ZMod 2).injective
  apply ZMod.val_injective
  exact he

theorem pairLift_injective {H : Type v} [Group H]
    (N : Subgroup H) (eta : N ≃* SL F) (a : Fˣ) (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F N eta (beta F a X) =
      t * layerLift F N eta X * t⁻¹) (hout : t ∉ N) :
    Function.Injective (pairLift F N eta a t ht hconj) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  change pairLift F N eta a t ht hconj x = 1 at hx
  rw [pairLift_formula] at hx
  have he := exponent_lt_two x.right
  interval_cases he' : exponent x.right
  · have hX : x.left = 1 := by
      apply layerLift_injective F N eta
      simpa only [he', pow_zero, mul_one, map_one, layerLift_apply] using hx
    apply SemidirectProduct.ext hX
    exact c2_eq_one_of_exponent_zero x.right he'
  · have hmem : t ∈ N := by
      have hxe : layerLift F N eta x.left * t = 1 := by
        simpa only [he', pow_one, layerLift_apply] using hx
      have ht' : t = (layerLift F N eta x.left)⁻¹ :=
        eq_inv_of_mul_eq_one_right hxe
      rw [ht']
      exact N.inv_mem (eta.symm x.left).property
    exact (hout hmem).elim

theorem pairLift_projective {H : Type v} [Group H]
    (N : Subgroup H) (eta : N ≃* SL F) (a : Fˣ) (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F N eta (beta F a X) =
      t * layerLift F N eta X * t⁻¹)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ x : N, OddFieldLift.slCoordinateAction F (eta x) = chi x)
    (himage : chi t = (jProjective F a : Equiv.Perm (Omega F))) (x : M F a) :
    chi (pairLift F N eta a t ht hconj x) =
      (MatrixCoverData.pi F a x : Equiv.Perm (Omega F)) := by
  rw [pairLift_formula, map_mul, map_pow, himage]
  have hl : chi (eta.symm x.left : H) =
      (slProjective F x.left : Equiv.Perm (Omega F)) := by
    rw [← heta, eta.apply_symm_apply, slProjective_coordinate]
  rw [hl, pi_formula, map_mul, map_pow]
  rfl

theorem layerLift_matrix_conjugation {H : Type v} [Group H]
    (p : ℕ) [CharP F p] (hp : Odd p) (N : Subgroup H) [N.Normal]
    (eta : N ≃* SL F) (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ x : N, OddFieldLift.slCoordinateAction F (eta x) = chi x)
    (a : Fˣ) (t : H) (ht : chi t = (jProjective F a : Equiv.Perm (Omega F)))
    (X : SL F) : layerLift F N eta (beta F a X) =
      t * layerLift F N eta X * t⁻¹ := by
  have h := compatible_matrix_conjugation F p hp N eta chi heta t (J F a) ht (eta.symm X)
  have he : eta.symm (beta F a X) = MulAut.conjNormal t (eta.symm X) := by
    apply eta.injective
    simpa only [eta.apply_symm_apply, beta] using h.symm
  change (eta.symm (beta F a X) : H) = _
  rw [he, MulAut.conjNormal_apply]
  rfl


theorem mem_Lambda_iff [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A) (x : H) :
    x ∈ OddFieldLift.Lambda F A pi ↔
      OddFieldLift.coordinateProjection F A pi x ∈ coordinateG F := Iff.rfl

theorem mem_M_iff [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A) (x : H) :
    x ∈ OddFieldLift.M F A pi ↔
      OddFieldLift.coordinateProjection F A pi x ∈ coordinateD F := Iff.rfl

theorem kernel_le_Lambda [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A) :
    pi.ker ≤ OddFieldLift.Lambda F A pi := pi.ker_le_comap _

theorem quotient_coordinates_injective [Finite F] (A : Subgroup (F ≃+* F)) :
    Function.Injective (fun x : OddFieldLift.Gamma F A =>
      ((x : coordinateE F) : Equiv.Perm (Omega F))) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem coordinateProjection_ker [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A) :
    (OddFieldLift.coordinateProjection F A pi).ker = pi.ker := by
  change (((coordinateE F).subtype.comp (OddFieldLift.Gamma F A).subtype).comp pi).ker = pi.ker
  exact MonoidHom.ker_comp_of_injective pi _ (quotient_coordinates_injective F A)

theorem pairLift_mem_M [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (eta : OddFieldLift.Lambda F A pi ≃* SL F) (a : Fˣ) (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F (OddFieldLift.Lambda F A pi) eta (beta F a X) =
      t * layerLift F (OddFieldLift.Lambda F A pi) eta X * t⁻¹)
    (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
      OddFieldLift.coordinateProjection F A pi x)
    (himage : OddFieldLift.coordinateProjection F A pi t =
      (jProjective F a : Equiv.Perm (Omega F))) (x : M F a) :
    pairLift F (OddFieldLift.Lambda F A pi) eta a t ht hconj x ∈ OddFieldLift.M F A pi := by
  rw [mem_M_iff, pairLift_projective F _ eta a t ht hconj _ heta himage]
  exact (MatrixCoverData.pi F a x).property

theorem pairLift_range [Finite F] {H : Type v} [Group H]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (eta : OddFieldLift.Lambda F A pi ≃* SL F) (a : Fˣ) (ha : ¬IsSquare a)
    (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F (OddFieldLift.Lambda F A pi) eta (beta F a X) =
      t * layerLift F (OddFieldLift.Lambda F A pi) eta X * t⁻¹)
    (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
      OddFieldLift.coordinateProjection F A pi x)
    (himage : OddFieldLift.coordinateProjection F A pi t =
      (jProjective F a : Equiv.Perm (Omega F))) :
    (pairLift F (OddFieldLift.Lambda F A pi) eta a t ht hconj).range =
      OddFieldLift.M F A pi := by
  let psi := pairLift F (OddFieldLift.Lambda F A pi) eta a t ht hconj
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact pairLift_mem_M F A pi eta a t ht hconj heta himage x
  · intro m hm
    obtain ⟨x, hx⟩ := cover_pi_surjective F hF a ha
      ⟨OddFieldLift.coordinateProjection F A pi m, hm⟩
    have hproj : OddFieldLift.coordinateProjection F A pi (psi x) =
        OddFieldLift.coordinateProjection F A pi m := by
      rw [pairLift_projective F _ eta a t ht hconj _ heta himage]
      exact congrArg Subtype.val hx
    have hk : m * (psi x)⁻¹ ∈ OddFieldLift.Lambda F A pi := by
      apply kernel_le_Lambda F A pi
      rw [← coordinateProjection_ker, MonoidHom.mem_ker, map_mul, map_inv, hproj,
        mul_inv_cancel]
    let k : OddFieldLift.Lambda F A pi := ⟨m * (psi x)⁻¹, hk⟩
    refine ⟨inclusion F a (eta k) * x, ?_⟩
    change psi (inclusion F a (eta k) * x) = m
    rw [map_mul]
    have hl : psi (inclusion F a (eta k)) = (k : H) := by
      change (SemidirectProduct.lift _ _ _) (SemidirectProduct.inl (eta k)) = _
      rw [SemidirectProduct.lift_inl]
      exact congrArg Subtype.val (eta.symm_apply_apply k)
    rw [hl]
    dsimp [k]
    group


@[expose] def pairEquiv [Finite F] {H : Type v} [Group H]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (eta : OddFieldLift.Lambda F A pi ≃* SL F) (a : Fˣ) (ha : ¬IsSquare a)
    (t : H) (ht : t ^ 2 = 1) (hout : t ∉ OddFieldLift.Lambda F A pi)
    (hconj : ∀ X : SL F, layerLift F (OddFieldLift.Lambda F A pi) eta (beta F a X) =
      t * layerLift F (OddFieldLift.Lambda F A pi) eta X * t⁻¹)
    (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
      OddFieldLift.coordinateProjection F A pi x)
    (himage : OddFieldLift.coordinateProjection F A pi t =
      (jProjective F a : Equiv.Perm (Omega F))) :
    M F a ≃* OddFieldLift.M F A pi :=
  MulEquiv.ofBijective ((pairLift F (OddFieldLift.Lambda F A pi) eta a t ht hconj).codRestrict
    (OddFieldLift.M F A pi) (pairLift_mem_M F A pi eta a t ht hconj heta himage)) (by
      constructor
      · intro x y h
        apply pairLift_injective F _ eta a t ht hconj hout
        exact congrArg Subtype.val h
      · intro m
        have hr := pairLift_range F hF A pi eta a ha t ht hconj heta himage
        have hm : (m : H) ∈ (pairLift F _ eta a t ht hconj).range := by
          rw [hr]
          exact m.property
        obtain ⟨x, hx⟩ := hm
        exact ⟨x, Subtype.ext hx⟩)

theorem pairEquiv_coe [Finite F] {H : Type v} [Group H]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (eta : OddFieldLift.Lambda F A pi ≃* SL F) (a : Fˣ) (ha : ¬IsSquare a)
    (t : H) (ht : t ^ 2 = 1) (hout : t ∉ OddFieldLift.Lambda F A pi)
    (hconj : ∀ X : SL F, layerLift F (OddFieldLift.Lambda F A pi) eta (beta F a X) =
      t * layerLift F (OddFieldLift.Lambda F A pi) eta X * t⁻¹)
    (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
      OddFieldLift.coordinateProjection F A pi x)
    (himage : OddFieldLift.coordinateProjection F A pi t =
      (jProjective F a : Equiv.Perm (Omega F))) (x : M F a) :
    (pairEquiv F hF A pi eta a ha t ht hout hconj heta himage x : H) =
      (eta.symm x.left : H) * t ^ exponent x.right := rfl

@[expose] def originalFieldLift [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (hd : Odd (Nat.card A)) : A →* H :=
  (OddFieldLift.E F A pi z hzc hker).subtype.comp
    (OddFieldLift.EEquivField F A pi hpi z hz hzc hker hd).symm.toMonoidHom

theorem originalFieldLift_apply [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (hd : Odd (Nat.card A)) (sigma : A) :
    originalFieldLift F A pi hpi z hz hzc hker hd sigma =
      (OddFieldLift.eSigma F A pi hpi z hz hzc hker hd sigma : H) := rfl

theorem original_eSigma_unique [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (hd : Odd (Nat.card A)) (sigma : A) :
    ∃! e : OddFieldLift.E F A pi z hzc hker,
      OddFieldLift.coordinateProjection F A pi e = fieldExtension F sigma := by
  refine ⟨OddFieldLift.eSigma F A pi hpi z hz hzc hker hd sigma,
    OddFieldLift.eSigma_projective F A pi hpi z hz hzc hker hd sigma, ?_⟩
  intro e he
  apply (OddFieldLift.piOnE F A pi hpi z hz hzc hker hd).injective
  apply Subtype.ext
  apply quotient_coordinates_injective F A
  simpa only [OddFieldLift.piOnE_coe, OddFieldLift.coordinateProjection,
    MonoidHom.comp_apply, Subgroup.coe_subtype] using
    he.trans (OddFieldLift.eSigma_projective F A pi hpi z hz hzc hker hd sigma).symm


theorem layerLift_field_conjugation [Finite F] {H : Type v} [Group H]
    (p : ℕ) [CharP F p] (hp : Odd p) (N : Subgroup H) [N.Normal]
    (eta : N ≃* SL F) (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ x : N, OddFieldLift.slCoordinateAction F (eta x) = chi x)
    (e : H) (sigma : F ≃+* F) (he : chi e = fieldExtension F sigma)
    (X : SL F) : layerLift F N eta (SpecialLinearGroup.map sigma.toRingHom X) =
      e * layerLift F N eta X * e⁻¹ := by
  let alpha : SL F →* SL F := eta.toMonoidHom.comp
    ((MulAut.conjNormal e).toMonoidHom.comp eta.symm.toMonoidHom)
  have hproj : ∀ X : SL F, OddFieldLift.slCoordinateAction F (alpha X) =
      OddFieldLift.slCoordinateAction F (SpecialLinearGroup.map sigma.toRingHom X) := by
    intro Y
    change OddFieldLift.slCoordinateAction F (eta (MulAut.conjNormal e (eta.symm Y))) = _
    rw [heta, MulAut.conjNormal_apply, map_mul, map_mul, map_inv, he,
      ← heta (eta.symm Y), eta.apply_symm_apply]
    exact (OddFieldLift.slCoordinateAction_field F sigma Y).symm
  have h := DFunLike.congr_fun (OddFieldLift.hom_eq_of_projective_eq p hp alpha
    (SpecialLinearGroup.map sigma.toRingHom) hproj) X
  have hN : eta.symm (SpecialLinearGroup.map sigma.toRingHom X) =
      MulAut.conjNormal e (eta.symm X) := by
    apply eta.injective
    simpa only [alpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      eta.apply_symm_apply] using h.symm
  change (eta.symm (SpecialLinearGroup.map sigma.toRingHom X) : H) = _
  rw [hN, MulAut.conjNormal_apply]
  rfl

theorem pairLift_field_conjugation [Finite F] {H : Type v} [Group H]
    (p : ℕ) [CharP F p] (hp : Odd p) (A : Subgroup (F ≃+* F))
    (N : Subgroup H) [N.Normal] (eta : N ≃* SL F) (a : (FixedField F A)ˣ)
    (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F N eta (beta F (fixedUnit F A a) X) =
      t * layerLift F N eta X * t⁻¹)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ x : N, OddFieldLift.slCoordinateAction F (eta x) = chi x)
    (e : H) (sigma : A) (he : chi e = fieldExtension F sigma) (het : Commute e t)
    (x : M F (fixedUnit F A a)) :
    pairLift F N eta (fixedUnit F A a) t ht hconj (matrixFieldAction F A a sigma x) =
      e * pairLift F N eta (fixedUnit F A a) t ht hconj x * e⁻¹ := by
  rw [pairLift_formula, pairLift_formula]
  change layerLift F N eta (SpecialLinearGroup.map sigma.val.toRingHom x.left) *
    t ^ exponent x.right = e * ((eta.symm x.left : H) * t ^ exponent x.right) * e⁻¹
  rw [layerLift_field_conjugation F p hp N eta chi heta e sigma he x.left]
  calc
    e * layerLift F N eta x.left * e⁻¹ * t ^ exponent x.right =
        e * layerLift F N eta x.left * (e⁻¹ * t ^ exponent x.right) := by group
    _ = e * layerLift F N eta x.left * (t ^ exponent x.right * e⁻¹) := by
      rw [(het.inv_left.pow_right (exponent x.right)).eq]
    _ = e * ((eta.symm x.left : H) * t ^ exponent x.right) * e⁻¹ := by
      rw [layerLift_apply]
      group

@[expose] def Phi [Finite F] {H : Type v} [Group H]
    (p : ℕ) [CharP F p] (hp : Odd p)
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (hd : Odd (Nat.card A)) (eta : OddFieldLift.Lambda F A pi ≃* SL F)
    (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
      OddFieldLift.coordinateProjection F A pi x)
    (a : (FixedField F A)ˣ) (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F (OddFieldLift.Lambda F A pi) eta
      (beta F (fixedUnit F A a) X) = t * layerLift F (OddFieldLift.Lambda F A pi) eta X * t⁻¹)
    (hcentral : ∀ e : OddFieldLift.E F A pi z hzc hker, Commute (e : H) t) :
    MatrixFieldModel F A a →* H :=
  SemidirectProduct.lift (pairLift F (OddFieldLift.Lambda F A pi) eta (fixedUnit F A a)
    t ht hconj) (originalFieldLift F A pi hpi z hz hzc hker hd) (by
      intro sigma
      apply MonoidHom.ext
      intro x
      exact pairLift_field_conjugation F p hp A _ eta a t ht hconj
        (OddFieldLift.coordinateProjection F A pi) heta _ sigma
        (OddFieldLift.eSigma_projective F A pi hpi z hz hzc hker hd sigma)
        (hcentral (OddFieldLift.eSigma F A pi hpi z hz hzc hker hd sigma)) x)

theorem Phi_formula [Finite F] {H : Type v} [Group H]
    (p : ℕ) [CharP F p] (hp : Odd p)
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (hd : Odd (Nat.card A)) (eta : OddFieldLift.Lambda F A pi ≃* SL F)
    (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
      OddFieldLift.coordinateProjection F A pi x)
    (a : (FixedField F A)ˣ) (t : H) (ht : t ^ 2 = 1)
    (hconj : ∀ X : SL F, layerLift F (OddFieldLift.Lambda F A pi) eta
      (beta F (fixedUnit F A a) X) = t * layerLift F (OddFieldLift.Lambda F A pi) eta X * t⁻¹)
    (hcentral : ∀ e : OddFieldLift.E F A pi z hzc hker, Commute (e : H) t)
    (x : MatrixFieldModel F A a) :
    Phi F p hp A pi hpi z hz hzc hker hd eta heta a t ht hconj hcentral x =
      (eta.symm x.left.left : H) * t ^ exponent x.left.right *
        (OddFieldLift.eSigma F A pi hpi z hz hzc hker hd x.right : H) := rfl


section FullMap

variable [Finite F] {H : Type v} [Group H]
variable (p : ℕ) [CharP F p] (hp : Odd p)
variable (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
variable (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
variable (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
variable (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
variable (hd : Odd (Nat.card A)) (eta : OddFieldLift.Lambda F A pi ≃* SL F)
variable (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
  OddFieldLift.coordinateProjection F A pi x)
variable (a : (FixedField F A)ˣ) (ha : ¬IsSquare a) (t : H) (ht : t ^ 2 = 1)
variable (hout : t ∉ OddFieldLift.Lambda F A pi)
variable (himage : OddFieldLift.coordinateProjection F A pi t =
  (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)))
variable (hconj : ∀ X : SL F, layerLift F (OddFieldLift.Lambda F A pi) eta
  (beta F (fixedUnit F A a) X) = t * layerLift F (OddFieldLift.Lambda F A pi) eta X * t⁻¹)
variable (hcentral : ∀ e : OddFieldLift.E F A pi z hzc hker, Commute (e : H) t)

include hF ha hout himage in
theorem Phi_bijective : Function.Bijective
    (Phi F p hp A pi hpi z hz hzc hker hd eta heta a t ht hconj hcentral) := by
  let em := pairEquiv F hF A pi eta (fixedUnit F A a)
    (fixed_nonsquare_retained F A hd a ha) t ht hout hconj heta himage
  let ee := (OddFieldLift.EEquivField F A pi hpi z hz hzc hker hd).symm
  let e : MatrixFieldModel F A a ≃
      OddFieldLift.M F A pi × OddFieldLift.E F A pi z hzc hker :=
    SemidirectProduct.equivProd.trans (em.toEquiv.prodCongr ee.toEquiv)
  have hc := (Subgroup.isComplement_iff_bijective _ _).mp
    (OddFieldLift.H_isComplement F A pi hpi z hz hzc hker hd)
  change Function.Bijective (fun y : OddFieldLift.M F A pi ×
    OddFieldLift.E F A pi z hzc hker => (y.1 : H) * (y.2 : H)) at hc
  exact hc.comp e.bijective

@[expose] def PhiEquiv : MatrixFieldModel F A a ≃* H :=
  MulEquiv.ofBijective
    (Phi F p hp A pi hpi z hz hzc hker hd eta heta a t ht hconj hcentral)
    (Phi_bijective F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral)

theorem PhiEquiv_formula (x : MatrixFieldModel F A a) :
    PhiEquiv F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral x =
      (eta.symm x.left.left : H) * t ^ exponent x.left.right *
        (OddFieldLift.eSigma F A pi hpi z hz hzc hker hd x.right : H) := rfl

theorem PhiEquiv_projective (x : MatrixFieldModel F A a) :
    OddFieldLift.coordinateProjection F A pi
      (PhiEquiv F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral x) =
      (MatrixCoverData.pi F (fixedUnit F A a) x.left : Equiv.Perm (Omega F)) *
        fieldExtension F x.right := by
  change OddFieldLift.coordinateProjection F A pi
    (pairLift F _ eta (fixedUnit F A a) t ht hconj x.left *
      originalFieldLift F A pi hpi z hz hzc hker hd x.right) = _
  rw [map_mul, pairLift_projective F _ eta (fixedUnit F A a) t ht hconj _ heta himage]
  congr 1
  exact OddFieldLift.eSigma_projective F A pi hpi z hz hzc hker hd x.right

theorem PhiEquiv_matrix_range :
    ((PhiEquiv F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral).toMonoidHom.comp
      ((SemidirectProduct.inl : M F (fixedUnit F A a) →* MatrixFieldModel F A a).comp
        (inclusion F (fixedUnit F A a)))).range = OddFieldLift.Lambda F A pi := by
  have h : (PhiEquiv F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral).toMonoidHom.comp
      ((SemidirectProduct.inl : M F (fixedUnit F A a) →* MatrixFieldModel F A a).comp
        (inclusion F (fixedUnit F A a))) = layerLift F _ eta := by
    apply MonoidHom.ext
    intro X
    change Phi F p hp A pi hpi z hz hzc hker hd eta heta a t ht hconj hcentral
      (SemidirectProduct.inl (inclusion F (fixedUnit F A a) X)) = _
    rw [Phi, SemidirectProduct.lift_inl, pairLift, inclusion, SemidirectProduct.lift_inl]
  rw [h]
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    exact (eta.symm X).property
  · intro x hx
    exact ⟨eta ⟨x, hx⟩, congrArg Subtype.val (eta.symm_apply_apply ⟨x, hx⟩)⟩

theorem PhiEquiv_field_range :
    ((PhiEquiv F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral).toMonoidHom.comp
      (SemidirectProduct.inr : A →* MatrixFieldModel F A a)).range =
        OddFieldLift.E F A pi z hzc hker := by
  have h : (PhiEquiv F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral).toMonoidHom.comp
      (SemidirectProduct.inr : A →* MatrixFieldModel F A a) =
        originalFieldLift F A pi hpi z hz hzc hker hd := by
    apply MonoidHom.ext
    intro sigma
    change Phi F p hp A pi hpi z hz hzc hker hd eta heta a t ht hconj hcentral
      (SemidirectProduct.inr sigma) = _
    rw [Phi, SemidirectProduct.lift_inr]
  rw [h]
  apply le_antisymm
  · rintro _ ⟨sigma, rfl⟩
    exact (OddFieldLift.eSigma F A pi hpi z hz hzc hker hd sigma).property
  · intro e he
    let ee : OddFieldLift.E F A pi z hzc hker := ⟨e, he⟩
    refine ⟨OddFieldLift.EEquivField F A pi hpi z hz hzc hker hd ee, ?_⟩
    exact congrArg Subtype.val
      ((OddFieldLift.EEquivField F A pi hpi z hz hzc hker hd).symm_apply_apply ee)

theorem PhiEquiv_minusIdentity (hzN : z ∈ OddFieldLift.Lambda F A pi)
    (hetaz : eta ⟨z, hzN⟩ = OddFieldSL2.minusIdentity F) :
    PhiEquiv F p hp hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage hconj hcentral
      (SemidirectProduct.inl (inclusion F (fixedUnit F A a) (OddFieldSL2.minusIdentity F))) = z := by
  change Phi F p hp A pi hpi z hz hzc hker hd eta heta a t ht hconj hcentral
    (SemidirectProduct.inl (inclusion F (fixedUnit F A a) (OddFieldSL2.minusIdentity F))) = _
  rw [Phi, SemidirectProduct.lift_inl, pairLift, inclusion, SemidirectProduct.lift_inl]
  change (eta.symm (OddFieldSL2.minusIdentity F) : H) = z
  rw [← hetaz, eta.symm_apply_apply]

end FullMap


theorem central_involution_mem_sylow {H : Type v} [Group H] (z : H)
    (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H) (S : Sylow 2 H) : z ∈ S := by
  let : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center
    (Subgroup.zpowers_le.mpr hzc)
  have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by
    rw [Nat.card_zpowers, hz, pow_one]
  exact (IsPGroup.of_card hcard).le_sylow_of_normal S (Subgroup.mem_zpowers z)

theorem semidihedral_sylow_noncentral_involution {H : Type v} [Group H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n)
    (e : (S : Subgroup H) ≃* CFSG.Open.SemidihedralGroup n) :
    ∃ s : H, s ∈ S ∧ orderOf s = 2 ∧
      ∀ z : H, z ∈ Subgroup.center H → s ≠ z := by
  let s0 := e.symm (CFSG.Semidihedral.s n)
  have hs : orderOf (s0 : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (e.symm.orderOf_eq _).trans (semidihedral_reflection n hn).1
  refine ⟨s0, s0.property, hs, ?_⟩
  intro z hzc hsz
  have hc : s0 ∈ Subgroup.center (S : Subgroup H) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    change (x : H) * (s0 : H) = (s0 : H) * (x : H)
    rw [hsz]
    exact Subgroup.mem_center_iff.mp hzc x
  have hce : CFSG.Semidihedral.s n ∈ Subgroup.center (CFSG.Open.SemidihedralGroup n) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg e (Subgroup.mem_center_iff.mp hc (e.symm x))
    simpa only [map_mul, e.apply_symm_apply, s0] using h
  exact (semidihedral_reflection n hn).2 hce

theorem semidihedral_sylow_outer_involution [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z)
    (eta : OddFieldLift.Lambda F A pi ≃* SL F)
    (hetaz : eta ⟨z, kernel_le_Lambda F A pi (by rw [hker]; exact Subgroup.mem_zpowers z)⟩ =
      OddFieldSL2.minusIdentity F) (h2 : (2 : F) ≠ 0)
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n)
    (e : (S : Subgroup H) ≃* CFSG.Open.SemidihedralGroup n) :
    ∃ s : H, s ∈ S ∧ orderOf s = 2 ∧ s ∉ OddFieldLift.Lambda F A pi ∧
      orderOf (OddFieldLift.coordinateProjection F A pi s) = 2 := by
  obtain ⟨s, hs, hso, hsn⟩ := semidihedral_sylow_noncentral_involution S n hn e
  have hout : s ∉ OddFieldLift.Lambda F A pi := by
    intro hN
    have heq := layer_unique_involution F _ eta
      ⟨z, kernel_le_Lambda F A pi (by rw [hker]; exact Subgroup.mem_zpowers z)⟩
      hetaz h2 ⟨s, hN⟩ (by simpa only [Subgroup.orderOf_mk] using hso)
    exact hsn z hzc (congrArg Subtype.val heq)
  have hsq : (OddFieldLift.coordinateProjection F A pi s) ^ 2 = 1 := by
    rw [← map_pow]
    have h : s ^ 2 = 1 := by simpa only [hso] using pow_orderOf_eq_one s
    rw [h, map_one]
  have hne : OddFieldLift.coordinateProjection F A pi s ≠ 1 := by
    intro h1
    apply hout
    apply kernel_le_Lambda F A pi
    rw [← coordinateProjection_ker, MonoidHom.mem_ker]
    exact h1
  exact ⟨s, hs, hso, hout, orderOf_eq_prime hsq hne⟩

open CFSG.GorensteinWalter
open scoped commutatorElement

theorem gamma_involution_mem_linear [Finite F] (A : Subgroup (F ≃+* F))
    (hd : Odd (Nat.card A)) (g : OddFieldLift.Gamma F A) (hg : g ^ 2 = 1) :
    g ∈ OddFieldLift.gammaLinear F A := by
  let x := (OddFieldLift.gammaSemidirectEquiv F A).symm g
  have hx2 : x ^ 2 = 1 := by
    change ((OddFieldLift.gammaSemidirectEquiv F A).symm g) ^ 2 = 1
    rw [← map_pow, hg, map_one]
  have hr2 : x.right ^ 2 = 1 := by
    change (SemidirectProduct.rightHom x) ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  have hrc := pow_card_eq_one' (x := x.right)
  have hodd : Odd (Nat.card (OddFieldLift.gammaField F A)) := by
    rw [OddFieldLift.gammaField_card]
    exact hd
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, hr2, one_pow, one_mul] at hrc
  have hprod : g = (x.left : OddFieldLift.Gamma F A) * (x.right : OddFieldLift.Gamma F A) := by
    calc
      g = OddFieldLift.gammaSemidirectEquiv F A x :=
        ((OddFieldLift.gammaSemidirectEquiv F A).apply_symm_apply g).symm
      _ = _ := SemilinearOddExtensions.internalSemidirectEquiv_apply _ _ _ x
  rw [hrc, Subgroup.coe_one, mul_one] at hprod
  rw [hprod]
  exact x.left.property

theorem glProjective_field [Finite F] (sigma : F ≃+* F) (V : GL2 F) :
    (glProjective F (GeneralLinearGroup.map sigma.toRingHom V) : Equiv.Perm (Omega F)) =
      fieldExtension F sigma * (glProjective F V : Equiv.Perm (Omega F)) *
        (fieldExtension F sigma)⁻¹ := by
  have h := congrArg (coordinateSemilinearAction F)
    (SemidirectProduct.inl_aut (φ := pgl2FieldAut F) sigma (Matrix.ProjGenLinGroup.mk V))
  simp only [map_mul, map_inv, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr] at h
  rw [pgl2FieldAut_apply] at h
  change coordinatePGLAction F (pgl2RingEquiv sigma (QuotientGroup.mk' _ V)) = _ at h
  rw [pgl2RingEquiv_mk] at h
  exact h

theorem fixed_jProjective_commute [Finite F] (A : Subgroup (F ≃+* F))
    (a : (FixedField F A)ˣ) (sigma : A) :
    Commute (fieldExtension F sigma)
      (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) := by
  have ha : Units.map (sigma : F ≃+* F).toMonoidHom (fixedUnit F A a) = fixedUnit F A a := by
    apply Units.ext
    exact (a : FixedField F A).property sigma
  have h := glProjective_field F sigma (J F (fixedUnit F A a))
  rw [field_map_J, ha] at h
  change (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) =
    fieldExtension F sigma * (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) *
      (fieldExtension F sigma)⁻¹ at h
  show fieldExtension F sigma * (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) =
    (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) * fieldExtension F sigma
  have hm := congrArg (fun v : Equiv.Perm (Omega F) => v * fieldExtension F sigma) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm

theorem fixed_jLift_centralizes_E [Finite F] {H : Type v} [Group H]
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (hd : Odd (Nat.card A)) (a : (FixedField F A)ˣ) (t : H)
    (ht : OddFieldLift.coordinateProjection F A pi t =
      (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F))) :
    ∀ e : OddFieldLift.E F A pi z hzc hker, Commute (e : H) t := by
  intro e
  let sigma := OddFieldLift.EEquivField F A pi hpi z hz hzc hker hd e
  have he : OddFieldLift.coordinateProjection F A pi e = fieldExtension F sigma := by
    have he' := (OddFieldLift.EEquivField F A pi hpi z hz hzc hker hd).symm_apply_apply e
    have hp := OddFieldLift.eSigma_projective F A pi hpi z hz hzc hker hd sigma
    change OddFieldLift.coordinateProjection F A pi
      ((OddFieldLift.EEquivField F A pi hpi z hz hzc hker hd).symm sigma) = _ at hp
    rw [he'] at hp
    exact hp
  have hk : pi ⁅(e : H), t⁆ = 1 := by
    apply quotient_coordinates_injective F A
    change OddFieldLift.coordinateProjection F A pi ⁅(e : H), t⁆ = 1
    rw [map_commutatorElement, he, ht]
    exact commutatorElement_eq_one_iff_commute.mpr (fixed_jProjective_commute F A a sigma)
  have hc : Commute (e : H) ⁅(e : H), t⁆ :=
    Subgroup.mem_center_iff.mp (OddFieldLift.kernel_central pi z hzc hker hk) e
  have hepow := ((OddFieldLift.mem_E F A pi z hzc hker e).mp e.property).2
  have hpow : ⁅(e : H), t⁆ ^ Nat.card A = 1 := by
    rw [hc.commutatorElement_pow_left, hepow, commutatorElement_one_left]
  exact commutatorElement_eq_one_iff_commute.mp
    (OddFieldLift.odd_kernel_identity pi z hz hker (Nat.card A) hd hk hpow)

set_option maxHeartbeats 800000 in
theorem exists_exact_jLift [Finite F] {H : Type v} [Group H]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (A : Subgroup (F ≃+* F)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z)
    (eta : OddFieldLift.Lambda F A pi ≃* SL F)
    (hetaz : eta ⟨z, kernel_le_Lambda F A pi (by rw [hker]; exact Subgroup.mem_zpowers z)⟩ =
      OddFieldSL2.minusIdentity F) (h2 : (2 : F) ≠ 0)
    (hd : Odd (Nat.card A)) (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n)
    (e : (S : Subgroup H) ≃* CFSG.Open.SemidihedralGroup n)
    (a : (FixedField F A)ˣ) (ha : ¬IsSquare a) :
    ∃ t : H, orderOf t = 2 ∧ t ∉ OddFieldLift.Lambda F A pi ∧
      OddFieldLift.coordinateProjection F A pi t =
        (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) := by
  obtain ⟨s, _, hso, hsout, hsproj⟩ :=
    semidihedral_sylow_outer_involution F A pi z hzc hker eta hetaz h2 S n hn e
  have hs2 : s ^ 2 = 1 := by simpa only [hso] using pow_orderOf_eq_one s
  have hsD : OddFieldLift.coordinateProjection F A pi s ∈ coordinateD F := by
    exact gamma_involution_mem_linear F A hd (pi s) (by rw [← map_pow, hs2, map_one])
  have haF := fixed_nonsquare_retained F A hd a ha
  obtain ⟨d, hdconj⟩ := ProjectiveNonsquareInvolutions.projective_nonsquare_involutions_are_conjugate
    F hF (fixedUnit F A a) haF ⟨OddFieldLift.coordinateProjection F A pi s, hsD⟩
    (fun h => hsout ((mem_Lambda_iff F A pi s).mpr h))
    (by simpa only [Subgroup.orderOf_mk] using hsproj)
  let dg : OddFieldLift.Gamma F A :=
    ⟨SemilinearOuterQuotient.linearInclusion F d, (show SemilinearOddExtensions.linearLayer F ≤
      OddFieldLift.Gamma F A from le_sup_left) (show
      SemilinearOuterQuotient.linearInclusion F d ∈ SemilinearOddExtensions.linearLayer F from
        d.property)⟩
  obtain ⟨h, hh⟩ := hpi dg
  let t := h * s * h⁻¹
  have htimage : OddFieldLift.coordinateProjection F A pi t =
      (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) := by
    change OddFieldLift.coordinateProjection F A pi (h * s * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    have hp : OddFieldLift.coordinateProjection F A pi h = (d : Equiv.Perm (Omega F)) := by
      change (((pi h : OddFieldLift.Gamma F A) : coordinateE F) : Equiv.Perm (Omega F)) = _
      rw [hh]
      rfl
    rw [hp]
    exact congrArg Subtype.val hdconj
  have htout : t ∉ OddFieldLift.Lambda F A pi := by
    intro htmem
    have hj := (ProjectiveNonsquareInvolutions.jProjective_outer_involution F
      (fixedUnit F A a) haF).1
    exact hj (htimage ▸ (mem_Lambda_iff F A pi t).mp htmem)
  have ht2 : t ^ 2 = 1 := by
    change (h * s * h⁻¹) ^ 2 = 1
    rw [conj_pow, hs2]
    group
  have htne : t ≠ 1 := fun ht1 => htout (ht1 ▸ (OddFieldLift.Lambda F A pi).one_mem)
  exact ⟨t, orderOf_eq_prime ht2 htne, htout, htimage⟩

theorem semidihedral_local_cover_exact_matrix_field_model [Finite F]
    {H : Type v} [Group H] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (A : Subgroup (F ≃+* F))
    (hd : Odd (Nat.card A)) (pi : H →* OddFieldLift.Gamma F A)
    (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (eta : OddFieldLift.Lambda F A pi ≃* SL F)
    (hetaz : eta ⟨z, kernel_le_Lambda F A pi (by rw [hker]; exact Subgroup.mem_zpowers z)⟩ =
      OddFieldSL2.minusIdentity F)
    (heta : ∀ x : OddFieldLift.Lambda F A pi, OddFieldLift.slCoordinateAction F (eta x) =
      OddFieldLift.coordinateProjection F A pi x)
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n)
    (e : (S : Subgroup H) ≃* CFSG.Open.SemidihedralGroup n)
    (a : (FixedField F A)ˣ) (ha : ¬IsSquare a) :
    ¬IsSquare (fixedUnit F A a) ∧
    (∀ sigma : A, ∃! e : OddFieldLift.E F A pi z hzc hker,
      OddFieldLift.coordinateProjection F A pi e = fieldExtension F sigma) ∧
    ∃ t : H, orderOf t = 2 ∧
      t ∈ Subgroup.centralizer (OddFieldLift.E F A pi z hzc hker : Set H) ∧
      t ∉ OddFieldLift.Lambda F A pi ∧
      OddFieldLift.coordinateProjection F A pi t =
        (jProjective F (fixedUnit F A a) : Equiv.Perm (Omega F)) ∧
      ∃ phi : MatrixFieldModel F A a ≃* H,
        (∀ x : MatrixFieldModel F A a, phi x =
          (eta.symm x.left.left : H) * t ^ exponent x.left.right *
            (OddFieldLift.eSigma F A pi hpi z hz hzc hker hd x.right : H)) ∧
        phi (SemidirectProduct.inl
          (inclusion F (fixedUnit F A a) (OddFieldSL2.minusIdentity F))) = z ∧
        (phi.toMonoidHom.comp
          ((SemidirectProduct.inl : M F (fixedUnit F A a) →* MatrixFieldModel F A a).comp
            (inclusion F (fixedUnit F A a)))).range = OddFieldLift.Lambda F A pi ∧
        (phi.toMonoidHom.comp
          (SemidirectProduct.inr : A →* MatrixFieldModel F A a)).range =
            OddFieldLift.E F A pi z hzc hker ∧
        (∀ x : MatrixFieldModel F A a,
          OddFieldLift.coordinateProjection F A pi (phi x) =
            coordinatePGLAction F (Matrix.ProjGenLinGroup.mk
              (SpecialLinearGroup.toGL x.left.left *
                J F (fixedUnit F A a) ^ exponent x.left.right)) * fieldExtension F x.right) := by
  let : CharP F p := FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, hcard⟩
  have h2 : (2 : F) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp hzero
    have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hp.ne_one
    exact (by decide : ¬Odd (2 : ℕ)) (hp2 ▸ hpodd)
  obtain ⟨t, hto, hout, himage⟩ := exists_exact_jLift F hF A pi hpi z hzc hker eta
    hetaz h2 hd S n hn e a ha
  have ht : t ^ 2 = 1 := by simpa only [hto] using pow_orderOf_eq_one t
  have hcentral := fixed_jLift_centralizes_E F A pi hpi z hz hzc hker hd a t himage
  have hconj := layerLift_matrix_conjugation F p hpodd (OddFieldLift.Lambda F A pi) eta
    (OddFieldLift.coordinateProjection F A pi) heta (fixedUnit F A a) t himage
  let phi := PhiEquiv F p hpodd hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout himage
    hconj hcentral
  refine ⟨fixed_nonsquare_retained F A hd a ha,
    original_eSigma_unique F A pi hpi z hz hzc hker hd, t, hto, ?_, hout, himage,
    phi, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcentral ⟨x, hx⟩).eq)
  · exact PhiEquiv_formula F p hpodd hF A pi hpi z hz hzc hker hd eta heta a ha t ht hout
      himage hconj hcentral
  · exact PhiEquiv_minusIdentity F p hpodd hF A pi hpi z hz hzc hker hd eta heta a ha t ht
      hout himage hconj hcentral _ hetaz
  · exact PhiEquiv_matrix_range F p hpodd hF A pi hpi z hz hzc hker hd eta heta a ha t ht
      hout himage hconj hcentral
  · exact PhiEquiv_field_range F p hpodd hF A pi hpi z hz hzc hker hd eta heta a ha t ht
      hout himage hconj hcentral
  · intro x
    have hx := PhiEquiv_projective F p hpodd hF A pi hpi z hz hzc hker hd eta heta a ha t ht
      hout himage hconj hcentral x
    rw [MatrixCoverData.pi_coordinate] at hx
    exact hx

end

end CFSG.Semidihedral.MatrixCover
