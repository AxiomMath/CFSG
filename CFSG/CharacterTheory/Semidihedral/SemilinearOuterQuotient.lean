module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateQuotients
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public section

namespace CFSG.Semidihedral.SemilinearOuterQuotient

noncomputable section

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

universe u

abbrev SquareClass (K : Type u) [Field K] := Kˣ ⧸ Subgroup.square Kˣ

@[expose] def squareClassMap (K : Type u) [Field K] : Kˣ →* SquareClass K :=
  QuotientGroup.mk' (Subgroup.square Kˣ)

theorem squareClassMap_eq_one (K : Type u) [Field K] (a : Kˣ) :
    squareClassMap K a = 1 ↔ IsSquare a := by
  change a ∈ (squareClassMap K).ker ↔ _
  rw [squareClassMap, QuotientGroup.ker_mk', Subgroup.mem_square]

theorem isSquare_unit_iff {K : Type u} [Field K] (a : Kˣ) :
    IsSquare a ↔ IsSquare (a : K) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(b : K), congrArg Units.val hb⟩
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      intro h
      exact a.ne_zero (by simp [h] at hb)
    exact ⟨Units.mk0 b hb0, Units.ext hb⟩

@[expose] def pglDet (K : Type u) [Field K] : PGL2 K →* SquareClass K :=
  Matrix.ProjGenLinGroup.lift
    ((squareClassMap K).comp Matrix.GeneralLinearGroup.det) (by
      ext a
      change squareClassMap K (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = 1
      rw [Matrix.GeneralLinearGroup.det_scalar]
      apply (squareClassMap_eq_one K _).mpr
      exact ⟨a, by simp [pow_two]⟩)

theorem pglDet_mk (K : Type u) [Field K]
    (a : Matrix.GeneralLinearGroup (Fin 2) K) :
    pglDet K (Matrix.ProjGenLinGroup.mk a) = squareClassMap K a.det := rfl

theorem pglDet_ker (K : Type u) [Field K] :
    (pglDet K).ker =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  ext g
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk a =>
    rw [MonoidHom.mem_ker, pglDet_mk, squareClassMap_eq_one, isSquare_unit_iff,
      pgl2_mk_mem_psl2_range_iff_det_isSquare]

theorem pglDet_surjective (K : Type u) [Field K] :
    Function.Surjective (pglDet K) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.square Kˣ) q
  exact ⟨Matrix.ProjGenLinGroup.mk (diagonalGL K a), by
    rw [pglDet_mk, diagonalGL_det]; rfl⟩

theorem squareClass_card_two (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : Nat.card (SquareClass K) = 2 := by
  let H := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  let : H.Normal := pglPSLRange_normal K
  let e : PGL2 K ⧸ H ≃* SquareClass K :=
    QuotientGroup.liftEquiv H (pglDet_surjective K) (pglDet_ker K).symm
  rw [← Nat.card_congr e.toEquiv, ← Subgroup.index_eq_card]
  exact pgl2_psl2Range_index_eq_two K hK

@[expose] def ringAutEquivAlgAut (K : Type u) [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  exact {
    toFun := fun sigma => AlgEquiv.ofRingEquiv (f := sigma) (by
      intro x
      exact DFunLike.congr_fun (RingHom.ext_zmod
        (sigma.toRingHom.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K)) x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }

theorem fieldAut_card (K : Type u) [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hcard : Nat.card K = p ^ f) :
    Nat.card (K ≃+* K) = f := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow
    (show Fintype.card K = p ^ f by simpa [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod p) K := ZMod.algebra K p
  rw [Nat.card_congr (ringAutEquivAlgAut K p).toEquiv,
    IsGalois.card_aut_eq_finrank]
  apply Nat.pow_right_injective hp.two_le
  change p ^ Module.finrank (ZMod p) K = p ^ f
  rw [FiniteField.pow_finrank_eq_natCard, hcard]

theorem eq_of_nonone_of_card_two {H : Type u} [Group H]
    (hcard : Nat.card H = 2) {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨c, _hc, hu⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  exact (hu a ha).trans (hu b hb).symm

theorem isSquare_field_map_iff {K : Type u} [Field K]
    (sigma : K ≃+* K) (a : Kˣ) :
    IsSquare (Units.map sigma.toMonoidHom a) ↔ IsSquare a := by
  rw [isSquare_unit_iff, isSquare_unit_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨sigma.symm b, by simpa using congrArg sigma.symm hb⟩
  · exact IsSquare.map sigma

theorem squareClassMap_field (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (sigma : K ≃+* K) (a : Kˣ) :
    squareClassMap K (Units.map sigma.toMonoidHom a) = squareClassMap K a := by
  have h : squareClassMap K (Units.map sigma.toMonoidHom a) = 1 ↔
      squareClassMap K a = 1 := by
    rw [squareClassMap_eq_one, squareClassMap_eq_one, isSquare_field_map_iff]
  by_cases ha : squareClassMap K a = 1
  · exact (h.mpr ha).trans ha.symm
  · exact eq_of_nonone_of_card_two (squareClass_card_two K hK)
      (fun hc => ha (h.mp hc)) ha

theorem pglDet_field (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (sigma : K ≃+* K) (g : PGL2 K) :
    pglDet K (pgl2FieldAut K sigma g) = pglDet K g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk a =>
    rw [pgl2FieldAut_apply,
      show pgl2RingEquiv sigma (Matrix.ProjGenLinGroup.mk a) =
        Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom a)
        from pgl2RingEquiv_mk sigma a, pglDet_mk, pglDet_mk,
      Matrix.GeneralLinearGroup.map_det]
    exact squareClassMap_field K hK sigma a.det

@[expose] def fieldLift (K : Type u) [Field K] [Finite K] :
    (K ≃+* K) →* coordinateE K :=
  (semilinearEquivCoordinateE K).toMonoidHom.comp SemidirectProduct.inr

theorem fieldLift_coe (K : Type u) [Field K] [Finite K] (sigma : K ≃+* K) :
    (fieldLift K sigma : Equiv.Perm (Omega K)) = fieldExtension K sigma :=
  coordinateSemilinearAction_inr K sigma

@[expose] def linearInclusion (K : Type u) [Field K] :
    coordinateD K →* coordinateE K := Subgroup.inclusion (coordinateD_le_E K)

theorem linearInclusion_coe (K : Type u) [Field K] (d : coordinateD K) :
    (linearInclusion K d : Equiv.Perm (Omega K)) = d :=
  Subgroup.coe_inclusion (coordinateD_le_E K) d

@[expose] def fieldProjection (K : Type u) [Field K] [Finite K] :
    coordinateE K →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearEquivCoordinateE K).symm.toMonoidHom

theorem fieldProjection_fieldLift (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) : fieldProjection K (fieldLift K sigma) = sigma := by
  simp [fieldProjection, fieldLift]

theorem fieldProjection_surjective (K : Type u) [Field K] [Finite K] :
    Function.Surjective (fieldProjection K) :=
  fun sigma => ⟨fieldLift K sigma, fieldProjection_fieldLift K sigma⟩

theorem linearInclusion_pgl (K : Type u) [Field K] [Finite K] (g : PGL2 K) :
    linearInclusion K (pglEquivCoordinateD K g) =
      semilinearEquivCoordinateE K (SemidirectProduct.inl g) := by
  apply Subtype.ext
  exact (coordinateSemilinearAction_inl K g).symm

theorem fieldProjection_linear (K : Type u) [Field K] [Finite K] (d : coordinateD K) :
    fieldProjection K (linearInclusion K d) = 1 := by
  obtain ⟨g, rfl⟩ := (pglEquivCoordinateD K).surjective d
  rw [linearInclusion_pgl]
  simp [fieldProjection]

theorem fieldProjection_ker (K : Type u) [Field K] [Finite K] :
    (fieldProjection K).ker = (coordinateD K).subgroupOf (coordinateE K) := by
  change (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).ker.comap
    (semilinearEquivCoordinateE K).symm.toMonoidHom = _
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom,
    Subgroup.comap_equiv_eq_map_symm']
  exact semilinearPGLRange_map K

@[expose] def linearPart (K : Type u) [Field K] [Finite K] (e : coordinateE K) :
    coordinateD K := pglEquivCoordinateD K ((semilinearEquivCoordinateE K).symm e).left

theorem coordinate_decomposition (K : Type u) [Field K] [Finite K] (e : coordinateE K) :
    e = linearInclusion K (linearPart K e) * fieldLift K (fieldProjection K e) := by
  let x := (semilinearEquivCoordinateE K).symm e
  change e = linearInclusion K (pglEquivCoordinateD K x.left) * fieldLift K x.right
  calc
    e = semilinearEquivCoordinateE K x :=
      ((semilinearEquivCoordinateE K).apply_symm_apply e).symm
    _ = semilinearEquivCoordinateE K
        (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) :=
      congrArg (semilinearEquivCoordinateE K)
        (SemidirectProduct.inl_left_mul_inr_right x).symm
    _ = _ := by rw [map_mul, ← linearInclusion_pgl]; rfl

theorem coordinate_decomposition_coe (K : Type u) [Field K] [Finite K]
    (e : coordinateE K) : (e : Equiv.Perm (Omega K)) =
      (linearPart K e : Equiv.Perm (Omega K)) * fieldExtension K (fieldProjection K e) := by
  have h := congrArg (fun g : coordinateE K => (g : Equiv.Perm (Omega K)))
    (coordinate_decomposition K e)
  rw [Subgroup.coe_mul, linearInclusion_coe, fieldLift_coe] at h
  exact h

theorem coordinate_normal_form_unique (K : Type u) [Field K] [Finite K]
    {d t : coordinateD K} {sigma tau : K ≃+* K}
    (h : (d : Equiv.Perm (Omega K)) * fieldExtension K sigma =
      (t : Equiv.Perm (Omega K)) * fieldExtension K tau) : d = t ∧ sigma = tau := by
  have he : linearInclusion K d * fieldLift K sigma =
      linearInclusion K t * fieldLift K tau := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, linearInclusion_coe, fieldLift_coe] using h
  have hs : sigma = tau := by
    have hh := congrArg (fieldProjection K) he
    simpa only [map_mul, fieldProjection_linear, fieldProjection_fieldLift, one_mul] using hh
  refine ⟨Subtype.ext ?_, hs⟩
  rw [hs] at h
  exact mul_right_cancel h

theorem coordinate_normal_form (K : Type u) [Field K] [Finite K] (e : coordinateE K) :
    ∃! ds : coordinateD K × (K ≃+* K),
      (e : Equiv.Perm (Omega K)) = ds.1 * fieldExtension K ds.2 := by
  refine ⟨(linearPart K e, fieldProjection K e), coordinate_decomposition_coe K e, ?_⟩
  rintro ⟨d, sigma⟩ h
  have hh := coordinate_normal_form_unique K (h.symm.trans (coordinate_decomposition_coe K e))
  exact Prod.ext hh.1 hh.2

@[expose] def semilinearTheta (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    PGammaL2 K →* SquareClass K × (K ≃+* K) where
  toFun x := (pglDet K x.left, x.right)
  map_one' := by simp
  map_mul' x y := by
    apply Prod.ext
    · simp only [SemidirectProduct.mul_left, map_mul, Prod.fst_mul]
      rw [pglDet_field K hK]
    · rfl

theorem semilinearTheta_ker (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    (semilinearTheta K hK).ker = pGammaL2PSLRange K := by
  ext x
  constructor
  · intro hx
    have hh : (pglDet K x.left, x.right) = (1, 1) := hx
    have hl : x.left ∈ (pglDet K).ker := congrArg Prod.fst hh
    rw [pglDet_ker] at hl
    obtain ⟨y, hy⟩ := hl
    exact (mem_pGammaL2PSLRange_iff K x).mpr
      ⟨y, SemidirectProduct.ext hy (congrArg Prod.snd hh).symm⟩
  · rintro ⟨y, rfl⟩
    change (pglDet K (Matrix.ProjectiveSpecialLinearGroup.toPGL y), 1) = (1, 1)
    apply Prod.ext
    · exact (show Matrix.ProjectiveSpecialLinearGroup.toPGL y ∈ (pglDet K).ker by
        rw [pglDet_ker]; exact ⟨y, rfl⟩)
    · rfl

theorem semilinearTheta_surjective (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    Function.Surjective (semilinearTheta K hK) := by
  rintro ⟨q, sigma⟩
  obtain ⟨g, hg⟩ := pglDet_surjective K q
  exact ⟨⟨g, sigma⟩, Prod.ext hg rfl⟩

@[expose] def theta (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    coordinateE K →* SquareClass K × (K ≃+* K) :=
  (semilinearTheta K hK).comp (semilinearEquivCoordinateE K).symm.toMonoidHom

theorem theta_ker (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    (theta K hK).ker = (coordinateG K).subgroupOf (coordinateE K) := by
  change (semilinearTheta K hK).ker.comap
    (semilinearEquivCoordinateE K).symm.toMonoidHom = _
  rw [semilinearTheta_ker, Subgroup.comap_equiv_eq_map_symm']
  exact semilinearPSLRange_map K

theorem theta_surjective (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : Function.Surjective (theta K hK) :=
  (semilinearTheta_surjective K hK).comp (semilinearEquivCoordinateE K).symm.surjective

theorem theta_snd (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : coordinateE K) :
    (theta K hK e).2 = fieldProjection K e := rfl

theorem theta_fieldLift (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (sigma : K ≃+* K) :
    theta K hK (fieldLift K sigma) = (1, sigma) := by
  simp [theta, fieldLift, semilinearTheta]

theorem theta_linear_matrix (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (a : Matrix.GeneralLinearGroup (Fin 2) K) :
    theta K hK (linearInclusion K
      (pglEquivCoordinateD K (Matrix.ProjGenLinGroup.mk a))) =
        (squareClassMap K a.det, 1) := by
  rw [linearInclusion_pgl]
  simp [theta, semilinearTheta, pglDet_mk]

@[expose] def determinantClass (K : Type u) [Field K] [Finite K] :
    coordinateD K →* SquareClass K :=
  (pglDet K).comp (pglEquivCoordinateD K).symm.toMonoidHom

theorem theta_linear (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (d : coordinateD K) :
    theta K hK (linearInclusion K d) = (determinantClass K d, 1) := by
  obtain ⟨g, rfl⟩ := (pglEquivCoordinateD K).surjective d
  rw [linearInclusion_pgl]
  simp [theta, semilinearTheta, determinantClass]

theorem determinantClass_matrix (K : Type u) [Field K] [Finite K]
    (d : coordinateD K) (a : Matrix.GeneralLinearGroup (Fin 2) K)
    (ha : coordinatePGLAction K (Matrix.ProjGenLinGroup.mk a) = d) :
    determinantClass K d = squareClassMap K a.det := by
  have hd : pglEquivCoordinateD K (Matrix.ProjGenLinGroup.mk a) = d :=
    Subtype.ext ha
  rw [← hd]
  simp [determinantClass, pglDet_mk]

theorem theta_presentation (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : coordinateE K)
    (d : coordinateD K) (sigma : K ≃+* K)
    (he : (e : Equiv.Perm (Omega K)) = d * fieldExtension K sigma)
    (a : Matrix.GeneralLinearGroup (Fin 2) K)
    (ha : coordinatePGLAction K (Matrix.ProjGenLinGroup.mk a) = d) :
    theta K hK e = (squareClassMap K a.det, sigma) := by
  have hh : e = linearInclusion K d * fieldLift K sigma := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, linearInclusion_coe, fieldLift_coe] using he
  rw [hh, map_mul, theta_linear, theta_fieldLift, determinantClass_matrix K d a ha]
  simp

theorem determinant_presentation_independent (K : Type u) [Field K] [Finite K]
    (a b : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : coordinatePGLAction K (Matrix.ProjGenLinGroup.mk a) =
      coordinatePGLAction K (Matrix.ProjGenLinGroup.mk b)) :
    squareClassMap K a.det = squareClassMap K b.det := by
  have hh := coordinatePGLAction_injective K h
  exact (pglDet_mk K a).symm.trans ((congrArg (pglDet K) hh).trans (pglDet_mk K b))

theorem theta_linear_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    ((coordinateD K).subgroupOf (coordinateE K)).map (theta K hK) =
      (⊤ : Subgroup (SquareClass K)).prod (⊥ : Subgroup (K ≃+* K)) := by
  ext qs
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [← fieldProjection_ker] at he
    change e ∈ (fieldProjection K).ker at he
    constructor
    · trivial
    · exact he
  · rintro ⟨_, hs⟩
    have hs' : qs.2 = 1 := hs
    obtain ⟨g, hg⟩ := pglDet_surjective K qs.1
    refine ⟨linearInclusion K (pglEquivCoordinateD K g), ?_, ?_⟩
    · exact (pglEquivCoordinateD K g).property
    · rw [theta_linear]
      apply Prod.ext
      · simpa [determinantClass] using hg
      · exact hs'.symm

theorem theta_field_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    (fieldLift K).range.map (theta K hK) =
      (⊥ : Subgroup (SquareClass K)).prod (⊤ : Subgroup (K ≃+* K)) := by
  ext qs
  constructor
  · rintro ⟨_, ⟨sigma, rfl⟩, rfl⟩
    rw [theta_fieldLift]
    exact ⟨(⊥ : Subgroup (SquareClass K)).one_mem, trivial⟩
  · rintro ⟨hq, _⟩
    have hq' : qs.1 = 1 := hq
    exact ⟨fieldLift K qs.2, ⟨qs.2, rfl⟩,
      (theta_fieldLift K hK qs.2).trans (Prod.ext hq'.symm rfl)⟩

@[expose] def outerQuotientEquiv (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    CoordinateQuotientEG K ≃* SquareClass K × (K ≃+* K) :=
  QuotientGroup.liftEquiv ((coordinateG K).subgroupOf (coordinateE K))
    (theta_surjective K hK) (theta_ker K hK).symm

theorem outerQuotientEquiv_mk (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : coordinateE K) :
    outerQuotientEquiv K hK (QuotientGroup.mk e) = theta K hK e :=
  QuotientGroup.liftEquiv_mk _ _ _ e

@[expose] def fieldQuotientEquiv (K : Type u) [Field K] [Finite K] :
    CoordinateQuotientED K ≃* (K ≃+* K) :=
  QuotientGroup.liftEquiv ((coordinateD K).subgroupOf (coordinateE K))
    (fieldProjection_surjective K) (fieldProjection_ker K).symm

theorem fieldQuotientEquiv_mk (K : Type u) [Field K] [Finite K] (e : coordinateE K) :
    fieldQuotientEquiv K (QuotientGroup.mk e) = fieldProjection K e :=
  QuotientGroup.liftEquiv_mk _ _ _ e

theorem odd_field_projective_semilinear_exact_outer_quotient
    (K : Type u) [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f) :
    let hK : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hodd, hf, hcard⟩
    Function.Surjective (theta K hK) ∧
      (theta K hK).ker = (coordinateG K).subgroupOf (coordinateE K) ∧
      Nat.card (SquareClass K) = 2 ∧ IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = f ∧
      (∀ e : coordinateE K, ∃! ds : coordinateD K × (K ≃+* K),
        (e : Equiv.Perm (Omega K)) = ds.1 * fieldExtension K ds.2) ∧
      (∀ (e : coordinateE K) (d : coordinateD K) (sigma : K ≃+* K),
        (e : Equiv.Perm (Omega K)) = d * fieldExtension K sigma →
        ∀ a : Matrix.GeneralLinearGroup (Fin 2) K,
          coordinatePGLAction K (Matrix.ProjGenLinGroup.mk a) = d →
          theta K hK e = (squareClassMap K a.det, sigma)) ∧
      ((coordinateD K).subgroupOf (coordinateE K)).map (theta K hK) =
        (⊤ : Subgroup (SquareClass K)).prod ⊥ ∧
      (∀ sigma : K ≃+* K, theta K hK (fieldLift K sigma) = (1, sigma)) ∧
      Function.Surjective (fieldProjection K) ∧
      (fieldProjection K).ker = (coordinateD K).subgroupOf (coordinateE K) := by
  dsimp only
  let hK : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hodd, hf, hcard⟩
  exact ⟨theta_surjective K hK, theta_ker K hK, squareClass_card_two K hK,
    fieldAut_isCyclic K, fieldAut_card K hp hcard, coordinate_normal_form K,
    theta_presentation K hK, theta_linear_image K hK, theta_fieldLift K hK,
    fieldProjection_surjective K, fieldProjection_ker K⟩

end

end CFSG.Semidihedral.SemilinearOuterQuotient
