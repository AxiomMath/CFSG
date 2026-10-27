module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryB

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E]

section Bridge

variable {W : Type*} [AddCommGroup W] [Module E W]

instance generalLinearGroup_finite [Finite E] [FiniteDimensional E W] :
    Finite (LinearMap.GeneralLinearGroup E W) := by
  have : Finite W := Module.finite_of_finite E
  exact Finite.of_injective
    (fun g : LinearMap.GeneralLinearGroup E W => ((g : W →ₗ[E] W) : W → W))
    fun _ _ hgg => Units.ext (LinearMap.ext (congrFun hgg))

theorem nondegenerate_of_isSymm {σ : E →+* E} {C : W →ₛₗ[σ] W →ₗ[E] E} (hC : C.IsSymm)
    (hl : C.SeparatingLeft) : C.Nondegenerate := by
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [← hC.eq x y, hy x, map_zero]

@[expose] def sesqUnitaryIsometryEquiv (h : UnitaryFieldData p f E) [Fact p.Prime]
    [Finite E] (C : W →ₛₗ[h.bar] W →ₗ[E] E) :
    sesqUnitaryGroup C ≃*
      CatalogueBUnitaryIsometry.isometryGroup
        (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C where
  toFun g := ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv E W g, fun x y => g.2 x y⟩
  invFun g := ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv E W).symm g,
    fun x y => g.2 x y⟩
  left_inv _ := Subtype.ext (MulEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (MulEquiv.apply_symm_apply _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem sesqUnitary_pComponent_quasisimple (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E W] (hW : 1 ≤ finrank E W) {C : W →ₛₗ[h.bar] W →ₗ[E] E}
    (hC : C.IsSymm) (hl : C.SeparatingLeft) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (J : Subgroup (sesqUnitaryGroup C)) (hJ : CFSG.IsPComponent ℓ J) : CFSG.IsQuasisimple J := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ
    (sesqUnitaryIsometryEquiv h C)
    ((CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components p f hp h.one_le
      h.card_eq_sq C hC (nondegenerate_of_isSymm hC hl) hW).1 ℓ hℓ) J hJ

theorem generalLinear_pComponent_quasisimple [Finite E] [FiniteDimensional E W]
    (hW : 1 ≤ finrank E W) (ℓ : ℕ) [Fact ℓ.Prime]
    (J : Subgroup (LinearMap.GeneralLinearGroup E W)) (hJ : CFSG.IsPComponent ℓ J) :
    CFSG.IsQuasisimple J :=
  CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E W)
    (CatalogueBOrthogonalLinearFixed.original_generalLinear_pComponent_quasisimple hW ℓ) J hJ

end Bridge

variable {V : Type} [AddCommGroup V] [Module E V]

theorem centralizer_lift_pComponent_quasisimple (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (J : Subgroup (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))))
    (hJ : CFSG.IsPComponent ℓ J) : CFSG.IsQuasisimple J := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, -, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  rcases hN with hN | hN
  · obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ e
      (CatalogueBProjectiveInvolutionProduct.pComponent_quasisimple_product ℓ
        (sesqUnitary_pComponent_quasisimple h hp (Submodule.one_le_finrank_iff.mpr hP)
          (hsymm _) hlP ℓ hℓ)
        (sesqUnitary_pComponent_quasisimple h hp (Submodule.one_le_finrank_iff.mpr hM)
          (hsymm _) hlM ℓ hℓ)) J hJ
  · obtain ⟨-, -, -, -, -, -, e, -⟩ := hpaired hN
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ e
      (generalLinear_pComponent_quasisimple (Submodule.one_le_finrank_iff.mpr hP) ℓ) J hJ

section Image

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

@[expose] def centralizerImageHom (A : sesqUnitaryGroup B) :
    Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B)) →*
      Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :=
  ((QuotientGroup.mk' (sesqNormOneScalars h B)).comp
    (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))).subtype).codRestrict _ fun g =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        change (QuotientGroup.mk' (sesqNormOneScalars h B)) (g : sesqUnitaryGroup B) *
            (QuotientGroup.mk' (sesqNormOneScalars h B)) A =
          (QuotientGroup.mk' (sesqNormOneScalars h B)) A *
            (QuotientGroup.mk' (sesqNormOneScalars h B)) (g : sesqUnitaryGroup B)
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp g.2])

theorem coe_centralizerImageHom (A : sesqUnitaryGroup B)
    (g : Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))) :
    (centralizerImageHom A g : sesqProjUnitary h B) =
      QuotientGroup.mk (g : sesqUnitaryGroup B) :=
  rfl

theorem range_centralizerImageHom (A : sesqUnitaryGroup B) :
    (centralizerImageHom (h := h) A).range =
      ((Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))).map
        (QuotientGroup.mk' (sesqNormOneScalars h B))).subgroupOf
          (Subgroup.centralizer {(QuotientGroup.mk' (sesqNormOneScalars h B)) A}) := by
  ext x
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨g, hg, hgx⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩

theorem ker_centralizerImageHom_le_center (A : sesqUnitaryGroup B) :
    (centralizerImageHom (h := h) A).ker ≤
      Subgroup.center (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))) := by
  intro g hg
  have hz : (g : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B := by
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    exact (QuotientGroup.eq_one_iff _).mp h1
  refine Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_
  exact (mem_sesqNormOneScalars_commute hz x).symm

end Image

theorem projective_unitary_involution_centralizer_p_components (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) (a : sesqProjUnitary h B) (ha : orderOf a = 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (L : Subgroup (Subgroup.centralizer ({a} : Set (sesqProjUnitary h B))))
    (hL : CFSG.IsPComponent ℓ L) : CFSG.IsQuasisimple L := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite E := h.finite
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars h B) a
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnormal, hindex, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl ha
  rw [← range_centralizerImageHom] at hnormal hindex
  have := hnormal
  have := CatalogueRelativeB.quotient_solvable_of_index_le_two _ hindex
  exact CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient ℓ
    (centralizerImageHom A).range
    (CatalogueBProjectiveInvolution.pComponent_quasisimple_of_central_surjection ℓ
      (centralizerImageHom A).rangeRestrict (centralizerImageHom A).rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict]; exact ker_centralizerImageHom_le_center A)
      (centralizer_lift_pComponent_quasisimple h hp hn hB hBl ha ℓ hℓ)) L hL

end CFSG.ComponentClassification.CatalogueBUnitaryB
