module

public import CFSG.LieType.AlgebraicGroups.ConeFixedPoint
public import CFSG.LieType.AlgebraicGroups.RegularCocharacter
public import CFSG.Mathlib.RingTheory.ConnectedRegular
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

public noncomputable section

open WithConv TauCeti.Comodule CFSG.LieType.AlgebraicGroups.ClosedCone
open CFSG.LieType.AlgebraicGroups.RegularCocharacter

namespace CFSG.LieType.AlgebraicGroups.TorusConjugacy

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem map_pointConjugationAlgHom {A B : Type u} [CommRing A] [HopfAlgebra k A]
    [CommRing B] [HopfAlgebra k B] (f : A →ₐc[k] B) (g : WithConv (B →ₐ[k] k)) (y : A) :
    f (TauCeti.HopfAlgebra.pointConjugationAlgHom
        (TauCeti.AlgHom.mapDomain (A := k) f g) y) =
      TauCeti.HopfAlgebra.pointConjugationAlgHom g (f y) := by
  have hχ : TauCeti.AlgHom.mapDomain (A := B) f
      (TauCeti.AlgHom.mapValue (H := B) (Algebra.ofId k B) g) =
      TauCeti.AlgHom.mapValue (H := A) (Algebra.ofId k B)
        (TauCeti.AlgHom.mapDomain (A := k) f g) := by
    have hm := DFunLike.congr_fun
      (TauCeti.AlgHom.mapValue_mapDomain (φ := f) (χ := Algebra.ofId k B)) g
    simp only [MonoidHom.comp_apply] at hm
    rw [← hm]
  have hid : TauCeti.AlgHom.mapDomain (A := B) f (WithConv.toConv (AlgHom.id k B)) =
      WithConv.toConv (f : A →ₐ[k] B) := by
    rw [TauCeti.AlgHom.mapDomain_apply]
    simp
  have hmain : WithConv.toConv
      ((TauCeti.HopfAlgebra.pointConjugationAlgHom g).comp (f : A →ₐ[k] B)) =
      WithConv.toConv ((f : A →ₐ[k] B).comp (TauCeti.HopfAlgebra.pointConjugationAlgHom
        (TauCeti.AlgHom.mapDomain (A := k) f g))) := by
    have hleft : WithConv.toConv
        ((TauCeti.HopfAlgebra.pointConjugationAlgHom g).comp (f : A →ₐ[k] B)) =
        TauCeti.AlgHom.mapValue (H := A) (Algebra.ofId k B)
            (TauCeti.AlgHom.mapDomain (A := k) f g) *
          WithConv.toConv (f : A →ₐ[k] B) *
          (TauCeti.AlgHom.mapValue (H := A) (Algebra.ofId k B)
            (TauCeti.AlgHom.mapDomain (A := k) f g))⁻¹ := by
      rw [show WithConv.toConv
          ((TauCeti.HopfAlgebra.pointConjugationAlgHom g).comp (f : A →ₐ[k] B)) =
          TauCeti.AlgHom.mapDomain (A := B) f
            (WithConv.toConv (TauCeti.HopfAlgebra.pointConjugationAlgHom g)) from rfl]
      rw [TauCeti.HopfAlgebra.toConv_pointConjugationAlgHom g, map_mul, map_mul, map_inv,
        hχ, hid]
    have hright : WithConv.toConv
        ((f : A →ₐ[k] B).comp (TauCeti.HopfAlgebra.pointConjugationAlgHom
          (TauCeti.AlgHom.mapDomain (A := k) f g))) =
        TauCeti.AlgHom.mapValue (H := A) (Algebra.ofId k B)
            (TauCeti.AlgHom.mapDomain (A := k) f g) *
          WithConv.toConv (f : A →ₐ[k] B) *
          (TauCeti.AlgHom.mapValue (H := A) (Algebra.ofId k B)
            (TauCeti.AlgHom.mapDomain (A := k) f g))⁻¹ := by
      simpa only [WithConv.ofConv_toConv] using
        (TauCeti.HopfAlgebra.comp_pointConjugationAlgHom
          (TauCeti.AlgHom.mapDomain (A := k) f g) (WithConv.toConv (f : A →ₐ[k] B)))
    rw [hleft, hright]
  exact (congrArg (fun φ : A →ₐ[k] B => φ y)
    (WithConv.toConv_injective hmain)).symm

section Torus

variable (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)

omit [IsAlgClosed k] in
theorem isDomain_quotient_of_isMaximalTorus {I : TauCeti.HopfIdeal k H}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I) :
    IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) := by
  have hT : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) :=
    (TauCeti.HopfIdeal.isMaximalTorus_iff k H.obj I).mp hI |>.1
  have hsmooth : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp (hT.smooth k _)
  have hconn : ConnectedSpace
      (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)) :=
    (hT.geometricallyConnected k _).connectedSpace k _
  exact CFSG.isDomain_of_smooth_of_connected (k := k) _

theorem commute_of_mem_quotientPointsSubgroup_of_isMaximalTorus {I : TauCeti.HopfIdeal k H}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I) {s₁ s₂ : WithConv (H →ₐ[k] k)}
    (h₁ : s₁ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k))
    (h₂ : s₂ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    Commute s₁ s₂ := by
  obtain ⟨n, π, hπ, hker⟩ :=
    exists_splitCoordinates H I ((TauCeti.HopfIdeal.isMaximalTorus_iff k H.obj I).mp hI).1
  exact commute_of_mem_range_mapDomain π
    ((mem_quotientPointsSubgroup_iff_exists_mapDomain H I π hπ hker _).mp h₁)
    ((mem_quotientPointsSubgroup_iff_exists_mapDomain H I π hπ hker _).mp h₂)

theorem isSolvable_points_quotient_of_isMaximalTorus {I : TauCeti.HopfIdeal k H}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I) :
    Group.IsSolvable (WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k)) := by
  refine Group.isSolvable_of_comm fun g h => ?_
  apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj I (CommAlgCat.of k k)
  rw [map_mul, map_mul]
  exact (commute_of_mem_quotientPointsSubgroup_of_isMaximalTorus H hI ⟨g, rfl⟩ ⟨h, rfl⟩).eq

theorem exists_ne_zero_mem_forall_mem_span_of_isMaximalTorus {I : TauCeti.HopfIdeal k H}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I)
    {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W]
    {C : Set W} (hC : IsZariskiClosed k C) (hcone : IsCone k C)
    (hT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      ∀ v ∈ C, basePointsRepresentation (H := H) W s v ∈ C)
    (hne : ∃ v ∈ C, v ≠ 0) :
    ∃ x ∈ C, x ≠ 0 ∧ ∀ t ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I
      (CommAlgCat.of k k), basePointsRepresentation (H := H) W t x ∈ k ∙ x := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  let π : H →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I)
  let : TauCeti.Comodule k Q W := TauCeti.Comodule.Corestrict π.toCoalgHom
  have hdom : IsDomain Q := isDomain_quotient_of_isMaximalTorus H hI
  have hsol : Group.IsSolvable (WithConv (Q →ₐ[k] k)) :=
    isSolvable_points_quotient_of_isMaximalTorus H hI
  have hfin : Algebra.FiniteType k Q := inferInstance
  have hG' : ∀ g : WithConv (Q →ₐ[k] k), ∀ v ∈ C,
      basePointsRepresentation (H := Q) W g v ∈ C := by
    intro g v hv
    rw [TauCeti.Comodule.basePointsRepresentation_corestrict (φ := π) (g := g)]
    exact hT _ ⟨g, rfl⟩ v hv
  obtain ⟨x, hxC, hx0, χ, hχ, hxχ⟩ :=
    CFSG.LieType.AlgebraicGroups.ClosedCone.exists_ne_zero_mem_forall_eq_smul
      (k := k) (H := Q) (M := W) hC hcone hG' hne
  refine ⟨x, hxC, hx0, ?_⟩
  intro t ht
  have hkill : ∀ h : H.obj, h ∈ I → t.ofConv h = 0 :=
    (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj I
      (CommAlgCat.of k k) t).mp ht
  let g : WithConv (Q →ₐ[k] k) :=
    TauCeti.CommHopfAlgCat.liftQuotientPoint H.obj I (CommAlgCat.of k k) t hkill
  have h1 : TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) g = t :=
    TauCeti.CommHopfAlgCat.quotientPointsHom_liftQuotientPoint H.obj I
      (CommAlgCat.of k k) t hkill
  have h2 : TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) g =
      TauCeti.AlgHom.mapDomain (A := k) π g := by
    rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
    rfl
  rw [← h1, h2, ← TauCeti.Comodule.basePointsRepresentation_corestrict (φ := π) (g := g),
    hxχ g]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

noncomputable def quotientIsoOfSurjective {H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (f : H →ₐc[k] K) (hf : Function.Surjective f) (J : TauCeti.HopfIdeal k K) :
    TauCeti.FiniteTypeCommHopfAlgCat.quotient H (J.comapOfSurjective f hf) ≅
      TauCeti.FiniteTypeCommHopfAlgCat.quotient K J :=
  CategoryTheory.ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k)
    (TauCeti.CommHopfAlgCat.quotientIsoOfSurjective
      (_root_.CommHopfAlgCat.ofHom f) hf J)

omit [IsAlgClosed k] in
theorem isMaximalTorus_map {J I : TauCeti.HopfIdeal k H} (hJI : J ≤ I)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I) :
    TauCeti.HopfIdeal.IsMaximalTorus k (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J).obj
      (I.map (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H J))) := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H J
  let π : H →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H J)
  have hπ : Function.Surjective π :=
    TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj J
  have hker : TauCeti.HopfIdeal.kerOfSurjective π hπ = J :=
    TauCeti.HopfIdeal.kerOfSurjective_mkBialgHom (R := k) (H := H.obj) J
  have hcomap : (I.map π).comapOfSurjective π hπ = I := by
    rw [TauCeti.HopfIdeal.comapOfSurjective_map I π hπ, hker, sup_eq_left.mpr hJI]
  rw [TauCeti.HopfIdeal.isMaximalTorus_iff]
  constructor
  · have hT : TauCeti.torusCommHopfAlgProperty k
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) :=
      (TauCeti.HopfIdeal.isMaximalTorus_iff k H.obj I).mp hI |>.1
    have hT' : TauCeti.torusCommHopfAlgProperty k
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient H
          ((I.map π).comapOfSurjective π hπ)) := by
      rw [← hcomap] at hT
      exact hT
    exact (TauCeti.torusCommHopfAlgProperty k).prop_of_iso
      (quotientIsoOfSurjective π hπ (I.map π)) hT'
  · intro J' hJ' hle
    let J'' : TauCeti.HopfIdeal k H := J'.comapOfSurjective π hπ
    have hJ''torus : TauCeti.torusCommHopfAlgProperty k
        (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J'') :=
      (TauCeti.torusCommHopfAlgProperty k).prop_of_iso
        (quotientIsoOfSurjective π hπ J').symm hJ'
    have hJ''I : J'' ≤ I := by
      have h := TauCeti.HopfIdeal.comapOfSurjective_mono π hπ hle
      rwa [hcomap] at h
    have hI' : I ≤ J'' :=
      (TauCeti.HopfIdeal.isMaximalTorus_iff k H.obj I).mp hI |>.2 J'' hJ''torus hJ''I
    exact (TauCeti.HopfIdeal.map_le_iff_le_comapOfSurjective hπ).mpr hI'

omit [IsAlgClosed k] in
theorem conjugate_eq_of_map_conjugate_eq {J I₁ I₂ : TauCeti.HopfIdeal k H} (h₁ : J ≤ I₁)
    (h₂ : J ≤ I₂) (h' : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J →ₐ[k] k))
    (h : (I₁.map (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H J))).conjugate h' =
      I₂.map (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H J))) :
    I₁.conjugate (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) h') =
      I₂ := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H J
  let π : H →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H J)
  have hπ : Function.Surjective π :=
    TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj J
  have hker : TauCeti.HopfIdeal.kerOfSurjective π hπ = J :=
    TauCeti.HopfIdeal.kerOfSurjective_mkBialgHom (R := k) (H := H.obj) J
  let gH : WithConv (H →ₐ[k] k) :=
    TauCeti.CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) h'
  have hgH : TauCeti.AlgHom.mapDomain (A := k) π h' = gH := by
    change TauCeti.AlgHom.mapDomain (A := k) π h' =
      TauCeti.CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) h'
    rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
    rfl
  have hnat : ∀ y : H, π (TauCeti.HopfAlgebra.pointConjugationAlgHom gH y) =
      TauCeti.HopfAlgebra.pointConjugationAlgHom h' (π y) := by
    intro y
    simpa only [hgH] using map_pointConjugationAlgHom π h' y
  have hconj : ((I₁.map π).conjugate h').comapOfSurjective π hπ =
      I₁.conjugate gH := by
    ext x
    rw [TauCeti.HopfIdeal.mem_comapOfSurjective, TauCeti.HopfIdeal.mem_conjugate,
      TauCeti.HopfIdeal.mem_conjugate, ← hnat x,
      TauCeti.HopfIdeal.mem_map_iff_of_surjective hπ]
    constructor
    · rintro ⟨y, hy, hπy⟩
      have hsub : TauCeti.HopfAlgebra.pointConjugationAlgHom gH x - y ∈ J := by
        have hzero : π (TauCeti.HopfAlgebra.pointConjugationAlgHom gH x - y) = 0 := by
          rw [map_sub, hπy, sub_self]
        rw [← hker]
        exact (TauCeti.HopfIdeal.mem_kerOfSurjective π hπ).mpr hzero
      have hmem : TauCeti.HopfAlgebra.pointConjugationAlgHom gH x =
          y + (TauCeti.HopfAlgebra.pointConjugationAlgHom gH x - y) := by ring
      rw [hmem]
      exact I₁.toIdeal.add_mem hy (h₁ hsub)
    · rintro hx
      exact ⟨TauCeti.HopfAlgebra.pointConjugationAlgHom gH x, hx, rfl⟩
  have hcomap₂ : (I₂.map π).comapOfSurjective π hπ = I₂ := by
    rw [TauCeti.HopfIdeal.comapOfSurjective_map I₂ π hπ, hker, sup_eq_left.mpr h₂]
  have hc := congrArg
    (fun K : TauCeti.HopfIdeal k Q.obj => K.comapOfSurjective π hπ) h
  rwa [hconj, hcomap₂] at hc

end Torus

end CFSG.LieType.AlgebraicGroups.TorusConjugacy
