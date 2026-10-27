module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupGL
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.NoetherianSpace

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.SeminaireExp3

open Topology WithConv
open scoped CFSG.ConvolutionPoints

section Points

theorem isPreirreducible_image_iff_of_isInducing {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsInducing f) {S : Set X} :
    IsPreirreducible (f '' S) ↔ IsPreirreducible S := by
  refine ⟨fun h u v hu hv hSu hSv => ?_, fun h => h.image f hf.continuous.continuousOn⟩
  obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.1 hu
  obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.1 hv
  obtain ⟨x, hxS, hxu⟩ := hSu
  obtain ⟨y, hyS, hyv⟩ := hSv
  obtain ⟨_, ⟨z, hz, rfl⟩, hzuv⟩ :=
    h u' v' hu' hv' ⟨f x, ⟨x, hxS, rfl⟩, hxu⟩ ⟨f y, ⟨y, hyS, rfl⟩, hyv⟩
  exact ⟨z, hz, hzuv⟩

theorem isIrreducible_image_iff_of_isInducing {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsInducing f) {S : Set X} :
    IsIrreducible (f '' S) ↔ IsIrreducible S :=
  and_congr Set.image_nonempty (isPreirreducible_image_iff_of_isInducing hf)

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A]

theorem range_comp_mkₐ (J : Ideal A) :
    (Set.range fun z : (A ⧸ J) →ₐ[k] k => z.comp (Ideal.Quotient.mkₐ k J)) = pointsZero k J := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · intro hy
    exact ⟨Ideal.Quotient.liftₐ J y hy, AlgHom.ext fun a => rfl⟩

variable (k) in
@[expose] def IsDomainImage (S : Set (A →ₐ[k] k)) : Prop :=
  ∃ (D : Type) (_ : CommRing D) (_ : Algebra k D) (_ : Algebra.FiniteType k D) (_ : IsDomain D)
    (ψ : A →ₐ[k] D), S = Set.range fun z : D →ₐ[k] k => z.comp ψ

section Induced

variable {X : Type} [TopologicalSpace X] {e : X ≃ (A →ₐ[k] k)}

theorem closure_eq_preimage_pointsZero (he : IsInducing fun x => pointSpec (e x)) (S : Set X) :
    closure S = e ⁻¹' pointsZero k (pointsIdeal (e '' S)) := by
  rw [he.closure_eq_preimage_closure_image, pointsZero_pointsIdeal, Set.image_image]
  rfl

theorem isClosed_iff_image_eq (he : IsInducing fun x => pointSpec (e x)) {S : Set X} :
    IsClosed S ↔ e '' S = pointsZero k (pointsIdeal (e '' S)) := by
  rw [← closure_subset_iff_isClosed, closure_eq_preimage_pointsZero he]
  constructor
  · intro h
    refine (subset_pointsZero_pointsIdeal _).antisymm fun y hy => ?_
    exact ⟨e.symm y, h (by simpa using hy), by simp⟩
  · intro h x hx
    rw [Set.mem_preimage, ← h] at hx
    obtain ⟨x', hx', hxx'⟩ := hx
    rwa [← e.injective hxx']

theorem isClosed_iff_exists (he : IsInducing fun x => pointSpec (e x)) {S : Set X} :
    IsClosed S ↔ ∃ F : Set A, S = {x | ∀ a ∈ F, e x a = 0} := by
  constructor
  · intro hS
    refine ⟨pointsIdeal (e '' S), ?_⟩
    conv_lhs => rw [← hS.closure_eq, closure_eq_preimage_pointsZero he]
    rfl
  · rintro ⟨F, rfl⟩
    have : {x | ∀ a ∈ F, e x a = 0} =
        (fun x => pointSpec (e x)) ⁻¹' PrimeSpectrum.zeroLocus F := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, PrimeSpectrum.mem_zeroLocus,
        pointSpec_asIdeal]
      exact ⟨fun h a ha => h a ha, fun h a ha => h ha⟩
    rw [this]
    exact (PrimeSpectrum.isClosed_zeroLocus F).preimage he.continuous

theorem isIrreducible_iff_isPointIrreducible (he : IsInducing fun x => pointSpec (e x))
    {S : Set X} : IsIrreducible S ↔ IsPointIrreducible k (e '' S) := by
  rw [IsPointIrreducible, Set.image_image, isIrreducible_image_iff_of_isInducing he]

theorem isIrreducible_iff_isPrime (he : IsInducing fun x => pointSpec (e x)) {S : Set X} :
    IsIrreducible S ↔ (pointsIdeal (e '' S)).IsPrime := by
  rw [isIrreducible_iff_isPointIrreducible he, IsPointIrreducible,
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime]
  rfl

theorem isClosed_iff_isPointClosed (he : IsInducing fun x => pointSpec (e x)) {S : Set X} :
    IsClosed S ↔ IsPointClosed k (e '' S) := by
  constructor
  · intro hS
    refine ⟨closure (pointSpec '' (e '' S)), isClosed_closure, ?_⟩
    rw [← pointsZero_pointsIdeal, ← (isClosed_iff_image_eq he).1 hS]
  · rintro ⟨Z, hZ, hSZ⟩
    have : S = (fun x => pointSpec (e x)) ⁻¹' Z := by
      ext x
      rw [Set.mem_preimage, ← Set.mem_preimage (f := pointSpec), ← hSZ, e.injective.mem_set_image]
    rw [this]
    exact hZ.preimage he.continuous

theorem range_comp_mkₐ_pointsIdeal (he : IsInducing fun x => pointSpec (e x)) {S : Set X}
    (hS : IsClosed S) :
    (Set.range fun z : (A ⧸ pointsIdeal (e '' S)) →ₐ[k] k =>
      z.comp (Ideal.Quotient.mkₐ k (pointsIdeal (e '' S)))) = e '' S := by
  rw [range_comp_mkₐ, ← (isClosed_iff_image_eq he).1 hS]

end Induced

variable [IsAlgClosed k]

theorem isUnit_of_forall_algHom_ne_zero {D : Type} [CommRing D] [Algebra k D]
    [Algebra.FiniteType k D] {d : D} (h : ∀ z : D →ₐ[k] k, z d ≠ 0) : IsUnit d := by
  by_contra hd
  obtain ⟨m, hm, hdm⟩ := Ideal.exists_le_maximal (Ideal.span {d})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨z, hz⟩ := exists_algHom_ker_eq k D m
  exact h z (by rw [← RingHom.mem_ker, hz]; exact hdm (Ideal.subset_span rfl))

theorem IsDomainImage.isPointConstructible [Algebra.FiniteType k A] {S : Set (A →ₐ[k] k)}
    (h : IsDomainImage k S) : IsPointConstructible k S := by
  obtain ⟨D, _, _, _, _, ψ, rfl⟩ := h
  have h := isPointConstructible_iUnion_range (k := k) (A := A) (J := Unit) (fun _ => D)
    (fun _ => ψ)
  convert h using 1
  exact (Set.iUnion_const _).symm

theorem IsDomainImage.isPointIrreducible {S : Set (A →ₐ[k] k)} (h : IsDomainImage k S) :
    IsPointIrreducible k S := by
  obtain ⟨D, _, _, _, _, ψ, rfl⟩ := h
  exact isPointIrreducible_range_of_isDomain ψ

end Points

variable (σ : Type) (k : Type) in
@[expose] def ZariskiAffine : Type := σ → k

namespace ZariskiAffine

variable {σ : Type} {k : Type} [Field k]

@[expose] def coords : ZariskiAffine σ k ≃ (σ → k) := Equiv.refl _

@[expose] def pt : ZariskiAffine σ k ≃ (MvPolynomial σ k →ₐ[k] k) where
  toFun x := MvPolynomial.aeval (coords x)
  invFun y := coords.symm fun s => y (MvPolynomial.X s)
  left_inv x := by
    simp only [MvPolynomial.aeval_X]
    rfl
  right_inv y := MvPolynomial.algHom_ext fun s => by
    rw [MvPolynomial.aeval_X]
    rfl

theorem pt_apply (x : ZariskiAffine σ k) (P : MvPolynomial σ k) :
    pt x P = MvPolynomial.eval (coords x) P :=
  rfl

instance : TopologicalSpace (ZariskiAffine σ k) :=
  TopologicalSpace.induced (fun x => pointSpec (pt x)) inferInstance

theorem isInducing_pt : IsInducing fun x : ZariskiAffine σ k => pointSpec (pt x) :=
  ⟨rfl⟩

theorem isClosed_iff {V : Set (ZariskiAffine σ k)} :
    IsClosed V ↔
      ∃ F : Set (MvPolynomial σ k), V = {x | ∀ P ∈ F, MvPolynomial.eval (coords x) P = 0} :=
  isClosed_iff_exists isInducing_pt

end ZariskiAffine

variable (ι : Type) [Fintype ι] [DecidableEq ι] (k : Type) [Field k] in
@[expose] def ZariskiGL : Type := Matrix.GeneralLinearGroup ι k

namespace ZariskiGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : Type} [Field k]

instance : Group (ZariskiGL ι k) := inferInstanceAs (Group (Matrix.GeneralLinearGroup ι k))

@[expose] def toGL : ZariskiGL ι k ≃* Matrix.GeneralLinearGroup ι k := MulEquiv.refl _

@[expose] def point : ZariskiGL ι k ≃* WithConv (GLCoord k ι →ₐ[k] k) :=
  toGL.trans glPointEquiv

@[expose] def pt : ZariskiGL ι k ≃ (GLCoord k ι →ₐ[k] k) :=
  point.toEquiv.trans (WithConv.equiv _)

theorem pt_apply (g : ZariskiGL ι k) : pt g = (point g).ofConv :=
  rfl

theorem toConv_pt (g : ZariskiGL ι k) : toConv (pt g) = point g :=
  rfl

@[simp] theorem pt_glEntry (g : ZariskiGL ι k) (i j : ι) :
    pt g (glEntry k ι i j) = (toGL g : Matrix ι ι k) i j :=
  glPoint_glEntry _ i j

@[simp] theorem pt_glDetInv (g : ZariskiGL ι k) :
    pt g (glDetInv k ι) = ((toGL g : Matrix ι ι k).det)⁻¹ :=
  glPoint_glDetInv _

theorem pt_mul (g h : ZariskiGL ι k) : pt (g * h) = (toConv (pt g) * toConv (pt h)).ofConv := by
  rw [pt_apply, map_mul]
  rfl

theorem pt_inv (g : ZariskiGL ι k) :
    pt g⁻¹ = (pt g).comp (HopfAlgebra.antipodeAlgHom k (GLCoord k ι)) := by
  rw [pt_apply, map_inv]
  rfl

theorem pt_one : pt (1 : ZariskiGL ι k) = (1 : WithConv (GLCoord k ι →ₐ[k] k)).ofConv := by
  rw [pt_apply, map_one]

instance : TopologicalSpace (ZariskiGL ι k) :=
  TopologicalSpace.induced (fun g => pointSpec (pt g)) inferInstance

theorem isInducing_pt : IsInducing fun g : ZariskiGL ι k => pointSpec (pt g) :=
  ⟨rfl⟩

@[expose] def glVec (g : ZariskiGL ι k) : ι × ι ⊕ Unit → k :=
  Sum.elim (fun p => (toGL g : Matrix ι ι k) p.1 p.2) fun _ => ((toGL g : Matrix ι ι k).det)⁻¹

@[expose] def eval (g : ZariskiGL ι k) : MvPolynomial (ι × ι ⊕ Unit) k →ₐ[k] k :=
  MvPolynomial.aeval (glVec g)

@[simp] theorem eval_X_inl (g : ZariskiGL ι k) (i j : ι) :
    eval g (MvPolynomial.X (Sum.inl (i, j))) = (toGL g : Matrix ι ι k) i j := by
  simp [eval, glVec]

@[simp] theorem eval_X_inr (g : ZariskiGL ι k) (u : Unit) :
    eval g (MvPolynomial.X (Sum.inr u)) = ((toGL g : Matrix ι ι k).det)⁻¹ := by
  simp [eval, glVec]

@[expose] def glMk : MvPolynomial (ι × ι ⊕ Unit) k →ₐ[k] GLCoord k ι :=
  Ideal.Quotient.mkₐ k (glIdeal k ι)

theorem glMk_surjective : Function.Surjective (glMk (ι := ι) (k := k)) :=
  fun y => Ideal.Quotient.mk_surjective y

theorem pt_glMk (g : ZariskiGL ι k) (P : MvPolynomial (ι × ι ⊕ Unit) k) :
    pt g (glMk P) = eval g P := by
  have : (pt g).comp glMk = eval g := MvPolynomial.algHom_ext fun v => by
    rcases v with ⟨i, j⟩ | ⟨⟩
    · show pt g (Ideal.Quotient.mk (glIdeal k ι) (glX k ι i j)) = _
      rw [mk_glX, pt_glEntry, eval_X_inl]
    · show pt g (Ideal.Quotient.mk (glIdeal k ι) (glT k ι)) = _
      rw [mk_glT, pt_glDetInv, eval_X_inr]
  exact congrArg (fun f : MvPolynomial (ι × ι ⊕ Unit) k →ₐ[k] k => f P) this

@[expose] def vanishingIdeal (S : Set (ZariskiGL ι k)) : Ideal (MvPolynomial (ι × ι ⊕ Unit) k) :=
  MvPolynomial.vanishingIdeal k (glVec '' S)

theorem mem_vanishingIdeal {S : Set (ZariskiGL ι k)} {P : MvPolynomial (ι × ι ⊕ Unit) k} :
    P ∈ vanishingIdeal S ↔ ∀ g ∈ S, eval g P = 0 := by
  rw [vanishingIdeal, MvPolynomial.mem_vanishingIdeal_iff, Set.forall_mem_image]
  rfl

theorem vanishingIdeal_eq_comap (S : Set (ZariskiGL ι k)) :
    vanishingIdeal S = (pointsIdeal (pt '' S)).comap glMk := by
  ext P
  rw [mem_vanishingIdeal, Ideal.mem_comap, mem_pointsIdeal, Set.forall_mem_image]
  simp only [pt_glMk]

theorem isPrime_vanishingIdeal_iff (S : Set (ZariskiGL ι k)) :
    (vanishingIdeal S).IsPrime ↔ (pointsIdeal (pt '' S)).IsPrime := by
  rw [vanishingIdeal_eq_comap]
  refine ⟨fun h => ?_, fun h => Ideal.comap_isPrime _ _⟩
  rw [← Ideal.map_comap_of_surjective _ glMk_surjective (pointsIdeal (pt '' S))]
  refine Ideal.map_isPrime_of_surjective glMk_surjective ?_
  intro P hP
  rw [Ideal.mem_comap, RingHom.mem_ker.1 hP]
  exact Ideal.zero_mem _

theorem isClosed_iff {S : Set (ZariskiGL ι k)} :
    IsClosed S ↔ ∃ F : Set (MvPolynomial (ι × ι ⊕ Unit) k), S = {g | ∀ P ∈ F, eval g P = 0} := by
  rw [isClosed_iff_exists isInducing_pt]
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨glMk ⁻¹' F, ?_⟩
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro h P hP
      rw [← pt_glMk]
      exact h _ hP
    · intro h a ha
      obtain ⟨P, rfl⟩ := glMk_surjective a
      rw [pt_glMk]
      exact h P ha
  · rintro ⟨F, rfl⟩
    refine ⟨glMk '' F, ?_⟩
    ext g
    simp only [Set.mem_ofPred_eq, Set.forall_mem_image, pt_glMk]

theorem isIrreducible_iff_isPrime {S : Set (ZariskiGL ι k)} :
    IsIrreducible S ↔ (vanishingIdeal S).IsPrime := by
  rw [isPrime_vanishingIdeal_iff, SeminaireExp3.isIrreducible_iff_isPrime isInducing_pt]

instance : TopologicalSpace.NoetherianSpace (ZariskiGL ι k) :=
  have : IsNoetherianRing (GLCoord k ι) := Algebra.FiniteType.isNoetherianRing k _
  isInducing_pt.noetherianSpace

theorem continuous_of_comp_eq {κ : Type} [Fintype κ] [DecidableEq κ]
    {f : ZariskiGL ι k → ZariskiGL κ k} (ψ : GLCoord k κ →ₐ[k] GLCoord k ι)
    (h : ∀ g, pt (f g) = (pt g).comp ψ) : Continuous f := by
  refine continuous_induced_rng.2 ?_
  have : (fun g => pointSpec (pt g)) ∘ f =
      PrimeSpectrum.comap (ψ : GLCoord k κ →+* GLCoord k ι) ∘ fun g => pointSpec (pt g) := by
    funext g
    simp only [Function.comp_apply, comap_pointSpec, h]
  rw [this]
  exact (PrimeSpectrum.continuous_comap _).comp continuous_induced_dom

instance : SeparatelyContinuousMul (ZariskiGL ι k) where
  continuous_const_mul {a} := by
    refine continuous_of_comp_eq
      (constPoint (point a) * toConv (AlgHom.id k (GLCoord k ι))).ofConv fun g => ?_
    have h1 : (pt g).comp (constPoint (point a)).ofConv = pt a :=
      point_comp_constPoint (point g) (point a)
    rw [AlgHom.comp_convMul_distrib, pt_mul, h1, ofConv_toConv, AlgHom.comp_id]
  continuous_mul_const {a} := by
    refine continuous_of_comp_eq (rightTransCo (point a)) fun g => ?_
    rw [pt_apply, map_mul, ← point_comp_rightTransCo (point a) (point g)]
    rfl

instance : ContinuousInv (ZariskiGL ι k) where
  continuous_inv := continuous_of_comp_eq (HopfAlgebra.antipodeAlgHom k (GLCoord k ι)) pt_inv

end ZariskiGL

end CFSG.LieType.AlgebraicGroups.SeminaireExp3
