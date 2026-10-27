module

public import CFSG.LieType.AlgebraicGroups.BorelIdentityComponent
public import CFSG.LieType.AlgebraicGroups.ConeFixedPoint
public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed
public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic

public noncomputable section

open WithConv TauCeti.Comodule

namespace CFSG.LieType.AlgebraicGroups.TorusConjugacy

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)

theorem exists_conjugate_le_of_closedOrbitLine {W : Type u} [AddCommGroup W] [Module k W]
    [TauCeti.Comodule k H W] [FiniteDimensional k W] {w₁ : W} (hw₁ : w₁ ≠ 0)
    (hX : ClosedCone.IsZariskiClosed k (ClosedCone.orbitCone k H w₁))
    (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ basePointsRepresentation (H := H) W g w₁ ∈ k ∙ w₁)
    (I : TauCeti.HopfIdeal k H) (hI : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H I) :
    ∃ g, (closureIdentityComponent H P).conjugate g ≤ I := by
  have hcI := (TauCeti.HopfIdeal.isBorelCandidate_iff k H I).mp
    ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H I).mp hI).2.1
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  let : Algebra.Smooth k Q := (TauCeti.smoothCommHopfAlgProperty_iff _).mp hcI.1
  let : IsReduced Q := TauCeti.isReduced_of_smooth k Q
  let : ConnectedSpace (PrimeSpectrum Q) :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mp hcI.2.1
  let : IsDomain Q := CFSG.isDomain_of_smooth_of_connected (k := k) Q
  let : Group.IsSolvable (WithConv (Q →ₐ[k] AlgebraicClosure k)) :=
    (TauCeti.geometricallySolvablePointsCommHopfAlgProperty_iff k Q.obj).mp hcI.2.2
  let : Group.IsSolvable (WithConv (Q →ₐ[k] k)) :=
    Group.isSolvable_of_isSolvable_injective
      (TauCeti.AlgHom.mapValue_injective (Algebra.ofId k (AlgebraicClosure k)).injective)
  let q : H →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I)
  let : TauCeti.Comodule k Q W := TauCeti.Comodule.Corestrict q.toCoalgHom
  have hρ : ∀ p : WithConv (Q →ₐ[k] k), basePointsRepresentation (H := Q) W p =
      basePointsRepresentation (H := H) W (TauCeti.AlgHom.mapDomain q p) := fun p =>
    TauCeti.Comodule.basePointsRepresentation_corestrict q p
  have hcone : ClosedCone.IsCone k (ClosedCone.orbitCone k H w₁) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  have hG : ∀ p : WithConv (Q →ₐ[k] k), ∀ v ∈ ClosedCone.orbitCone k H w₁,
      basePointsRepresentation (H := Q) W p v ∈ ClosedCone.orbitCone k H w₁ := by
    rintro p _ ⟨g, c, rfl⟩
    rw [hρ, map_smul, ← Module.End.mul_apply, ← map_mul]
    exact ⟨_, c, rfl⟩
  have hw₁C : w₁ ∈ ClosedCone.orbitCone k H w₁ := ⟨1, 1, by rw [map_one, one_smul]; rfl⟩
  obtain ⟨_, ⟨g, c, rfl⟩, hv0, χ, -, hχ⟩ :=
    ClosedCone.exists_ne_zero_mem_forall_eq_smul (H := Q) (M := W) hX hcone hG ⟨w₁, hw₁C, hw₁⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (zero_smul k _)
  have hself : ∀ x : WithConv (H →ₐ[k] k),
      TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId k k) x = x := by
    intro x
    apply WithConv.ext
    ext a
    simp
  have hqp : ∀ p : WithConv (Q →ₐ[k] k),
      (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k)).hom p =
        TauCeti.AlgHom.mapDomain q p := by
    intro p
    apply WithConv.ext
    ext a
    rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply,
      TauCeti.AlgHom.mapDomain_apply_apply]
    exact congrArg p.ofConv (TauCeti.CommHopfAlgCat.mkQuotient_apply H.obj I a).symm
  have hstab : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      g⁻¹ * x * g ∈ P := by
    rintro _ ⟨p, rfl⟩
    have h1 := hχ p
    rw [hρ, ← hqp, map_smul, smul_comm (p.ofConv χ) c] at h1
    have h2 : basePointsRepresentation (H := H) W
        ((TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k)).hom p)
          (basePointsRepresentation (H := H) W g w₁) =
        p.ofConv χ • basePointsRepresentation (H := H) W g w₁ := smul_right_injective W hc0 h1
    refine (hP _).mpr (Submodule.mem_span_singleton.mpr ⟨p.ofConv χ, ?_⟩)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h2, map_smul,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hle : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (I.conjugate g⁻¹)
      (CommAlgCat.of k k) ≤ P := by
    intro x' hx'
    have he : g⁻¹ * (g * x' * g⁻¹) * g⁻¹⁻¹ = x' := by group
    have h1 := (TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff I g⁻¹
      (CommAlgCat.of k k) (g * x' * g⁻¹)).mp (by
        rw [hself, he]
        exact hx')
    have h2 := hstab _ h1
    rwa [show g⁻¹ * (g * x' * g⁻¹) * g = x' by group] at h2
  have hI' : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H (I.conjugate g⁻¹) :=
    TauCeti.HopfIdeal.IsBorelOverAlgClosed.conjugate hI g⁻¹
  have hcI' := (TauCeti.HopfIdeal.isBorelCandidate_iff k H _).mp
    ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H _).mp hI').2.1
  let Q' := TauCeti.FiniteTypeCommHopfAlgCat.quotient H (I.conjugate g⁻¹)
  let : Algebra.Smooth k Q' := (TauCeti.smoothCommHopfAlgProperty_iff _).mp hcI'.1
  let : IsReduced Q' := TauCeti.isReduced_of_smooth k Q'
  let : ConnectedSpace (PrimeSpectrum Q') :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mp hcI'.2.1
  refine ⟨g, ?_⟩
  have h5 := closureIdentityComponent_le H hle
  have h6 := TauCeti.HopfIdeal.conjugate_mono g h5
  rwa [TauCeti.HopfIdeal.conjugate_conjugate_inv] at h6

theorem exists_conjugate_eq_of_closedOrbitLine (B₀ : TauCeti.HopfIdeal k H)
    (hB₀ : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B₀) {W : Type u} [AddCommGroup W]
    [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W] {w₁ : W} (hw₁ : w₁ ≠ 0)
    (hX : ClosedCone.IsZariskiClosed k (ClosedCone.orbitCone k H w₁))
    (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ basePointsRepresentation (H := H) W g w₁ ∈ k ∙ w₁)
    (hBP : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B₀ (CommAlgCat.of k k) ≤ P)
    (hsol : Group.IsSolvable P) {I J : TauCeti.HopfIdeal k H}
    (hI : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H I)
    (hJ : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H J) :
    ∃ g, I.conjugate g = J := by
  obtain ⟨L, hL⟩ := exists_ideal_forall_iff_mem_span_self H hw₁
  have hC := closureIdentityComponent_eq_of_isBorelOverAlgClosed H B₀ hB₀ P hBP hsol
    (quotientPointsSubgroup_vanishingIdeal_le_of_forall_iff H P L fun g => (hP g).trans (hL g).symm)
  have hcand₀ := ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H B₀).mp hB₀).2.1
  refine TauCeti.HopfIdeal.exists_conjugate_eq_of_isBorelOverAlgClosed B₀ hcand₀
    (fun I' hI' => ?_) hI hJ
  obtain ⟨g, hg⟩ := exists_conjugate_le_of_closedOrbitLine H hw₁ hX P hP I' hI'
  exact ⟨g, hC ▸ hg⟩

theorem isBorelOverAlgClosed_closureIdentityComponent_of_closedOrbitLine {W : Type u}
    [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W] {w₁ : W}
    (hw₁ : w₁ ≠ 0) (hX : ClosedCone.IsZariskiClosed k (ClosedCone.orbitCone k H w₁))
    (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ basePointsRepresentation (H := H) W g w₁ ∈ k ∙ w₁)
    (hsol : Group.IsSolvable P) :
    TauCeti.HopfIdeal.IsBorelOverAlgClosed k H (closureIdentityComponent H P) := by
  obtain ⟨L, hL⟩ := exists_ideal_forall_iff_mem_span_self H hw₁
  have hC := isBorelCandidate_closureIdentityComponent H P hsol
    (quotientPointsSubgroup_vanishingIdeal_le_of_forall_iff H P L fun g => (hP g).trans (hL g).symm)
  obtain ⟨B₁, hmin⟩ := TauCeti.HopfIdeal.exists_minimal_isBorelCandidate H
  have hB₁ : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B₁ :=
    (TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H B₁).mpr ⟨inferInstance, hmin⟩
  obtain ⟨g, hg⟩ := exists_conjugate_le_of_closedOrbitLine H hw₁ hX P hP B₁ hB₁
  have h1 : closureIdentityComponent H P ≤ B₁.conjugate g⁻¹ := by
    have h := TauCeti.HopfIdeal.conjugate_mono g⁻¹ hg
    rwa [TauCeti.HopfIdeal.conjugate_inv_conjugate] at h
  have hB₁' : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H (B₁.conjugate g⁻¹) :=
    TauCeti.HopfIdeal.IsBorelOverAlgClosed.conjugate hB₁ g⁻¹
  have h2 : B₁.conjugate g⁻¹ ≤ closureIdentityComponent H P :=
    ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H _).mp hB₁').2.2 hC h1
  rw [le_antisymm h1 h2]
  exact hB₁'

theorem exists_closedOrbitLine_of_isBorelOverAlgClosed_of_isSolvable {W : Type u}
    [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W] {w₁ : W}
    (hw₁ : w₁ ≠ 0) (hX : ClosedCone.IsZariskiClosed k (ClosedCone.orbitCone k H w₁))
    (P : Subgroup (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ basePointsRepresentation (H := H) W g w₁ ∈ k ∙ w₁)
    (hsol : Group.IsSolvable P) (B : TauCeti.HopfIdeal k H)
    (hB : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B) :
    ∃ w : W, w ≠ 0 ∧ ClosedCone.IsZariskiClosed k (ClosedCone.orbitCone k H w) ∧
      ∃ P' : Subgroup (WithConv (H →ₐ[k] k)),
        (∀ g, g ∈ P' ↔ basePointsRepresentation (H := H) W g w ∈ k ∙ w) ∧
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) ≤ P' ∧
        Group.IsSolvable P' := by
  obtain ⟨L, hL⟩ := exists_ideal_forall_iff_mem_span_self H hw₁
  have hclosed := quotientPointsSubgroup_vanishingIdeal_le_of_forall_iff H P L
    fun g => (hP g).trans (hL g).symm
  have hCB := isBorelOverAlgClosed_closureIdentityComponent_of_closedOrbitLine H hw₁ hX P hP hsol
  have hCP : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (closureIdentityComponent H P)
      (CommAlgCat.of k k) ≤ P :=
    (quotientPointsSubgroup_closureIdentityComponent_le H P).trans hclosed
  obtain ⟨h, hh⟩ := exists_conjugate_eq_of_closedOrbitLine H _ hCB hw₁ hX P hP hCP hsol hCB hB
  have hself : ∀ x : WithConv (H →ₐ[k] k),
      TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId k k) x = x := by
    intro x
    apply WithConv.ext
    ext a
    simp
  have hne : basePointsRepresentation (H := H) W h w₁ ≠ 0 := by
    intro h0
    apply hw₁
    have := congrArg (basePointsRepresentation (H := H) W h⁻¹) h0
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  have hmemw : basePointsRepresentation (H := H) W h w₁ ∈ ClosedCone.orbitCone k H w₁ :=
    ⟨h, 1, by rw [one_smul]⟩
  refine ⟨basePointsRepresentation (H := H) W h w₁, hne, ?_,
    P.map (MulAut.conj h).toMonoidHom, fun g => ?_, ?_,
    Group.isSolvable_of_surjective ((MulAut.conj h).toMonoidHom.subgroupMap_surjective P)⟩
  · rwa [ClosedCone.orbitCone_eq_of_mem hmemw hne]
  · rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hP, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply]
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hg
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      have := congrArg (basePointsRepresentation (H := H) W h) hc
      rwa [map_smul, ← Module.End.mul_apply (basePointsRepresentation (H := H) W h),
        ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    · intro hg
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hg
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      rw [← hc, map_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
  · intro x hx
    rw [← hh] at hx
    have h1 := (TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff
      (closureIdentityComponent H P) h (CommAlgCat.of k k) (h⁻¹ * x * h)).mp (by
        rw [hself, show h * (h⁻¹ * x * h) * h⁻¹ = x by group]
        exact hx)
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    exact hCP h1

end CFSG.LieType.AlgebraicGroups.TorusConjugacy

namespace CFSG.LieType.AlgebraicGroups

open CategoryTheory

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_borel_innerTwist_stable_of_closedOrbitLine
    (S : TauCeti.SemisimpleCommHopfAlgCat.{u} k) (σ : S.obj →ₐc[k] S.obj)
    (hσ : Function.Bijective σ)
    (hflag : ∀ B : TauCeti.HopfIdeal k S.obj, TauCeti.HopfIdeal.IsBorelOverAlgClosed k S.obj B →
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : TauCeti.Comodule k S.obj W)
        (_ : Module.Finite k W) (w : W), w ≠ 0 ∧
        ClosedCone.IsZariskiClosed k (ClosedCone.orbitCone k S.obj w) ∧
        ∃ P : Subgroup (WithConv (S.obj →ₐ[k] k)),
          (∀ g, g ∈ P ↔ TauCeti.Comodule.basePointsRepresentation (H := S.obj) W g w ∈ k ∙ w) ∧
          TauCeti.CommHopfAlgCat.quotientPointsSubgroup S.obj.obj B (CommAlgCat.of k k) ≤ P ∧
          Group.IsSolvable P) :
    ∃ (B : TauCeti.HopfIdeal k S.obj),
      TauCeti.HopfIdeal.IsBorelOverAlgClosed k S.obj B ∧
      ∃ y : WithConv (S.obj →ₐ[k] k), ∀ a : S.obj,
        (σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom) a ∈ B ↔ a ∈ B := by
  obtain ⟨B₀, hmin⟩ := TauCeti.HopfIdeal.exists_minimal_isBorelCandidate S.obj
  have hB₀ : TauCeti.HopfIdeal.IsBorelOverAlgClosed k S.obj B₀ :=
    (TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k S.obj B₀).mpr ⟨inferInstance, hmin⟩
  let e : S.obj ≅ S.obj := ObjectProperty.isoMk (TauCeti.finiteTypeCommHopfAlgProperty k)
    (_root_.CommHopfAlgCat.isoMk (BialgEquiv.ofBijective σ hσ))
  have he : TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom = σ := by
    change (_root_.CommHopfAlgCat.isoMk (BialgEquiv.ofBijective σ hσ)).hom.hom = σ
    rw [_root_.CommHopfAlgCat.isoMk_hom, _root_.CommHopfAlgCat.hom_ofHom]
    rfl
  let J := B₀.comapOfSurjective σ hσ.2
  have hJ : TauCeti.HopfIdeal.IsBorelOverAlgClosed k S.obj J := by
    have h := hB₀.comapOfIso e
    simpa only [he] using h
  obtain ⟨W, _, _, _, _, w, hw, hX, P, hP, hBP, hsol⟩ := hflag B₀ hB₀
  obtain ⟨y, hy⟩ := TorusConjugacy.exists_conjugate_eq_of_closedOrbitLine S.obj B₀ hB₀ hw hX P hP
    hBP hsol hJ hB₀
  refine ⟨B₀, hB₀, y, fun a => ?_⟩
  have h1 : a ∈ J.conjugate y ↔ a ∈ B₀ := by rw [hy]
  have h2 : (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom a =
      TauCeti.HopfAlgebra.pointConjugationAlgHom y a := by
    rw [← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
    rfl
  rw [← h1, TauCeti.HopfIdeal.mem_conjugate, TauCeti.HopfIdeal.mem_comapOfSurjective,
    BialgHom.comp_apply, h2]

end CFSG.LieType.AlgebraicGroups
