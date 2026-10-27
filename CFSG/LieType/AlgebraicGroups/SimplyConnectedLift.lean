module

public import CFSG.Mathlib.RingTheory.ConnectedRegular
public import CFSG.LieType.AlgebraicGroups.CentralIsogenyPullback
public import CFSG.LieType.AlgebraicGroups.IsogenyComponents
public import TauCeti.Algebra.AlgebraicGroup.SimplyConnected.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent

public noncomputable section
open CategoryTheory WithConv
namespace CFSG.LieType.AlgebraicGroups
open CentralIsogenyPullback Isogeny
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_lift_of_simplyConnected
    (D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (S : TauCeti.SemisimpleCommHopfAlgCat.{u} k)
    (hS : TauCeti.simplyConnectedSemisimpleCommHopfAlgProperty k S)
    (q : D.obj ⟶ S.obj.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (σ : D →ₐc[k] D) :
    ∃ β : S.obj →ₐc[k] S.obj, q.hom.comp σ = β.comp q.hom := by
  let : Algebra.Smooth k S.obj := S.property.smooth
  let : IsReduced S.obj := TauCeti.isReduced_of_smooth k _
  let : ConnectedSpace (PrimeSpectrum S.obj) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k S.obj.obj
      S.property.geometricallyConnected
  let P := pullbackCoordinate D S.obj q σ
  let R := TauCeti.FiniteTypeCommHopfAlgCat.quotient P (TauCeti.HopfIdeal.reduction k P)
  let X := TauCeti.FiniteTypeCommHopfAlgCat.identityComponent R
  let r := TauCeti.CommHopfAlgCat.mkQuotient P.obj (TauCeti.HopfIdeal.reduction k P)
  let j := TauCeti.CommHopfAlgCat.mkQuotient R.obj
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R))
  let l : S.obj.obj ⟶ X.obj := firstProjection D S.obj q σ ≫ r ≫ j
  let t : S.obj.obj ⟶ X.obj := secondProjection D S.obj q σ ≫ r ≫ j
  have hlP := isCentralIsogeny_firstProjection D S.obj q hq σ
  have hlR := isCentralIsogeny_comp_reduction S.obj P _ hlP
  have hl := isCentralIsogeny_comp_identityComponent S.obj R _ hlR
  have hRsm : Algebra.Smooth k R := smooth_quotient_reduction P
  let := hRsm
  have hXsm : Algebra.Smooth k X := TauCeti.FiniteTypeCommHopfAlgCat.smooth_identityComponent R
  have hXc : TauCeti.geometricallyConnectedCommHopfAlgProperty k X.obj :=
    TauCeti.FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent R
  have hXss : TauCeti.semisimpleCommHopfAlgProperty k X :=
    semisimple_of_finite_of_injective S.obj X S.property l hl.finite hl.injective hXsm hXc
  let Xss : TauCeti.SemisimpleCommHopfAlgCat.{u} k := ⟨X, hXss⟩
  let lss : S ⟶ Xss := ObjectProperty.homMk (ObjectProperty.homMk l)
  let : IsIso lss := hS.isIso lss hl
  let : IsIso l := inferInstanceAs (IsIso lss.hom.hom)
  let β := t ≫ inv l
  refine ⟨β.hom, ?_⟩
  have heq : l.hom.comp (q.hom.comp σ) = t.hom.comp q.hom := by
    have h := projection_equation D S.obj q σ
    have he := congrArg (fun f => (r ≫ j).hom.comp f) h
    change (r ≫ j).hom.comp
        ((firstProjection D S.obj q σ).hom.comp (q.hom.comp σ)) =
      (r ≫ j).hom.comp ((secondProjection D S.obj q σ).hom.comp q.hom)
    exact he
  have hc : (inv l).hom.comp l.hom = BialgHom.id k S.obj := by
    have h := congrArg (fun f => f.hom) (IsIso.hom_inv_id l)
    exact h
  have hh := congrArg (fun f => (inv l).hom.comp f) heq
  change q.hom.comp σ = ((inv l).hom.comp t.hom).comp q.hom
  simpa only [← BialgHom.comp_assoc, hc, BialgHom.id_comp] using hh

omit [IsAlgClosed k] in
theorem comp_pointConjugation_of_fixed
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (F : M →ₐc[k] M)
    (x : TauCeti.HopfAlgebra.points (H := M) (CommAlgCat.of k k))
    (hx : TauCeti.AlgHom.mapDomain F x = x) :
    F.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv x).toBialgHom =
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv x).toBialgHom.comp F := by
  let σ := (TauCeti.HopfAlgebra.pointConjugationBialgEquiv x).toBialgHom
  let y : WithConv (M →ₐ[k] M) := toConv (AlgHom.id k M)
  let c := TauCeti.AlgHom.mapValue (H := M) (Algebra.ofId k M) x
  have hc : TauCeti.AlgHom.mapDomain F c = c := by
    have h := congrArg (fun f => f x)
      (TauCeti.AlgHom.mapValue_mapDomain F (Algebra.ofId k M))
    change TauCeti.AlgHom.mapDomain F c =
      TauCeti.AlgHom.mapValue (Algebra.ofId k M) (TauCeti.AlgHom.mapDomain F x) at h
    rw [hx] at h
    exact h
  have heq : TauCeti.AlgHom.mapDomain (F.comp σ) y =
      TauCeti.AlgHom.mapDomain (σ.comp F) y := by
    rw [TauCeti.AlgHom.mapDomain_comp, TauCeti.AlgHom.mapDomain_comp,
      MonoidHom.comp_apply, MonoidHom.comp_apply]
    change TauCeti.AlgHom.mapDomain σ (TauCeti.AlgHom.mapDomain F y) =
      TauCeti.AlgHom.mapDomain F (TauCeti.AlgHom.mapDomain σ y)
    rw [TauCeti.HopfAlgebra.mapDomain_pointConjugationBialgEquiv,
      TauCeti.HopfAlgebra.mapDomain_pointConjugationBialgEquiv,
      map_mul, map_mul, map_inv, hc]
  apply BialgHom.ext
  intro a
  have h := congrArg (fun z : WithConv (M →ₐ[k] M) => z.ofConv a) heq
  exact h

theorem isIsogeny_of_lift
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsDomain S]
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsIsogeny q)
    (F : D.obj ⟶ D.obj) (hF : TauCeti.CommHopfAlgCat.IsIsogeny F)
    (FS : S.obj ⟶ S.obj) (h : q ≫ FS = F ≫ q) :
    TauCeti.CommHopfAlgCat.IsIsogeny FS := by
  have hfinite : FS.hom.toAlgHom.Finite := by
    apply AlgHom.Finite.of_comp_finite (f := q.hom.toAlgHom)
    have hi := hF.comp hq
    have hh := congrArg (fun f => f.hom.toAlgHom) h
    change FS.hom.toAlgHom.comp q.hom.toAlgHom = q.hom.toAlgHom.comp F.hom.toAlgHom at hh
    rw [hh]
    exact hi.finite
  let : Algebra D S := q.hom.toAlgHom.toAlgebra
  let : Module.Finite D S := hq.finite
  let : Algebra.IsIntegral D S := inferInstance
  let : Nontrivial D := q.hom.toAlgHom.toRingHom.domain_nontrivial
  have hi : Function.Injective FS.hom := by
    change Function.Injective FS.hom.toAlgHom.toRingHom
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_under_eq_bot (R := D)
    change Ideal.comap q.hom.toAlgHom.toRingHom (RingHom.ker FS.hom.toAlgHom.toRingHom) = ⊥
    change RingHom.ker (FS.hom.toAlgHom.toRingHom.comp q.hom.toAlgHom.toRingHom) = ⊥
    have hh := congrArg (fun f => f.hom.toAlgHom.toRingHom) h
    change FS.hom.toAlgHom.toRingHom.comp q.hom.toAlgHom.toRingHom =
      q.hom.toAlgHom.toRingHom.comp F.hom.toAlgHom.toRingHom at hh
    rw [hh, ← RingHom.injective_iff_ker_eq_bot]
    exact hq.injective.comp hF.injective
  exact (TauCeti.CommHopfAlgCat.isIsogeny_iff _).2 ⟨hfinite,
    TauCeti.CommHopfAlgCat.faithfullyFlat_of_finite_of_dominant FS hfinite
      ((RingHom.denseRange_comap_iff_injective _).2 hi)⟩

theorem isIsogeny_of_lift_of_smooth_of_connected
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    [Algebra.Smooth k S] [ConnectedSpace (PrimeSpectrum S)]
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsIsogeny q)
    (F : D →ₐc[k] D) (hF : TauCeti.CommHopfAlgCat.IsIsogeny (_root_.CommHopfAlgCat.ofHom F))
    (FS : S →ₐc[k] S) (heq : FS.comp q.hom = q.hom.comp F) :
    TauCeti.CommHopfAlgCat.IsIsogeny (_root_.CommHopfAlgCat.ofHom FS) := by
  let : IsDomain S := CFSG.isDomain_of_smooth_of_connected (k := k) S
  apply isIsogeny_of_lift D S q hq (_root_.CommHopfAlgCat.ofHom F) hF
    (_root_.CommHopfAlgCat.ofHom FS)
  exact _root_.CommHopfAlgCat.hom_ext heq

theorem exists_isogeny_lift_of_simplyConnected
    (D : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (S : TauCeti.SemisimpleCommHopfAlgCat.{u} k)
    (hS : TauCeti.simplyConnectedSemisimpleCommHopfAlgProperty k S)
    (q : D.obj ⟶ S.obj.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (F : D →ₐc[k] D) (hF : TauCeti.CommHopfAlgCat.IsIsogeny (_root_.CommHopfAlgCat.ofHom F)) :
    ∃ FS : S.obj →ₐc[k] S.obj,
      FS.comp q.hom = q.hom.comp F ∧
      TauCeti.CommHopfAlgCat.IsIsogeny (_root_.CommHopfAlgCat.ofHom FS) := by
  obtain ⟨FS, heq⟩ := exists_lift_of_simplyConnected D S hS q hq F
  let : Algebra.Smooth k S.obj := S.property.smooth
  let : ConnectedSpace (PrimeSpectrum S.obj) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k S.obj.obj
      S.property.geometricallyConnected
  exact ⟨FS,heq.symm,isIsogeny_of_lift_of_smooth_of_connected D S.obj q hq.isIsogeny
    F hF FS heq.symm⟩

end CFSG.LieType.AlgebraicGroups
