module

public import CFSG.Mathlib.RingTheory.FinitePoints
public import CFSG.ThirdParty.TauCeti.GenericFreeness
public import CFSG.LieType.AlgebraicGroups.RationalPointEndomorphism
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Finiteness

public noncomputable section
open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem moduleFinite_kernel_of_finite_ker_points
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : H.obj ⟶ K.obj)
    [Finite (TauCeti.AlgHom.mapDomain (A := k) f.hom).ker] :
    Module.Finite k (K ⧸ (TauCeti.CommHopfAlgCat.kernelHopfIdeal f).toIdeal) := by
  let I := TauCeti.CommHopfAlgCat.kernelHopfIdeal f
  have hker := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
    f (CommAlgCat.of k k)
  change TauCeti.CommHopfAlgCat.quotientPointsSubgroup K.obj I (CommAlgCat.of k k) =
    (TauCeti.AlgHom.mapDomain (A := k) f.hom).ker at hker
  let : Finite (TauCeti.CommHopfAlgCat.quotientPointsSubgroup K.obj I (CommAlgCat.of k k)) :=
    hker.symm ▸ inferInstance
  let e := TauCeti.CommHopfAlgCat.quotientPointsSubgroupIso K.obj I (CommAlgCat.of k k)
  let : Finite (WithConv ((K ⧸ I.toIdeal) →ₐ[k] k)) :=
    Finite.of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).1
  let : Finite ((K ⧸ I.toIdeal) →ₐ[k] k) := Finite.of_injective toConv toConv_injective
  exact moduleFinite_of_finite_algHom (K ⧸ I.toIdeal)

theorem injective_of_surjective_points
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    (f : H.obj ⟶ K.obj)
    (hf : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) f.hom)) :
    Function.Injective f.hom := by
  intro a b hab
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro p
  obtain ⟨t, ht⟩ := hf (toConv p)
  have hta := congrArg (fun v => v.ofConv a) ht
  have htb := congrArg (fun v => v.ofConv b) ht
  exact hta.symm.trans ((congrArg t.ofConv hab).trans htb)

theorem isIsogeny_of_surjective_points_of_finite_ker
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    (f : H.obj ⟶ K.obj)
    [Finite (TauCeti.AlgHom.mapDomain (A := k) f.hom).ker]
    (hf : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) f.hom)) :
    TauCeti.CommHopfAlgCat.IsIsogeny f := by
  have hflat := CFSG.ThirdParty.TauCeti.CommHopfAlgCat.faithfullyFlat_of_dominant f
    ((RingHom.denseRange_comap_iff_injective _).2 (injective_of_surjective_points H K f hf))
  exact (TauCeti.CommHopfAlgCat.isIsogeny_iff f).2 ⟨
    (TauCeti.CommHopfAlgCat.finite_iff_moduleFinite_quotient_kernelHopfIdeal f hflat).2
      (moduleFinite_kernel_of_finite_ker_points H K f), hflat⟩

theorem isIsogeny_of_injective_points
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    (F : H.obj ⟶ H.obj)
    (hF : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) F.hom)) :
    TauCeti.CommHopfAlgCat.IsIsogeny F := by
  have hFi : Function.Injective (fun p : H →ₐ[k] k => p.comp F.hom.toAlgHom) := by
    intro p q hpq
    exact WithConv.toConv_injective (hF (congrArg WithConv.toConv hpq))
  have hFs : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) F.hom) := by
    intro p
    obtain ⟨q, hq⟩ := RationalPoints.surjective_comp_of_injective F.hom.toAlgHom hFi p.ofConv
    exact ⟨toConv q, congrArg WithConv.toConv hq⟩
  let : Subsingleton (TauCeti.AlgHom.mapDomain (A := k) F.hom).ker := by
    rw [MonoidHom.ker_eq_bot _ hF]
    infer_instance
  exact isIsogeny_of_surjective_points_of_finite_ker H H F hFs

omit [IsAlgClosed k] in
theorem injective_mapDomain_of_restriction
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (j : H →ₐc[k] K) (hj : Function.Surjective j)
    (F : H →ₐc[k] H) (FK : K →ₐc[k] K)
    (heq : FK.comp j = j.comp F)
    (hF : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) F)) :
    Function.Injective (TauCeti.AlgHom.mapDomain (A := k) FK) := by
  have hji := TauCeti.CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective
    (_root_.CommHopfAlgCat.ofHom j) hj (CommAlgCat.of k k)
  change Function.Injective (TauCeti.AlgHom.mapDomain (A := k) j) at hji
  have hc : (TauCeti.AlgHom.mapDomain (A := k) F).comp (TauCeti.AlgHom.mapDomain j) =
      (TauCeti.AlgHom.mapDomain j).comp (TauCeti.AlgHom.mapDomain FK) := by
    rw [← TauCeti.AlgHom.mapDomain_comp, ← TauCeti.AlgHom.mapDomain_comp, heq]
  intro p q hpq
  apply hji
  apply hF
  simpa only [← MonoidHom.comp_apply, hc] using congrArg (TauCeti.AlgHom.mapDomain j) hpq

theorem isIsogeny_of_restriction_of_injective_points
    (H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced K]
    (j : H →ₐc[k] K) (hj : Function.Surjective j)
    (F : H →ₐc[k] H) (FK : K →ₐc[k] K)
    (heq : FK.comp j = j.comp F)
    (hF : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) F)) :
    TauCeti.CommHopfAlgCat.IsIsogeny (_root_.CommHopfAlgCat.ofHom FK) :=
  isIsogeny_of_injective_points K (_root_.CommHopfAlgCat.ofHom FK)
    (injective_mapDomain_of_restriction H K j hj F FK heq hF)

end CFSG.LieType.AlgebraicGroups
