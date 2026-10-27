module

public import CFSG.LieType.Steinberg.Core
public import CFSG.LieType.Steinberg.Bridge
public import CFSG.LieType.Steinberg.Statement

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

universe u w

variable {K : Type u} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem bijective_stPi_of
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) :
    (⨆ γ ∈ D.roots, D.rootGroup γ = ⊤) ∧
      Function.Bijective (stPi (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup) :=
  ⟨hct.iSup_eq_top, (isSteinberg_of hct hext).bijective_stPi hct.iSup_eq_top⟩

theorem steinbergPresentation_of_extras
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) :
    D.SteinbergPresentation.{u, w} :=
  steinbergPresentation_of hct.iSup_eq_top
    ((isSteinberg_of hct hext).bijective_stPi hct.iSup_eq_top)

theorem presentationA_of
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) :
    PresentationA.{0, u, w} (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup := by
  refine ⟨hct.iSup_eq_top, (isSteinberg_of hct hext).bijective_stPi hct.iSup_eq_top, ?_⟩
  intro G _ φ hφ
  exact (isSteinberg_of hct hext).existsUnique_hom hct.iSup_eq_top φ hφ

end CFSG.LieType.Steinberg
