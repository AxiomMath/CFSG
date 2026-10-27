module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Act

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

variable {G : Type} [Group G] {E : Subgroup G}

@[expose] noncomputable def subgroupOfNormalizerEquiv (E : Subgroup G) :
    ↥(E.subgroupOf (normalizer (E : Set G))) ≃* ↥E :=
  Subgroup.subgroupOfEquivOfLe le_normalizer

theorem CocodeExtension.of_normalizer (hcent : centralizer (E : Set G) = E) (e : ↥E ≃* W11)
    (hX : (S44.actN E).range.map (MulAut.congr e).toMonoidHom = img11 AutPerm) :
    CocodeExtension ↥(normalizer (E : Set G)) (E.subgroupOf (normalizer (E : Set G)))
      ((subgroupOfNormalizerEquiv E).trans e) where
  normal := Subgroup.normal_in_normalizer
  centralizer_eq := by
    ext n
    rw [mem_centralizer_iff, mem_subgroupOf]
    constructor
    · intro h
      have hn : (n : G) ∈ centralizer (E : Set G) := by
        rw [mem_centralizer_iff]
        intro x hx
        exact congrArg Subtype.val (h ⟨x, le_normalizer hx⟩ hx)
      rwa [hcent] at hn
    · intro hn x hx
      have hn' : (n : G) ∈ centralizer (E : Set G) := by rwa [hcent]
      exact Subtype.ext (mem_centralizer_iff.1 hn' x hx)
  range_eq := by
    rw [← hX, MonoidHom.map_range, MonoidHom.map_range]
    congr 1
    refine MonoidHom.ext fun n => MulEquiv.ext fun w => ?_
    refine congrArg e (Subtype.ext ?_)
    simp [S44.actN_apply, MulAut.conjNormal_apply, subgroupOfNormalizerEquiv]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
