module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open

attribute [local instance] CFSG.LocalCores.layer_characteristic

variable {G : Type*} [Group G]

theorem open_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q := by
  obtain ⟨hp, hs, -⟩ := h
  exact ⟨hp.commutator_eq_top, hs⟩

theorem isSubnormal_map {H K : Subgroup G} (h : IsSubnormal H K) {G' : Type*} [Group G']
    (f : G →* G') (hf : Function.Injective f) : IsSubnormal (H.map f) (K.map f) := by
  clear hf
  induction h with
  | refl => exact CFSG.Open.IsSubnormal.refl _
  | @step H M K hle hnormal _ ih =>
    refine CFSG.Open.IsSubnormal.step (Subgroup.map_mono hle) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hle)]
    rintro _ _ ⟨x, hx, rfl⟩ ⟨m, hm, rfl⟩
    rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
    exact ⟨m * x * m⁻¹, hnormal x m hx hm, by simp⟩

private theorem isComponentOf_map_of_injective {G' : Type*} [Group G'] {L K : Subgroup G}
    (h : IsComponentOf L K) (f : G →* G') (hf : Function.Injective f) :
    IsComponentOf (L.map f) (K.map f) := by
  obtain ⟨hLK, hsub, hq⟩ := h
  exact ⟨Subgroup.map_mono hLK, isSubnormal_map hsub f hf,
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L f hf) hq⟩

theorem isComponentOf_map_subtype {C : Subgroup G} {L : Subgroup ↥C} (hL : CFSG.IsComponent L) :
    IsComponentOf (L.map C.subtype) C := by
  have h1 := isComponentOf_map_of_injective ((CFSG.isComponent_iff_open L).1 hL) C.subtype
    C.subtype_injective
  have htop : (⊤ : Subgroup ↥C).map C.subtype = C := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rwa [htop] at h1

theorem map_layer_le_glaLayer (C : Subgroup G) : (CFSG.layer ↥C).map C.subtype ≤ GLALayer C := by
  rw [CFSG.layer.eq_sSup, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  have hL' : CFSG.IsComponent L := hL
  exact Subgroup.map_le_iff_le_comap.1
    (le_sSup (show L.map C.subtype ∈ {K : Subgroup G | IsComponentOf K C} from
      isComponentOf_map_subtype hL'))

private theorem isSolvable_quotient_of_eq {A : Type*} [Group A] {X Y : Subgroup A} [X.Normal]
    [Y.Normal] (hXY : X = Y) (h : Group.IsSolvable (A ⧸ X)) : Group.IsSolvable (A ⧸ Y) := by
  subst hXY
  exact h

theorem perfectInLayer_of_isSolvable_layer_quotient (β : MulAut G)
    (h : Group.IsSolvable (↥(fixSubgroup β) ⧸ CFSG.layer ↥(fixSubgroup β))) :
    PerfectInLayer β := by
  intro P hPC hP
  have hN : ((CFSG.layer ↥(fixSubgroup β)).map (fixSubgroup β).subtype).subgroupOf
      (fixSubgroup β) = CFSG.layer ↥(fixSubgroup β) :=
    Subgroup.comap_map_eq_self_of_injective (fixSubgroup β).subtype_injective _
  haveI : (((CFSG.layer ↥(fixSubgroup β)).map (fixSubgroup β).subtype).subgroupOf
      (fixSubgroup β)).Normal := by
    rw [hN]
    infer_instance
  have hsol := isSolvable_quotient_of_eq hN.symm h
  exact (perfect_le_of_solvable_quotient (Subgroup.map_subtype_le (CFSG.layer ↥(fixSubgroup β)))
    hsol hPC hP).trans (map_layer_le_glaLayer (fixSubgroup β))

theorem isComponentOf_of_normal_normal {C N L : Subgroup G} (hLN : L ≤ N) (hNC : N ≤ C)
    (hLn : (L.subgroupOf N).Normal) (hNn : (N.subgroupOf C).Normal) (hL : CFSG.IsQuasisimple L) :
    IsComponentOf L C := by
  exact ⟨hLN.trans hNC,
    CFSG.Open.IsSubnormal.step hLN hLn
      (CFSG.Open.IsSubnormal.step hNC hNn (CFSG.Open.IsSubnormal.refl C)),
    open_isQuasisimple hL⟩

private theorem glaLayer_map_le {S : Type*} [Group S] (e : S ≃* G) (H : Subgroup S) :
    GLALayer (H.map (e : S →* G)) ≤ (GLALayer H).map (e : S →* G) := by
  unfold GLALayer
  refine sSup_le fun K hK => ?_
  have hK0 : IsComponentOf K (H.map (e : S →* G)) := hK
  have hK' : IsComponentOf (K.map (e.symm : G →* S)) H := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK0
    have hcomp : (e.symm : G →* S).comp (e : S →* G) = MonoidHom.id S := by
      ext x
      simp
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
  have hmem : K.map (e.symm : G →* S) ∈ {K : Subgroup S | IsComponentOf K H} := hK'
  intro x hx
  exact Subgroup.mem_map.2
    ⟨e.symm x, le_sSup hmem (Subgroup.mem_map_of_mem (e.symm : G →* S) hx), by simp⟩

theorem perfectInLayer_of_congr {S : Type*} [Group S] (e : S ≃* G) (β : MulAut S)
    (h : PerfectInLayer (MulAut.congr e β)) : PerfectInLayer β := by
  intro P hPC hP
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hP' : P.map (e : S →* G) ≤ fixSubgroup (MulAut.congr e β) := by
    rw [hfix]
    exact Subgroup.map_mono hPC
  have hperf : ⁅P.map (e : S →* G), P.map (e : S →* G)⁆ = P.map (e : S →* G) := by
    rw [← Subgroup.map_commutator, hP]
  have h1 := h (P.map (e : S →* G)) hP' hperf
  rw [hfix] at h1
  exact (Subgroup.map_le_map_iff_of_injective (f := (e : S →* G)) e.injective).1
    (h1.trans (glaLayer_map_le e (fixSubgroup β)))

theorem perfectInLayer_conj (γ β : MulAut G) (h : PerfectInLayer β) :
    PerfectInLayer (γ * β * γ⁻¹) := by
  have hc : MulAut.congr (γ⁻¹ : G ≃* G) (γ * β * γ⁻¹) = β := by
    ext x
    show γ.symm (γ (β (γ.symm (γ x)))) = β x
    simp
  refine perfectInLayer_of_congr (γ⁻¹ : G ≃* G) (γ * β * γ⁻¹) ?_
  rw [hc]
  exact h

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
