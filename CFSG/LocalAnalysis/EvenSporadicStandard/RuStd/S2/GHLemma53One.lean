module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GHLemma53OneM10
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GHLemma53OneFStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.M10
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentralizerFieldsA6

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Open

section Reduction

variable {X : Type} [Group X] [Finite X] {t : X}

theorem eq_one_of_forall_commute_of_centralizer_equiv_prod_M10
    (ht : orderOf t = 2) (htc : t ∉ center X)
    (e : ↥(centralizer ({t} : Set X)) ≃* (Multiplicative (ZMod 2) × M10)) {x : X}
    (hx : ∀ g : X, g * x = x * g) : x = 1 := by
  by_contra hx1
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  let c : ↥(centralizer ({t} : Set X)) := ⟨x, mem_centralizer_singleton_iff.2 (hx t).symm⟩
  have hc : c ∈ center ↥(centralizer ({t} : Set X)) :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hx (g : X))
  have hc1 : c ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext_iff.mp h)
  have hzc : SolomonRed.zz t ∈ center ↥(centralizer ({t} : Set X)) :=
    Subgroup.mem_center_iff.2 fun g => SolomonRed.zz_comm g
  have hz1 : SolomonRed.zz t ≠ 1 := by
    intro h
    exact ht1 (by simpa [SolomonRed.zz] using Subtype.ext_iff.mp h)
  have h1 := mulEquiv_central_involution_prod_M10 e hc hc1
  have h2 := mulEquiv_central_involution_prod_M10 e hzc hz1
  have hct : c = SolomonRed.zz t := e.injective (h1.trans h2.symm)
  have hxt_eq : x = t := by
    have h := Subtype.ext_iff.mp hct
    simpa [c, SolomonRed.zz] using h
  exact htc (Subgroup.mem_center_iff.2 fun g => by rw [← hxt_eq]; exact hx g)

private theorem fusionZStar_eq_bot_of_forall_commute {Y : Type} [Group Y]
    (hO : fusionOddCore Y = ⊥) (hZ : ∀ y : Y, (∀ g : Y, g * y = y * g) → y = 1) :
    fusionZStar Y = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  rw [mem_bot]
  refine hZ y fun g => ?_
  have h1 : QuotientGroup.mk' (fusionOddCore Y) y ∈ center (Y ⧸ fusionOddCore Y) := hy
  rw [mem_center_iff] at h1
  have h2 := h1 (QuotientGroup.mk' (fusionOddCore Y) g)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, hO, mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem fusionZStar_eq_bot_of_centralizer_equiv_prod_M10
    (hO : CFSG.oddCore X = ⊥) (ht : orderOf t = 2) (htc : t ∉ center X)
    (e : ↥(centralizer ({t} : Set X)) ≃* (Multiplicative (ZMod 2) × M10)) :
    fusionZStar X = ⊥ := by
  refine fusionZStar_eq_bot_of_forall_commute (Y := X) ?_ ?_
  · exact hO
  · intro y hy
    exact eq_one_of_forall_commute_of_centralizer_equiv_prod_M10 ht htc e hy

theorem solomonM10Hyp_of_centralizer_equiv_prod_M10
    (ht : orderOf t = 2)
    (e : ↥(centralizer ({t} : Set X)) ≃* (Multiplicative (ZMod 2) × M10)) :
    Fin76b.SolomonM10Hyp X t := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hzc : SolomonRed.zz t ∈ center ↥(centralizer ({t} : Set X)) :=
    Subgroup.mem_center_iff.2 fun g => SolomonRed.zz_comm g
  have hz1 : SolomonRed.zz t ≠ 1 := by
    intro h
    exact ht1 (by simpa [SolomonRed.zz] using Subtype.ext_iff.mp h)
  have hz : e (SolomonRed.zz t) = (Multiplicative.ofAdd 1, 1) :=
    mulEquiv_central_involution_prod_M10 e hzc hz1
  obtain ⟨Ab, ⟨iso⟩, hzAb, hidx, hsq⟩ := exists_alt6_subgroup_of_mulEquiv_prod_M10 e hz
  have hOC : fusionOddCore ↥(centralizer ({t} : Set X)) = ⊥ :=
    fusionOddCore_eq_bot_of_mulEquiv_prod_M10 e
  let θ := SolomonRed.mulEquivQuotientOddCore hOC
  have hzbar : Fin76b.zbarC X t = θ (SolomonRed.zz t) := rfl
  have hzbar' : Fin76b.zbarC X t = θ.toMonoidHom (SolomonRed.zz t) := rfl
  have hmap : Ab.map θ.toMonoidHom ⊔ zpowers (Fin76b.zbarC X t)
      = (Ab ⊔ zpowers (SolomonRed.zz t)).map θ.toMonoidHom := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← hzbar']
  refine ⟨Ab.map θ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact ⟨(Subgroup.equivMapOfInjective Ab θ.toMonoidHom θ.injective).symm.trans iso⟩
  · intro h
    rw [hzbar, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h
    exact hzAb h
  · rw [hmap]
    exact (Subgroup.index_map_of_bijective (f := θ.toMonoidHom) θ.bijective _).trans hidx
  · intro h hh
    obtain ⟨h', rfl⟩ := θ.surjective h
    rw [hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    apply hsq
    have h2 : θ (h' * h') ∈ (zpowers (SolomonRed.zz t)).map θ.toMonoidHom := by
      rw [MonoidHom.map_zpowers, ← hzbar']
      simpa only [map_mul] using hh
    rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h2

end Reduction

theorem ghLemma53_1_of_solomonM10
    (hSol : Fin76b.SolomonM10) :
    GHLemma53_1 := by
  intro X _ _ hK hO t ht htc e
  obtain ⟨e⟩ := e
  have hZ : fusionZStar X = ⊥ :=
    fusionZStar_eq_bot_of_centralizer_equiv_prod_M10 hO ht htc e
  have hOC : fusionOddCore ↥(centralizer ({t} : Set X)) = ⊥ :=
    fusionOddCore_eq_bot_of_mulEquiv_prod_M10 e
  have hHyp : Fin76b.SolomonM10Hyp X t := solomonM10Hyp_of_centralizer_equiv_prod_M10 ht e
  have hconcl := hSol X hK t ht hZ hOC hHyp
  rcases hconcl.2 with hN' | hU
  · obtain ⟨N, hN, ⟨eN⟩, hCN⟩ := hN'
    haveI := hN
    exact Or.inr (nonempty_fStar_equiv_prod_of_normal N eN hCN)
  · obtain ⟨eU⟩ := hU
    exact Or.inl (nonempty_fStar_equiv_U43_of_mulEquiv_U43Ext eU)

section Holds

set_option linter.unusedSectionVars false


theorem ghLemma53_1_holds : GHLemma53_1 :=
  ghLemma53_1_of_solomonM10
    (SolomonRed.solomonM10_of_cat ComponentClassification.CatFC.catM10_holds)

end Holds

end CFSG.EvenSporadicStandard.RuStd.S2
