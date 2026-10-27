module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuCase
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms

namespace L34R

theorem not_isL34Type_of_comps {s : TauCeti.SporadicName}
    (hfree : CatalogueU.SporadicOddCoreFree s)
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => ¬ SmallCentralQuotient Y)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 → α ∉ inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) fun Y _ => ¬ SmallCentralQuotient Y)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  intro hL
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  have hcore := CatLeaf.oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (CatLeaf.mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hsL : SmallCentralQuotient L :=
    Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ hL))
  have key : ∀ {F : Subgroup S} (hF : fixedSubgroup σ = F),
      IsComponent (L.map (MulEquiv.subgroupCongr hF).toMonoidHom) ∧
        SmallCentralQuotient (L.map (MulEquiv.subgroupCongr hF).toMonoidHom) := by
    intro F hF
    set φ := MulEquiv.subgroupCongr hF
    exact ⟨⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (L.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hcomp.1,
      Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hcomp.2⟩,
      smallCentralQuotient_of_mulEquiv (L.equivMapOfInjective φ.toMonoidHom φ.injective).symm
        hsL⟩
  rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  ·
    obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      ext x
      rw [mem_centralizer_singleton_iff]
      change t * x * t⁻¹ = x ↔ x * t = t * x
      rw [mul_inv_eq_iff_eq_mul]
      exact eq_comm
    obtain ⟨hB, hsB⟩ := key hfix
    exact hin S ⟨e⟩ t ht2 _ hB hsB
  ·
    have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
      ext x
      exact Iff.rfl
    obtain ⟨hB, hsB⟩ := key hfix
    exact hout S inferInstance hna ⟨e⟩ σ (MulEquiv.ext fun y => h.1 y) hout' _ hB hsB

theorem not_isL34Type_M22
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .M22) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  refine not_isL34Type_of_comps CatalogueU.sporadicOddCoreFree_M22 (fun G _ _ ⟨e⟩ t ht => ?_)
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => ?_) hna e h
  · exact (compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 384)
      m22_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_card_dvd
        not_isSmallOrder_dvd_384 h
  · refine CompsSatisfy.of_mulEquiv isoInvariant_not_small (fixSubTransportEquiv e α) ?_
    exact (m22_outer_comps _ (transportAut_mul_self e hα2)
      (transportAut_not_mem_inner e hα)).mono fun Y _ h => not_small_of_not_three h

theorem not_isL34Type_Ru
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Ru) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  refine not_isL34Type_of_comps CatalogueU.sporadicOddCoreFree_Ru (fun G _ _ ⟨e⟩ t ht => ?_)
    (outer_of_forall_inner (mem_inner_of_mulEquiv Sporadic.RuSchreier.ruEquivP
      Sporadic.RuSchreier.mulAut_inner)) hna e h
  exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd ru_centralizerIn_comps
    (e.trans Sporadic.RuSchreier.ruEquivP) t ht).mono fun Y _ h => not_small_of_not_three h

end L34R

end CFSG.ComponentClassification.GrSLit
