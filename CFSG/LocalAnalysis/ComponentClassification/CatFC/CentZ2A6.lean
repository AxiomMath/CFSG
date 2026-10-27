module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedReduction
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicNoA6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem alt6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt6_nonab : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  exact hnc ⟨⟨fun a b => hcon a b⟩⟩

theorem alt6_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem center_eq_bot_of_alt6 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    center X = ⊥ := by
  haveI := alt6_simple
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : e x = 1 := by
    apply eq_one_of_central_of_simple alt6_nonab
    intro b
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  exact e.injective (h1.trans e.map_one.symm)

theorem quotient_center_iso_alt6 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 6)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_alt6 e)).trans
    ((QuotientGroup.quotientBot : X ⧸ (⊥ : Subgroup X) ≃* X).trans e)⟩

theorem card_quotient_center_alt6 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    Nat.card (X ⧸ center X) = 360 := by
  obtain ⟨eQ⟩ := quotient_center_iso_alt6 e
  rw [Nat.card_congr eQ.toEquiv, alt6_card]

theorem isComponent_of_alt6 {G : Type} [Group G] (D : Subgroup G) [D.Normal]
    (e : ↥D ≃* alternatingGroup (Fin 6)) : CFSG.IsComponent D := by
  haveI := alt6_simple
  have hs : IsSimpleGroup ↥D := e.isSimpleGroup
  have hna : ∃ a b : ↥D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt6_nonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact ⟨CFSG.EvenSporadicStandard.Induction.Hyp.isQuasisimple_of_simple_nonabelian hs hna,
    Subgroup.Normal.isSubnormal inferInstance⟩

theorem exists_normal_alt6_of_prod {G : Type} [Group G]
    (ψ : G ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) :
    ∃ D : Subgroup G, D.Normal ∧ Nonempty (↥D ≃* alternatingGroup (Fin 6)) := by
  let M : Subgroup (Multiplicative (ZMod 2) × alternatingGroup (Fin 6)) :=
    (MonoidHom.inr (Multiplicative (ZMod 2)) (alternatingGroup (Fin 6))).range
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hn
    refine MonoidHom.mem_range.mpr ⟨g.2 * a * g.2⁻¹, ?_⟩
    ext <;> simp
  have hinj : Function.Injective
      (MonoidHom.inr (Multiplicative (ZMod 2)) (alternatingGroup (Fin 6))) :=
    fun a b h => congrArg Prod.snd h
  have hmap : (M.comap ψ.toMonoidHom).map ψ.toMonoidHom = M :=
    Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective M
  refine ⟨M.comap ψ.toMonoidHom, Subgroup.Normal.comap hMn ψ.toMonoidHom, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective (M.comap ψ.toMonoidHom) ψ.toMonoidHom ψ.injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (MonoidHom.ofInjective hinj).symm)

@[expose] def A6InnerOddLie : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], CFSG.Blueprint.OddLieType S →
    ∀ z : S, orderOf z = 2 →
      ¬ Nonempty (↥(Subgroup.centralizer ({z} : Set S)) ≃*
        Multiplicative (ZMod 2) × alternatingGroup (Fin 6))

@[expose] def A6OuterLie : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    (CFSG.Blueprint.OddLieType S ∨ CFSG.Blueprint.EvenLieType S) →
      ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
        ¬ Nonempty (↥(CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ) ≃*
          alternatingGroup (Fin 6))

theorem noInnerZ2_alt6_of_lie (hL : A6InnerOddLie) : NoInnerZ2 (alternatingGroup (Fin 6)) := by
  intro S _ _ hS hna hcat z hz hne
  obtain ⟨e⟩ := hne
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition S hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | ⟨s, ⟨es⟩⟩
  ·
    exact alt_not_centralizer_Z2_alt (k := 6) hn θ (Or.inl rfl) z hz ⟨e⟩
  ·
    exact hL S hodd z hz ⟨e⟩
  ·
    obtain ⟨B, hBn, ⟨eB⟩⟩ := exists_normal_alt6_of_prod e
    haveI := hBn
    exact CFSG.ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType
      heven z hz B (isComponent_of_alt6 B eB)
  ·
    have hI : Function.Injective (MulAut.conj : S →* MulAut S) :=
      CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
    have hσ : orderOf (MulAut.conj z : MulAut S) = 2 :=
      (orderOf_injective (MulAut.conj : S →* MulAut S) hI z).trans hz
    have hσr : (MulAut.conj z : MulAut S) ∈ (MulAut.conj : S →* MulAut S).range :=
      MonoidHom.mem_range.mpr ⟨z, rfl⟩
    have hfix : fixedSubgroup (MulAut.conj z : MulAut S) = centralizer ({z} : Set S) :=
      CFSG.SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf z
    obtain ⟨D, hDn, ⟨eD⟩⟩ := exists_normal_alt6_of_prod ((MulEquiv.subgroupCongr hfix).trans e)
    haveI := hDn
    have hD : CFSG.IsComponent D := isComponent_of_alt6 D eD
    have hcard := card_quotient_center_alt6 eD
    rcases sporadic_comp_360 hS hna es hσ hD hcard with ⟨rfl, -⟩ | ⟨-, hout⟩
    ·
      have h720 : Nat.card ↥(centralizer ({z} : Set S)) = 720 := by
        have h := Nat.card_congr e.toEquiv
        rw [Nat.card_prod, natCard_multiplicative_zmod_two, alt6_card] at h
        omega
      exact hs_card_centralizer_ne_720 es z hz h720
    ·
      exact hout hσr

theorem noOuterFixed_alt6_of_lie (hL : A6OuterLie) : NoOuterFixed (alternatingGroup (Fin 6)) := by
  intro S _ _ hS hna hcat σ hσ hout hne
  obtain ⟨e⟩ := hne
  have eD : ↥(⊤ : Subgroup ↥(fixedSubgroup σ)) ≃* alternatingGroup (Fin 6) :=
    Subgroup.topEquiv.trans e
  have hD : CFSG.IsComponent (⊤ : Subgroup ↥(fixedSubgroup σ)) := isComponent_of_alt6 ⊤ eD
  have hcard := card_quotient_center_alt6 eD
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition S hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | ⟨s, ⟨es⟩⟩
  ·
    exact alt_not_fixedSubgroup_alt (k := 6) hn θ (Or.inl rfl) hσ ⟨e⟩
  ·
    exact hL S (Or.inl hodd) σ hσ hout ⟨e⟩
  ·
    exact hL S (Or.inr heven) σ hσ hout ⟨e⟩
  ·
    rcases sporadic_comp_360 hS hna es hσ hD hcard with ⟨-, hin⟩ | ⟨rfl, -⟩
    · exact hout hin
    ·
      have h1 := he_outer_fixedSubgroup_card es hσ hout
      have h2 := Nat.card_congr e.toEquiv
      rw [alt6_card] at h2
      omega

theorem catZ2A6_of_lie (hI : A6InnerOddLie) (hO : A6OuterLie) :
    CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)) := by
  haveI := alt6_simple
  exact catNoAlmostSimpleZ2_of_noInner_noOuter alt6_nonab (noInnerZ2_alt6_of_lie hI)
    (noOuterFixed_alt6_of_lie hO)

end CFSG.ComponentClassification.CatFC
