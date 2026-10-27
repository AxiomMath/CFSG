module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedReduction
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause2
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicNoA7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem alt7_simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt7_nonab : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 7)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  exact hnc ⟨⟨fun a b => hcon a b⟩⟩

theorem card_alternatingGroup_fin_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem center_eq_bot_of_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) :
    center X = ⊥ := by
  haveI := alt7_simple
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : e x = 1 := by
    apply eq_one_of_central_of_simple alt7_nonab
    intro b
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  exact e.injective (h1.trans e.map_one.symm)

theorem quotient_center_iso_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) :
    Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_alt7 e)).trans
    ((QuotientGroup.quotientBot : X ⧸ (⊥ : Subgroup X) ≃* X).trans e)⟩

theorem card_quotient_center_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) :
    Nat.card (X ⧸ center X) = 2520 := by
  obtain ⟨eQ⟩ := quotient_center_iso_alt7 e
  rw [Nat.card_congr eQ.toEquiv, card_alternatingGroup_fin_seven]

theorem isComponent_of_alt7 {G : Type} [Group G] (D : Subgroup G) [D.Normal]
    (e : ↥D ≃* alternatingGroup (Fin 7)) : CFSG.IsComponent D := by
  haveI := alt7_simple
  have hs : IsSimpleGroup ↥D := e.isSimpleGroup
  have hna : ∃ a b : ↥D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt7_nonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact ⟨CFSG.EvenSporadicStandard.Induction.Hyp.isQuasisimple_of_simple_nonabelian hs hna,
    Subgroup.Normal.isSubnormal inferInstance⟩

theorem exists_normal_alt7_of_prod {G : Type} [Group G]
    (ψ : G ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 7)) :
    ∃ D : Subgroup G, D.Normal ∧ Nonempty (↥D ≃* alternatingGroup (Fin 7)) := by
  let M : Subgroup (Multiplicative (ZMod 2) × alternatingGroup (Fin 7)) :=
    (MonoidHom.inr (Multiplicative (ZMod 2)) (alternatingGroup (Fin 7))).range
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hn
    refine MonoidHom.mem_range.mpr ⟨g.2 * a * g.2⁻¹, ?_⟩
    ext <;> simp
  have hinj : Function.Injective
      (MonoidHom.inr (Multiplicative (ZMod 2)) (alternatingGroup (Fin 7))) :=
    fun a b h => congrArg Prod.snd h
  have hmap : (M.comap ψ.toMonoidHom).map ψ.toMonoidHom = M :=
    Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective M
  refine ⟨M.comap ψ.toMonoidHom, Subgroup.Normal.comap hMn ψ.toMonoidHom, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective (M.comap ψ.toMonoidHom) ψ.toMonoidHom ψ.injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (MonoidHom.ofInjective hinj).symm)

theorem psl_two_two_three_admissible :
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 2 3 :=
  ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩

theorem psu_three_three_one_admissible :
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 3 1 :=
  ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩

theorem not_oddLieType_of_alt7_iso {X : Type} [Group X]
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (e : X ≃* alternatingGroup (Fin 7)) : ¬ CFSG.Blueprint.OddLieType X :=
  fun h => not_oddLieType_alt7 hO (oddLieType_transport e h)

theorem not_evenLieType_of_alt7_iso {X : Type} [Group X]
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (e : X ≃* alternatingGroup (Fin 7)) : ¬ CFSG.Blueprint.EvenLieType X :=
  fun h => not_evenLieType_alt7 hO (evenLieType_transport e h)

theorem noInnerZ2_alt7 : NoInnerZ2 (alternatingGroup (Fin 7)) := by
  intro S _ _ hS hna hcat z hz hne
  obtain ⟨e⟩ := hne
  have hI : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
  have hσ : orderOf (MulAut.conj z : MulAut S) = 2 :=
    (orderOf_injective (MulAut.conj : S →* MulAut S) hI z).trans hz
  have hσr : (MulAut.conj z : MulAut S) ∈ (MulAut.conj : S →* MulAut S).range :=
    MonoidHom.mem_range.mpr ⟨z, rfl⟩
  have hfix : fixedSubgroup (MulAut.conj z : MulAut S) = centralizer ({z} : Set S) :=
    CFSG.SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf z
  obtain ⟨D, hDn, ⟨eD⟩⟩ := exists_normal_alt7_of_prod ((MulEquiv.subgroupCongr hfix).trans e)
  haveI := hDn
  have hD : CFSG.IsComponent D := isComponent_of_alt7 D eD
  have hcard : Nat.card (↥D ⧸ center ↥D) = 2520 := card_quotient_center_alt7 eD
  obtain ⟨eQ⟩ := quotient_center_iso_alt7 eD
  have I : ArmInputs := armInputs_holds
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, hkn, -, ⟨θ⟩, -⟩ | ⟨-, hQP⟩ | ⟨-, hout, -⟩ | ⟨s, ⟨es⟩⟩
  ·
    exact alt_not_centralizer_Z2_alt (by omega) θ (Or.inr rfl) z hz ⟨e⟩
  · rcases hQP with hQ | hP
    · exact not_oddLieType_of_alt7_iso I.order eQ hQ
    · exact not_lieModel_of_alt7 I.order psl_two_two_three_admissible hP ⟨eD⟩
  ·
    exact hout hσr
  ·
    exact (sporadic_comp_2520 hS hna es hσ hD hcard).2 hσr

theorem noOuterFixed_alt7 : NoOuterFixed (alternatingGroup (Fin 7)) := by
  intro S _ _ hS hna hcat σ hσ hout hne
  obtain ⟨e⟩ := hne
  have eD : ↥(⊤ : Subgroup ↥(fixedSubgroup σ)) ≃* alternatingGroup (Fin 7) :=
    Subgroup.topEquiv.trans e
  have hD : CFSG.IsComponent (⊤ : Subgroup ↥(fixedSubgroup σ)) := isComponent_of_alt7 ⊤ eD
  have hcard := card_quotient_center_alt7 eD
  obtain ⟨eQ⟩ := quotient_center_iso_alt7 eD
  have I : ArmInputs := armInputs_holds
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, hkn, -, ⟨θ⟩, -⟩ | ⟨-, hQP⟩ | ⟨-, -, hEv⟩ | ⟨s, ⟨es⟩⟩
  ·
    exact alt_not_fixedSubgroup_alt (by omega) θ (Or.inr rfl) hσ ⟨e⟩
  · rcases hQP with hQ | hP
    · exact not_oddLieType_of_alt7_iso I.order eQ hQ
    · exact not_lieModel_of_alt7 I.order psl_two_two_three_admissible hP ⟨eD⟩
  · rcases hEv with hQ | hA6 | hU
    · exact not_evenLieType_of_alt7_iso I.order eQ hQ
    ·
      obtain ⟨e6⟩ := hA6
      have h6 := Nat.card_congr e6.toEquiv
      rw [card_alternatingGroup_fin_six, hcard] at h6
      omega
    · exact not_lieModel_of_alt7 I.order psu_three_three_one_admissible hU ⟨eQ⟩
  ·
    obtain ⟨rfl, -⟩ := sporadic_comp_2520 hS hna es hσ hD hcard
    have h1 := he_outer_fixedSubgroup_card es hσ hout
    have h2 := Nat.card_congr e.toEquiv
    rw [card_alternatingGroup_fin_seven] at h2
    omega

theorem catZ2A7_holds :
    CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 (alternatingGroup (Fin 7)) := by
  haveI := alt7_simple
  exact catNoAlmostSimpleZ2_of_noInner_noOuter alt7_nonab noInnerZ2_alt7 noOuterFixed_alt7

end CFSG.ComponentClassification.CatFC
