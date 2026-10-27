module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

section Restrict

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaStarNbr_subgroupOf_gen (hΩ : HypOmegaGen Ω) {Y K J : Subgroup G} (hKY : K ≤ Y)
    (hJY : J ≤ Y) (hJ : J ∈ omegaStarNbr Ω K) :
    J.subgroupOf Y ∈ omegaStarNbr (restrictFamily Ω Y) (K.subgroupOf Y) := by
  obtain ⟨hJΩ, hne, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R, -, J₁, hJ₁, hRJ₁, hUR, hcyc, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hJ₁J : J₁ = J := Sec6Gen.eq_of_mem_USet hΩ hU hJ₁ hJΩ (hUR.trans hRJ₁.1) hUJ
  rw [hJ₁J] at hRJ₁
  have hUY : U ≤ Y := hUJ.trans hJY
  have hRY : R ≤ Y := hRJ₁.1.trans hJY
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hrel' : (U.subgroupOf Y).relIndex (R.subgroupOf Y) = 2 := by
    have h2 := Subgroup.relIndex_map_map_of_injective (U.subgroupOf Y) (R.subgroupOf Y)
      Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hUY, Subgroup.map_subgroupOf_eq_of_le hRY] at h2
    rw [← h2]
    exact hrel
  refine ⟨subgroupOf_mem_restrictFamily hJΩ hJY, subgroupOf_ne_of_ne hKY hJY hne,
    U.subgroupOf Y, ⟨R.subgroupOf Y, mem_RSet_restrict hJΩ hJY hRJ₁,
      Subgroup.subgroupOf_mono Y hUR, ?_, hrel'⟩, Subgroup.subgroupOf_mono Y hUJ, ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUY)).mpr hcyc
  · intro u hu
    exact (mem_normalizer_subgroupOf_iff hKY).mp (hUN (Subgroup.mem_subgroupOf.mp hu))

theorem aViol_restrict_gen (hΩ : HypOmegaGen Ω) {Y K J : Subgroup G} {zK zJ : G} (hKY : K ≤ Y)
    (hJY : J ≤ Y) (hv : AViol Ω K J zK zJ) :
    AViol (restrictFamily Ω Y) (K.subgroupOf Y) (J.subgroupOf Y) (⟨zK, hKY hv.hzK.mem⟩ : Y)
      (⟨zJ, hJY hv.hzJ.mem⟩ : Y) := by
  have hstar := omegaStarNbr_subgroupOf_gen hΩ hKY hJY hv.star
  have hnbr : J.subgroupOf Y ∉ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y) :=
    fun h => hv.not_nbr (omegaNbr_of_restrict hKY hJY h)
  have hzK := isUniqueInvolution_subgroupOf hv.hzK hKY
  have hzJ := isUniqueInvolution_subgroupOf hv.hzJ hJY
  refine ⟨hstar, hnbr, hzK, hzJ, ?_⟩
  intro g hg hcon
  have hmem : (g : G) ∈ pairNormalizers K J zK zJ :=
    map_pairNormalizers_subgroupOf_le hKY hJY ⟨zK, hKY hv.hzK.mem⟩ ⟨zJ, hJY hv.hzJ.mem⟩
      (Subgroup.mem_map_of_mem Y.subtype hg)
  have h1 : conjSub (g : G) K ≤ Y := by
    have := conjSub_mono (n := (g : G)) hKY
    rwa [conjSub_eq_self_of_mem g.2] at this
  have hconj : conjSub (g : G) K = J := by
    rw [conjSub_subgroupOf Y g K] at hcon
    have := Subgroup.subgroupOf_inj.mp hcon
    rwa [inf_eq_left.mpr h1, inf_eq_left.mpr hJY] at this
  exact hv.no_conj _ hmem hconj

theorem TypeRHyp.restrict (h : TypeRHyp Ω) (X : Subgroup G) : TypeRHyp (restrictFamily Ω X) where
  hyp := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.hypOmegaGen_restrict h.hyp X
  twoGroup := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    let φ : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
    exact (h.twoGroup L hL).of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  sylow := by
    rintro _ ⟨L, hL, hLX, rfl⟩ P hP
    have hP' : IsSylow2In (P.map X.subtype) L := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hLX] at this
    obtain ⟨e⟩ := h.sylow L hL _ hP'
    exact ⟨(P.equivMapOfInjective X.subtype X.subtype_injective).trans e⟩

end Restrict

section Datum

variable {T : Type} [Group T]

theorem typeRHyp_of_datum {R : Subgroup T} {t : T} (hD : FrameTightDatum R t) :
    TypeRHyp (CoreAssembly.conjClass R) where
  hyp := hD.hyp
  twoGroup := by
    rintro J ⟨g, rfl⟩
    let e : ↥R ≃* ↥(conjSub g R) :=
      R.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    let φ : ↥(conjSub g R) ≃* ↥R := e.symm
    exact hD.twoGroup.of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  sylow := by
    rintro J ⟨g, rfl⟩ P hP
    have h1 : IsSylow2In (conjSub g⁻¹ P) R := by
      have := Sec6Gen.isSylow2In_conjSub hP g⁻¹
      rwa [conjSub_inv_conjSub] at this
    obtain ⟨e⟩ := hD.quat _ h1
    exact ⟨(P.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).trans
      e⟩

end Datum

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaGen_aStar_restrict (hΩ : HypOmegaGen Ω) {K H : Subgroup G}
    (hH : omegaGen (aStar Ω K) = H) :
    omegaGen (aStar (restrictFamily Ω H) (K.subgroupOf H)) = ⊤ := by
  have hMH : ∀ M ∈ aStar Ω K, M ≤ H := fun M hM => hH ▸ le_omegaGen hM
  have hKH : K ≤ H := hMH K Relation.ReflTransGen.refl
  have key : ∀ M ∈ aStar Ω K, M.subgroupOf H ∈ aStar (restrictFamily Ω H) (K.subgroupOf H) := by
    intro M hM
    induction hM with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      rename_i b c
      have hbH : b ≤ H := hMH b hab
      have hcH : c ≤ H := hMH c (hab.tail hbc)
      refine ih.tail ?_
      obtain ⟨hcΩ, hA | hA | ⟨htw, hne⟩⟩ := hbc
      · obtain ⟨zb, zc, hv⟩ := hA
        exact ⟨subgroupOf_mem_restrictFamily hcΩ hcH,
          Or.inl ⟨_, _, aViol_restrict_gen hΩ hbH hcH hv⟩⟩
      · obtain ⟨zc, zb, hv⟩ := hA
        exact ⟨subgroupOf_mem_restrictFamily hcΩ hcH,
          Or.inr (Or.inl ⟨_, _, aViol_restrict_gen hΩ hcH hbH hv⟩)⟩
      · exact ⟨subgroupOf_mem_restrictFamily hcΩ hcH,
          Or.inr (Or.inr ⟨twinSet_subgroupOf hbH hcH htw,
            subgroupOf_ne_of_ne hbH hcH hne⟩)⟩
  have hle : H ≤ (omegaGen (aStar (restrictFamily Ω H) (K.subgroupOf H))).map H.subtype := by
    refine hH.symm.le.trans (iSup₂_le fun M hM => ?_)
    have h1 : M.subgroupOf H ≤ omegaGen (aStar (restrictFamily Ω H) (K.subgroupOf H)) :=
      le_omegaGen (key M hM)
    have h2 := Subgroup.map_mono (f := H.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le (hMH M hM)] at h2
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  exact le_antisymm (Subgroup.map_subtype_le _) hle

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
