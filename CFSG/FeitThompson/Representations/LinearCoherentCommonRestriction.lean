module

public import CFSG.FeitThompson.Representations.CentralLayerCharacterRegularDifference
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
import CFSG.FeitThompson.Representations.CentralLayerCoefficientIntegral
import CFSG.FeitThompson.Representations.DisjointConjugateFamiliesOrthogonalImages
import CFSG.FeitThompson.Representations.LinearFrobeniusLayerCoherence
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup NormalLinearInduced

section General

variable {G : Type*} [Group G] [Fintype G] {L P : Subgroup G} [Fintype ↥L]
  [(P.subgroupOf L).Normal]

theorem cfInner_coherent_eq_zero_of_disjoint_tiInduced
    (hTI : IsTIWithNormalizer ((P : Set G) \ {1}) L) {S T : Set (↥L → ℂ)}
    (hSind : S ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)))
    (hTind : T ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)))
    (hSirr : S ⊆ Irr ↥L) (hTirr : T ⊆ Irr ↥L)
    (hdisj : Disjoint S T) (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hSstar : ∀ χ ∈ S, star χ ∈ S) (hTstar : ∀ χ ∈ T, star χ ∈ T)
    (hSnr : ∀ χ ∈ S, star χ ≠ χ) (hTnr : ∀ χ ∈ T, star χ ≠ χ)
    {τS : charSpanZero S →+ virtualChars G}
    (hτS : ∀ f, (τS f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    {τT : charSpanZero T →+ virtualChars G}
    (hτT : ∀ f, (τT f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    {νS : Submodule.span ℤ S →+ virtualChars G} {νT : Submodule.span ℤ T →+ virtualChars G}
    (hνS : IsCoherentWith S τS νS) (hνT : IsCoherentWith T τT νT)
    {ξ η : ↥L → ℂ} (hξ : ξ ∈ S) (hη : η ∈ T) :
    cfInner (νS ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ)
      (νT ⟨η, Submodule.subset_span hη⟩ : G → ℂ) = 0 := by
  classical
  have hUind : S ∪ T ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) :=
    Set.union_subset hSind hTind
  have hUirr : S ∪ T ⊆ Irr ↥L := Set.union_subset hSirr hTirr
  set τ := tiIndCharSpanZeroHom hTI hUind hUirr with hτdef
  have hz : ∀ f : charSpanZero (S ∪ T),
      (f : ↥L → ℂ) ∈ dadeZDomain L ((P : Set G) \ {1}) := fun f =>
    mem_dadeZDomain_of_mem_charSpanZero hUind hUirr f
  have hτ1 : ∀ f : charSpanZero (S ∪ T), (τ f : G → ℂ) 1 = 0 := by
    intro f
    rw [hτdef, coe_tiIndCharSpanZeroHom]
    exact hTI.indClassFun_apply_one (fun x hx => (mem_dadeZDomain.1 (hz f)).2 x hx)
  have hτiso : ∀ f g : charSpanZero (S ∪ T),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := by
    intro f g
    rw [hτdef, coe_tiIndCharSpanZeroHom, coe_tiIndCharSpanZeroHom]
    exact hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain (hz f))
      (mem_dadeDomain_of_mem_dadeZDomain (hz g))
  have hτstar : ∀ f : charSpanZero (S ∪ T),
      (τ (starCharSpanZero (star_mem_union hSstar hTstar) f) : G → ℂ)
        = star ((τ f : G → ℂ)) := by
    intro f
    rw [hτdef, coe_tiIndCharSpanZeroHom, coe_tiIndCharSpanZeroHom, coe_starCharSpanZero]
    exact DisjointCoherentFamilies.indClassFun_star _ _
  have hνS' : IsCoherentWith S (restrictBaseline Set.subset_union_left τ) νS := by
    refine ⟨hνS.inner_eq, fun f => Subtype.ext ?_⟩
    rw [hνS.eq_on_zero f, hτS f, restrictBaseline_apply, hτdef, coe_tiIndCharSpanZeroHom]
    simp
  have hνT' : IsCoherentWith T (restrictBaseline Set.subset_union_right τ) νT := by
    refine ⟨hνT.inner_eq, fun f => Subtype.ext ?_⟩
    rw [hνT.eq_on_zero f, hτT f, restrictBaseline_apply, hτdef, coe_tiIndCharSpanZeroHom]
    simp
  exact cfInner_apply_apply_eq_zero_of_disjoint hSirr hTirr hdisj hSne hTne hSstar hTstar
    hSnr hTnr hτ1 hτiso hτstar hνS' hνT' hξ hη

end General

namespace IsFreeCentralSection

variable {G : Type*} [Group G] [Fintype G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z) [Fintype ↥L]
  [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

include h

omit [Fintype G] in
theorem indFamDetect_subset_Irr :
    indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ⊆ Irr ↥L := by
  intro χ hχ
  rw [h.indFamDetect_eq_irrDetect] at hχ
  rw [← irrChar_eq_Irr]
  exact (mem_irrDetect.1 hχ).1

theorem exists_int_forall_resClassFun_indFamLinear_eq
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G))
    (hZP' : Z ≤ (⁅P, P⁆ : Subgroup G))
    {τX : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G}
    (hτX : ∀ f, (τX f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (νX : Submodule.span ℤ (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G)
    (hνX : IsCoherentWith (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) τX νX)
    {τY : charSpanZero (indFamLinear (P.subgroupOf L)) →+ virtualChars G}
    (hτY : ∀ f, (τY f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (νY : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G)
    (hνY : IsCoherentWith (indFamLinear (P.subgroupOf L)) τY νY) :
    ∃ lam : ℤ, ∃ Δ ∈ Submodule.span ℤ (irrTrivialOn (Z.subgroupOf L)),
      ∀ η, ∀ hη : η ∈ indFamLinear (P.subgroupOf L),
        resClassFun L (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ)
          = η + Δ + (lam : ℂ) • centralLayerWeightedChar (P.subgroupOf L)
              ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) (Nat.card E : ℂ) := by
  classical
  have hXIrr : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ⊆ Irr ↥L := h.indFamDetect_subset_Irr
  have hYIrr : indFamLinear (P.subgroupOf L) ⊆ Irr ↥L := h.indFamLinear_subset_Irr hCP
  have hXind : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) := by
    have hh := indFamDetect_subset_indFam_irrChar (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
    rwa [irrChar_eq_Irr] at hh
  have hYind : indFamLinear (P.subgroupOf L)
      ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) := indFamLinear_subset_indFam_Irr _
  have hdisj : Disjoint (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) (indFamLinear (P.subgroupOf L)) :=
    Set.disjoint_iff_inter_eq_empty.2 (h.inter_indFamDetect_indFamLinear_eq_empty' hZP')
  have hXne := h.indFamDetect_nonempty_subgroupOf
  have hYne := h.indFamLinear_nonempty'
  have hXstar : ∀ χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), star χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := fun χ hχ => h.conj_mem_indFamDetect hχ
  have hYstar : ∀ χ ∈ indFamLinear (P.subgroupOf L), star χ ∈ indFamLinear (P.subgroupOf L) :=
    fun χ hχ => NormalLinearInduced.conj_mem_indFamLinear _ hχ
  have hXnr : ∀ χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), star χ ≠ χ := fun χ hχ hc =>
    h.not_conj_eq_self_of_mem_indFamDetect hχ hc.symm
  have hYnr : ∀ χ ∈ indFamLinear (P.subgroupOf L), star χ ≠ χ := fun χ hχ hc =>
    h.not_conj_eq_self_of_mem_indFamLinear' hCP hχ hc.symm
  obtain ⟨η₀, hη₀⟩ := hYne
  have hψsigned : ((νY ⟨η₀, Submodule.subset_span hη₀⟩ : virtualChars G) : G → ℂ)
      ∈ signedIrr G := by
    refine mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
      (mem_span_Irr_of_mem_virtualChars (νY _).2) ?_
    rw [hνY.inner_eq]
    exact cfInner_self_of_mem_Irr (hYIrr hη₀)
  have horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      cfInner ((νY ⟨η₀, Submodule.subset_span hη₀⟩ : virtualChars G) : G → ℂ)
        (νX ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0 := by
    intro ξ hξ
    have hzero := cfInner_coherent_eq_zero_of_disjoint_tiInduced h.isTI hXind hYind hXIrr hYIrr
      hdisj ⟨ξ, hξ⟩ ⟨η₀, hη₀⟩ hXstar hYstar hXnr hYnr hτX hτY hνX hνY hξ hη₀
    have hc := congrArg (starRingEnd ℂ) hzero
    rw [conj_cfInner] at hc
    simpa using hc
  obtain ⟨lam, Ξ, hΞ, hdec, -⟩ :=
    h.exists_int_resClassFun_eq_add_zsmul_of_isCoherentWith τX hτX νX hνX hψsigned horth
  have hη₀triv : η₀ ∈ irrTrivialOn (Z.subgroupOf L) := by
    refine mem_irrTrivialOn.2 ⟨hYIrr hη₀, fun z hz => ?_⟩
    refine apply_eq_apply_one_of_mem_commutator (P.subgroupOf L) hη₀ ?_
    rw [commutator_subgroupOf_eq h.P_le]
    exact Subgroup.mem_subgroupOf.2 (hZP' (Subgroup.mem_subgroupOf.1 hz))
  refine ⟨lam, Ξ - η₀, sub_mem hΞ (Submodule.subset_span hη₀triv), fun η hη => ?_⟩
  have hmem : η - η₀ ∈ charSpanZero (indFamLinear (P.subgroupOf L)) := by
    refine mem_charSpanZero.2 ⟨sub_mem (Submodule.subset_span hη) (Submodule.subset_span hη₀), ?_⟩
    simp only [Pi.sub_apply]
    rw [h.apply_one_of_mem_indFamLinear hη, h.apply_one_of_mem_indFamLinear hη₀, sub_self]
  have hdiff : ((νY ⟨η, Submodule.subset_span hη⟩ : virtualChars G) : G → ℂ)
      - ((νY ⟨η₀, Submodule.subset_span hη₀⟩ : virtualChars G) : G → ℂ)
      = indClassFun L (η - η₀) := by
    have hsub : (⟨η, Submodule.subset_span hη⟩ :
          Submodule.span ℤ (indFamLinear (P.subgroupOf L)))
        - ⟨η₀, Submodule.subset_span hη₀⟩
        = Submodule.inclusion (charSpanZero_le _) ⟨η - η₀, hmem⟩ := Subtype.ext (by simp)
    have heq := hνY.eq_on_zero ⟨η - η₀, hmem⟩
    rw [← hsub, map_sub] at heq
    have h2 := congrArg (fun v : virtualChars G => (v : G → ℂ)) heq
    simpa [hτY ⟨η - η₀, hmem⟩] using h2
  have hz0 : (η - η₀) ∈ dadeZDomain L ((P : Set G) \ {1}) :=
    mem_dadeZDomain_of_mem_charSpanZero hYind hYIrr ⟨_, hmem⟩
  have hcf : IsClassFun (η - η₀) :=
    isClassFun_of_mem_classFun
      (sub_mem (Irr_subset_classFun (hYIrr hη)) (Irr_subset_classFun (hYIrr hη₀)))
  funext x
  have hval := h.indClassFun_restrict hcf (fun y hy => (mem_dadeZDomain.1 hz0).2 y hy) x
  have hpt := congrFun hdiff (x : G)
  simp only [Pi.sub_apply] at hpt
  rw [hval] at hpt
  simp only [Pi.sub_apply] at hpt
  have hdecpt := congrFun hdec x
  simp only [resClassFun_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hdecpt ⊢
  linear_combination hpt + hdecpt

theorem exists_int_forall_resClassFun_indFamLinear_eq_of_isCoherent
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G))
    (hZP' : Z ≤ (⁅P, P⁆ : Subgroup G))
    {τX : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G}
    (hτX : ∀ f, (τX f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (hcohX : IsCoherent (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) τX)
    {τY : charSpanZero (indFamLinear (P.subgroupOf L)) →+ virtualChars G}
    (hτY : ∀ f, (τY f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (νY : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G)
    (hνY : IsCoherentWith (indFamLinear (P.subgroupOf L)) τY νY) :
    ∃ lam : ℤ, ∃ Δ ∈ Submodule.span ℤ (irrTrivialOn (Z.subgroupOf L)),
      ∀ η, ∀ hη : η ∈ indFamLinear (P.subgroupOf L),
        resClassFun L (νY ⟨η, Submodule.subset_span hη⟩ : G → ℂ)
          = η + Δ + (lam : ℂ) • centralLayerWeightedChar (P.subgroupOf L)
              ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) (Nat.card E : ℂ) := by
  obtain ⟨νX, hνX⟩ := isCoherent_iff.1 hcohX
  exact h.exists_int_forall_resClassFun_indFamLinear_eq hCP hZP' hτX νX hνX hτY νY hνY

end IsFreeCentralSection

end CFSG.FeitThompson
