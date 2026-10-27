module

public import CFSG.ClassicalInvolution.Asc77.AscC25J14b
public import CFSG.ClassicalInvolution.Asc77.AscR10QV

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Restrict

variable {H : Type} [Group H] [Finite H] {Λ : Set (Subgroup H)}


theorem omegaNbr_subgroupOf_gen (hΩ : HypOmegaGen Λ) {Y K J : Subgroup H} (hKY : K ≤ Y)
    (hJY : J ≤ Y) (hJ : J ∈ Λ) (h : J ∈ omegaNbr Λ K) :
    J.subgroupOf Y ∈ omegaNbr (restrictFamily Λ Y) (K.subgroupOf Y) := by
  obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ hT hTJ
  refine ⟨subgroupOf_mem_restrictFamily hJ hJY, subgroupOf_ne_of_ne hKY hJY hne, T.subgroupOf Y,
    mem_RSet_restrict hJ hJY hTsyl, Subgroup.subgroupOf_mono Y hTJ, fun x hx => ?_⟩
  exact (mem_normalizer_subgroupOf_iff hKY).mp (hTN (Subgroup.mem_subgroupOf.mp hx))

theorem aEmpty_restrict_gen (hΩ : HypOmegaGen Λ) {Y K : Subgroup H} (hKY : K ≤ Y)
    (hA : AEmpty Λ K) : AEmpty (restrictFamily Λ Y) (K.subgroupOf Y) := by
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  set J : Subgroup H := J'.map Y.subtype with hJdef
  have hJ'eq : J.subgroupOf Y = J' := subgroupOf_map_subtype' J'
  have hJY : J ≤ Y := Subgroup.map_subtype_le J'
  have hJ : J ∈ Λ := mem_restrictFamily_iff.mp hJ'star.1
  have hstar : J ∈ omegaStarNbr Λ K :=
    omegaStarNbr_of_restrict hKY hJY (by rwa [hJ'eq])
  have hnbr : J ∉ omegaNbr Λ K := fun h =>
    hJ'nbr (by rw [← hJ'eq]; exact omegaNbr_subgroupOf_gen hΩ hKY hJY hJ h)
  have hzK : IsUniqueInvolution K (zK' : H) := isUniqueInvolution_of_subgroupOf hzK' hKY
  have hzJ : IsUniqueInvolution J (zJ' : H) :=
    isUniqueInvolution_of_subgroupOf (by rwa [hJ'eq]) hJY
  obtain ⟨g, hg, hgK⟩ := hA J hstar hnbr _ _ hzK hzJ
  set Z' : Subgroup Y := Subgroup.closure ({zK', zJ'} : Set Y) with hZ'
  have hZ : Z'.map Y.subtype = Subgroup.closure ({(zK' : H), (zJ' : H)} : Set H) :=
    map_closure_pair_subtype zK' zJ'
  have hZY : Subgroup.closure ({(zK' : H), (zJ' : H)} : Set H) ≤ Y := by
    rw [← hZ]; exact Subgroup.map_subtype_le _
  have hgY : g ∈ Y := by
    have : pairNormalizers K J (zK' : H) (zJ' : H) ≤ Y := by
      unfold pairNormalizers
      exact sup_le (inf_le_left.trans hKY) (inf_le_left.trans hJY)
    exact this hg
  have hN : ∀ {A : Subgroup H}, A ≤ Y →
      (A ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : H), (zJ' : H)} : Set H) :
        Subgroup H) : Set H)).subgroupOf Y ≤
        A.subgroupOf Y ⊓ Subgroup.normalizer ((Z' : Subgroup Y) : Set Y) := by
    intro A hAY x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hx.1, ?_⟩
    have := (mem_normalizer_subgroupOf_iff hZY).mp hx.2
    rwa [← hZ, subgroupOf_map_subtype'] at this
  have hAY : K ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : H), (zJ' : H)} : Set H) :
      Subgroup H) : Set H) ≤ Y := inf_le_left.trans hKY
  have hBY : J ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : H), (zJ' : H)} : Set H) :
      Subgroup H) : Set H) ≤ Y := inf_le_left.trans hJY
  have hmem : (⟨g, hgY⟩ : Y) ∈ (pairNormalizers K J (zK' : H) (zJ' : H)).subgroupOf Y :=
    Subgroup.mem_subgroupOf.mpr hg
  have hmem' : (⟨g, hgY⟩ : Y) ∈ pairNormalizers (K.subgroupOf Y) J' zK' zJ' := by
    have h1 := hmem
    unfold pairNormalizers at h1
    rw [Subgroup.subgroupOf_sup hAY hBY] at h1
    have h2 := hN (A := K) hKY
    have h3 := hN (A := J) hJY
    rw [hJ'eq] at h3
    exact sup_le_sup h2 h3 h1
  refine ⟨⟨g, hgY⟩, hmem', ?_⟩
  rw [conjSub_subgroupOf Y ⟨g, hgY⟩ K]
  show (conjSub g K).subgroupOf Y = J'
  rw [hgK]
  exact hJ'eq

end Restrict

section Sec

variable {Y₀ : Type} [Group Y₀] [Finite Y₀]


theorem aEmpty_secFamily {L : Subgroup Y₀} (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily L))
    (hA : ∀ M ∈ conjFamily L, AEmpty (conjFamily L) M) :
    ∀ M ∈ oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L)),
      AEmpty (oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L))) M := by
  set X := conjGen L with hX
  have hΩg : HypOmegaGen (conjFamily L) := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaModU (.sl2 3 1) (restrictFamily (conjFamily L) X) :=
    hypOmegaModU_restrict hΛ X
  have hΛ₁g : HypOmegaGen (restrictFamily (conjFamily L) X) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ₁
  have hΛ' : HypOmegaGen
      (quotFamily (restrictFamily (conjFamily L) X) (classicalInvolutionOddCore ↥X)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (hypOmegaModU_oddQuotientFamily hΛ₁)
  have hΛA : ∀ M ∈ restrictFamily (conjFamily L) X,
      AEmpty (restrictFamily (conjFamily L) X) M := by
    rintro _ ⟨M, hM, hMY, rfl⟩
    exact aEmpty_restrict_gen hΩg hMY (hA M hM)
  exact aEmpty_quotFamily_gen hΛ₁g hΛ' hN₀odd hΛA

end Sec

end CFSG.ClassicalInvolution.Asc77.C25J
