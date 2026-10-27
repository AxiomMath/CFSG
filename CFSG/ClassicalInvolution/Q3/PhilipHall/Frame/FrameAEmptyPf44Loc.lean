module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf20OmegaA
public import CFSG.ClassicalInvolution.Asc77.AscAETSecViol

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge.Fam
open scoped commutatorElement

section Loc

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem tightCore_inf_subgroupOf_mem_omegaAFam {X P R : Subgroup G} (hP : P ∈ Ω)
    (hR : IsSylow2In R P) (hRX : R ≤ X) :
    (tightCore (P ⊓ X)).subgroupOf X ∈ omegaAFam Ω X := by
  exact ⟨tightCore (P ⊓ X), ⟨P, hP, ⟨R, hR, hRX⟩, rfl⟩, (tightCore_le _).trans inf_le_right, rfl⟩

theorem exists_of_mem_omegaAFam {X : Subgroup G} {Q' : Subgroup ↥X} (h : Q' ∈ omegaAFam Ω X) :
    ∃ P ∈ Ω, (∃ R : Subgroup G, IsSylow2In R P ∧ R ≤ X) ∧
      Q' = (tightCore (P ⊓ X)).subgroupOf X := by
  obtain ⟨_, ⟨P, hP, hR, rfl⟩, -, rfl⟩ := h
  exact ⟨P, hP, hR, rfl⟩

theorem member_eq_of_le (hΩ : HypOmegaGen Ω) {P Q : Subgroup G} (hP : P ∈ Ω) (hQ : Q ∈ Ω)
    (hPQ : P ≤ Q) : P = Q := by
  obtain ⟨R, hR, hRP, -⟩ := exists_mem_RSet_ge hP (isPGroup_two_bot' (G := G)) bot_le
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  exact Sec6Gen.eq_of_le_of_le hΩ hP hQ hRP.2.1 (by omega) hRP.1 (hRP.1.trans hPQ)

theorem eq_of_tightCore_inf_le (hΩ : HypOmegaGen Ω) {X P Q R : Subgroup G} (hP : P ∈ Ω)
    (hQ : Q ∈ Ω) (hR : IsSylow2In R P) (hRX : R ≤ X) (h : tightCore (P ⊓ X) ≤ Q) : P = Q := by
  have hRc : R ≤ tightCore (P ⊓ X) := le_tightCore_of_isPGroup (le_inf hR.1 hRX) hR.2.1
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hP hR)
  exact Sec6Gen.eq_of_le_of_le hΩ hP hQ hR.2.1 (by omega) hR.1 (hRc.trans h)

omit [Finite G] in
theorem tightCore_inf_eq_of_le {X P : Subgroup G} (hcore : tightCore P = P) (hPX : P ≤ X) :
    tightCore (P ⊓ X) = P := by
  rw [inf_eq_left.mpr hPX, hcore]

theorem subgroupOf_mem_omegaAFam {X P : Subgroup G} (hP : P ∈ Ω) (hcore : tightCore P = P)
    (hPX : P ≤ X) : P.subgroupOf X ∈ omegaAFam Ω X := by
  obtain ⟨R, -, hRP, -⟩ := exists_mem_RSet_ge hP (isPGroup_two_bot' (G := G)) bot_le
  have h := tightCore_inf_subgroupOf_mem_omegaAFam hP hRP (hRP.1.trans hPX)
  rwa [tightCore_inf_eq_of_le hcore hPX] at h

omit [Finite G] in
theorem tightCore_eq_of_mem_conjClass {K : Subgroup G} {t : G} (hD : FrameTightDatum K t)
    {P : Subgroup G} (hP : P ∈ CoreAssembly.conjClass K) : tightCore P = P := by
  obtain ⟨g, rfl⟩ := hP
  show tightCore (conjSub g K) = conjSub g K
  rw [← conjSub_tightCore, hD.tightCore_eq]

theorem aViol_omegaAFam_of_le (hΩ : HypOmegaGen Ω) (hcore : ∀ P ∈ Ω, tightCore P = P)
    {X L J : Subgroup G} {zL zJ : G} (hL : L ∈ Ω) (hLX : L ≤ X) (hJX : J ≤ X)
    (hv : AViol Ω L J zL zJ) :
    AViol (omegaAFam Ω X) (L.subgroupOf X) (J.subgroupOf X) ⟨zL, hLX hv.hzK.mem⟩
      ⟨zJ, hJX hv.hzJ.mem⟩ := by
  have hJΩ : J ∈ Ω := hv.mem
  have hΛ : HypOmegaGen (omegaAFam Ω X) := hypOmegaGen_omegaAFam hΩ X
  have hJmem0 : J ∈ omegaACore Ω X := by
    obtain ⟨R, -, hRJ, -⟩ := exists_mem_RSet_ge hJΩ (isPGroup_two_bot' (G := G)) bot_le
    exact ⟨J, hJΩ, ⟨R, hRJ, hRJ.1.trans hJX⟩, (tightCore_inf_eq_of_le (hcore J hJΩ) hJX).symm⟩
  have hJmem : J.subgroupOf X ∈ omegaAFam Ω X := subgroupOf_mem_restrictFamily hJmem0 hJX
  have hstar : J.subgroupOf X ∈ omegaStarNbr (omegaAFam Ω X) (L.subgroupOf X) := by
    obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := hv.star
    obtain ⟨R, -, J₁, hJ₁, hRJ₁, hUR, hcyc, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
    have hJ₁J : J₁ = J := Sec6Gen.eq_of_mem_USet hΩ hU hJ₁ hJΩ (hUR.trans hRJ₁.1) hUJ
    rw [hJ₁J] at hRJ₁
    refine ⟨hJmem, subgroupOf_ne_of_ne hLX hJX hne, U.subgroupOf X,
      AscAET.mem_USet_restrict_of_sylow hJmem0 hJX hRJ₁ hUR hcyc
        (AscAET.relIndex_eq_two_of_card hUR hcard), Subgroup.subgroupOf_mono X hUJ, ?_⟩
    intro u hu
    exact (mem_normalizer_subgroupOf_iff hLX).mp (hUN (Subgroup.mem_subgroupOf.mp hu))
  have hnbr : J.subgroupOf X ∉ omegaNbr (omegaAFam Ω X) (L.subgroupOf X) := by
    rintro ⟨-, -, R', hR', hR'J, hR'N⟩
    have hR'syl : IsSylow2In R' (J.subgroupOf X) :=
      Sec6Gen.isSylow2In_of_mem_RSet_of_le hΛ hJmem hR' hR'J
    have hmap : IsSylow2In (R'.map X.subtype) J := by
      have h1 := isSylow2In_map_subtype_iff.mpr hR'syl
      rwa [Subgroup.map_subgroupOf_eq_of_le hJX] at h1
    have hRN : R'.map X.subtype ≤ Subgroup.normalizer (L : Set G) := by
      have h1 := Asc77.map_le_normalizer_map hR'N
      rwa [Subgroup.map_subgroupOf_eq_of_le hLX] at h1
    exact hv.not_nbr ⟨hJΩ, hv.ne, _, mem_RSet_of_isSylow2In hJΩ hmap, hmap.1, hRN⟩
  refine ⟨hstar, hnbr, isUniqueInvolution_subgroupOf hv.hzK hLX,
    isUniqueInvolution_subgroupOf hv.hzJ hJX, ?_⟩
  intro g hg hcon
  have hmem : (g : G) ∈ pairNormalizers L J zL zJ :=
    map_pairNormalizers_subgroupOf_le hLX hJX ⟨zL, hLX hv.hzK.mem⟩ ⟨zJ, hJX hv.hzJ.mem⟩
      (Subgroup.mem_map_of_mem X.subtype hg)
  have h1 : conjSub (g : G) L ≤ X := by
    have := conjSub_mono (n := (g : G)) hLX
    rwa [conjSub_eq_self_of_mem g.2] at this
  have hconj : conjSub (g : G) L = J := by
    rw [conjSub_subgroupOf X g L] at hcon
    have := Subgroup.subgroupOf_inj.mp hcon
    rwa [inf_eq_left.mpr h1, inf_eq_left.mpr hJX] at this
  exact hv.no_conj _ hmem hconj

end Loc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
