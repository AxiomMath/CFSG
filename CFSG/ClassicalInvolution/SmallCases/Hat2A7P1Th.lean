module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7P1Inst
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SStd
public import CFSG.ClassicalInvolution.Q3.Q3CLSeven2

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7P1

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3CL
  CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem thompsonCube_of_key (hP : PartIHypG8 Ω) (hkey : Sec7.KeyOn Ω) : CubeOn Ω := by
  intro W hW R hR T hT r hr t ht hrW htW
  have hΩ : HypOmegaGen Ω := hP.hyp
  have h62 := Sec6Gen.l6_2Gen
  have hkey' := hkey W hW
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  by_cases hKJ : K = J
  · left
    subst hKJ
    exact (Thompson.piG_comm_iff hrN htN).mp
      (Thompson.piG_comm_of_le hΩ hW hR hT (hkey' R hR T hT K hK hRK.1 hTJ.1) hr ht hrW htW)
  · by_cases hnbr : J ∈ omegaNbr Ω K
    · left
      exact (Thompson.piG_comm_iff hrN htN).mp
        (Thompson.piG_comm_of_mem_omegaNbr h62 hΩ hW (fun R hR T hT J hJ hRJ hTJ' =>
          hkey' R hR T hT J hJ hRJ hTJ') hK hJ hKJ hR hT hRK hTJ hnbr hr ht hrW)
    · right
      exact (Thompson.piG_cube_iff hrN htN).mp
        (Thompson.piG_cube_of_key h62 hΩ hW (fun R hR T hT J hJ hRJ hTJ' =>
          hkey' R hR T hT J hJ hRJ hTJ') (hP.aEmpty K hK) hK hJ hKJ hR hT hRK hTJ hnbr hr ht hrW
          htW)

theorem thompsonKey (hP : PartIHypG8 Ω) : Sec7.KeyOn Ω := Sec7.l7_1Key hP

theorem thompsonCube (hP : PartIHypG8 Ω) : CubeOn Ω := thompsonCube_of_key hP (thompsonKey hP)

namespace T8

open CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.GH74.Uniqueness
  CFSG.StronglyEmbedded.UniqueCoset

theorem ctxOf (hP : PartIHypG8 Ω) (hW : W ∈ WSet Ω) : Thompson.Ctx Ω W :=
  ⟨hP.hyp, hW, thompsonKey hP W hW, hP.aEmpty⟩

@[expose] noncomputable def mkRep (hP : PartIHypG8 Ω) (hW : W ∈ WSet Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K) : Rep Ω W :=
  have h := Thompson.exists_not_mem_of_mem_D hP.hyp hW hR
  ⟨K, R, h.choose, hK, hR, hRK, h.choose_spec.1, h.choose_spec.2⟩

end T8

theorem partIHypG8_of_members
    (hΩ : HypOmegaGen Ω) (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z)
    (hA : ∀ J ∈ Ω, AEmpty Ω J) : PartIHypG8 Ω where
  hyp := hΩ
  cls := classicalClause8_of_members fun J hJ => by
    obtain ⟨z, hz⟩ := hcl J hJ
    exact ⟨z, IsClassicalMemberU.of2A7 hz⟩
  aEmpty := hA

end CFSG.ClassicalInvolution.Hat2A7P1

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.ClassicalInvolution.Hat2A7P1

theorem partIHypG8_of_std2A7 {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {K : Subgroup G}
    (h : Std2A7 Ω K) : PartIHypG8 Ω :=
  partIHypG8_of_members h.hyp h.classical h.aEmpty

end CFSG.ClassicalInvolution.Hat2A7S
