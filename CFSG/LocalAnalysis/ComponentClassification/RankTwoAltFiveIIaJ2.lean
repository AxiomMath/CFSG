module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIa
public import CFSG.Quasithin.Recognition.J2RecFiveQuot
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveTypeH2

public section

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G]
variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem nonempty_mulEquiv_j2_of_eps_one'
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨S, hPS⟩ := hP.isPGroup.exists_le_sylow
  obtain ⟨z, Q, hQ⟩ := h.exists_QFacts_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e
    hV'16 hinf hsup hV'inv S hPS
  have hz := h.isTypeH2_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup
    hV'inv S hPS hQ
  have hcount := h.involutionClassCount_eq_two_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv
  obtain ⟨y, hy, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hIIa
  have hV₀A : V₀ ≤ A := h.loc.inf_A ▸ inf_le_right
  have hconf : CFSG.Quasithin.J2A5Config z A R y :=
    { equiv := h.equiv
      z_mem := hV₀A hQ.z_mem_V₀
      le_centralizer := h.sylowR.le
      card := h.cardR
      mul_self := fun r hr => h.mul_self (mem_sup_left hr)
      not_isConj := fun r hr hr1 => h.not_isConj_of_mem_R hQ.z_mem_V₀ hQ.z_ne_one hr hr1
      y_mem := (mem_inf.mp hy).1
      y_normalizes := (mem_inf.mp hy).2
      y_not_mem := hyC }
  exact hconf.nonempty_mulEquiv_J2 hz hcount

end IIa

end PStructure

end Setting310

theorem asc310IIa_of' (hε : Asc310EpsOne) :
    Asc310IIa := by
  intro G _ _ A R g T V₀ h hX hIIa
  have hGs := h.isSimpleGroup_of_rankTwoX_eq_top hX
  obtain ⟨P, hP, hVP, hPC, hP64⟩ := h.exists_sylow_transv
  obtain ⟨V', hV'P, hV'e, hV'16, hinf, hsup, hV'inv, -⟩ := h.exists_Vprime hP hPC hIIa hP64 hVP
  obtain ⟨e⟩ := h.nonempty_mulEquiv_j2_of_eps_one' hP hPC hIIa Asc76X.goldschmidtTheoremA hGs
    hP64 hVP (hε G A R g T V₀ h hX hGs hIIa P hP hVP hPC hP64) hV'P hV'e hV'16 hinf hsup hV'inv
  rw [hX]
  exact ⟨Subgroup.topEquiv.trans e⟩

end CFSG.ComponentClassification.RankTwoAltFive
