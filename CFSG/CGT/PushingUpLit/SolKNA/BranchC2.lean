module

public import CFSG.CGT.PushingUpLit.SolKNA.RevPairOf
public import CFSG.CGT.PushingUpLit.SolKNA.Lemma18Final

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolKAb
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.Assembly (pCoreOf)
open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

section Certified


theorem caseII4_false (hSz : Lemma18SzAbelian) {K R T : Subgroup G} {g : G}
    (cfg : NAConfig G K R T g) (h4 : CaseII4 K R T) : False := by
  have hKR : K = R := cfg.eq_of_caseII4 h4
  have cfg' : NAConfig G R R T g := hKR ▸ cfg
  have h4' : CaseII4 R R T := hKR ▸ h4
  have hR2 : IsPGroup 2 R := cfg'.sylowR.isPGroup
  have hRpc : R ≤ pCoreOf 2 R := le_pCoreOf_of_normal le_rfl hR2 Subgroup.le_normalizer
  have hTI : IsTI R := isTI_of_normal_le_pCoreOf cfg'.stSetting.tight hRpc le_rfl
  have hg : g ∉ Subgroup.normalizer (R : Set G) := cfg'.g_not
  have hR'2 : IsPGroup 2 (rightConjugate R g) := hR2.map (MulAut.conj g⁻¹).toMonoidHom
  have hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G) :=
    (cfg'.sylowT.eq_of_le cfg'.sylowT.le le_rfl (hR'2.to_le inf_le_left)).symm
  have hcardN : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T :=
    Nat.card_congr h4'.iso.some.toEquiv
  have hle : Nat.card ↥R ≤ Nat.card ↥T ^ 2 := by
    have h1 := Subgroup.relIndex_mul_card (R ⊓ Subgroup.normalizer (T : Set G)) R
    rw [inf_of_le_left (inf_le_left : R ⊓ Subgroup.normalizer (T : Set G) ≤ R)] at h1
    calc Nat.card ↥R = (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R *
          Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) := h1.symm
      _ ≤ Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) *
          Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) :=
        Nat.mul_le_mul_right _ h4'.relIndex_le
      _ = Nat.card ↥T ^ 2 := by rw [hcardN, sq]
  have hrev : RevPair R g :=
    revPair_of_pair hR2 hTI hg hT cfg'.T_ne (isCommSubgroup_of_isElemAbelian h4'.elem_T)
      cfg'.not_isCyclic cfg'.isTI_T h4'.elem_N h4'.iso cfg'.T_lt hle
  have hinf : R ⊓ conjSubgroup g⁻¹ R = ⊥ := inf_rightConjugate_eq_bot hTI hg
  have hLN := inf_normalizer_rightConjugate_eq hTI hg hT cfg'.T_ne
  obtain ⟨hNnorm, hΦb₁, hΦb₂, hTZ⟩ := hrev.lemma18_data hR2 hT hLN
  have hT2 : ∀ x ∈ T, x * x = 1 := fun x hx => by
    have := h4'.elem_T.2 x hx
    rwa [sq] at this
  have hCR : R ⊓ Subgroup.normalizer (T : Set G) ≠ R := by
    intro h
    have := h4'.one_lt_relIndex
    rw [h, Subgroup.relIndex_self] at this
    exact lt_irrefl _ this
  have hab := lemma18_abelian_final hSz (g := g⁻¹) (Z := ⊤) (Subgroup.mem_top _) le_top hR2
    (isTIIn_of_isTI hTI) (T := T) (C := R ⊓ Subgroup.normalizer (T : Set G))
    (N := (R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T) hT cfg'.T_ne hinf cfg'.inf_normalizer_eq
    h4'.sq_mem h4'.comm_mem h4'.central h4'.iso hT2 hCR rfl hNnorm hΦb₁ hΦb₂ hTZ
  exact cfg'.noncomm hab

end Certified

end CFSG.CGT.PushingUpLit.SolKNA
