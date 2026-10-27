module

public import CFSG.ClassicalInvolution.Q3.Q3CHSec
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77

section Anchor

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {c b : G} {B : Subgroup G}

theorem hyp51At_of_secComp {ι : Type} (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c}) (centralizingLayer Φ {c}))))
    (j : ι) (hB : CFSG.Open.IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (hbj : oddQuotMk c ⟨b, hbC⟩ ∈ secComp hΦ D j)
    (hcase : CFSG.IsComponent (secComp hΦ D j) → MovedByAll B c (secComp hΦ D j) →
      alphaOf (inducedImage (secComp hΦ D j) (modOdd c B)) = ⊥) :
    Asc77.Hyp51At B c := by
  refine ⟨fun L L' hL hL' hm hm' => ?_, fun L hL hm => ?_⟩
  · exact (eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC hbj hL hm).trans
      (eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC hbj hL' hm').symm
  · have hLj := eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC hbj hL hm
    subst hLj
    exact hcase hL hm

theorem not_movedByAll_of_centralizes (hB : CFSG.Open.IsElemAbelian 2 B) (hcB : c ∈ B)
    (hc1 : c ≠ 1) (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) {L : Subgroup (OddQuot c)}
    (hcomm : ∀ y ∈ L, oddQuotMk c ⟨b, hbC⟩ * y = y * oddQuotMk c ⟨b, hbC⟩) :
    ¬ MovedByAll B c L := by
  intro hmov
  obtain ⟨y, hyL, hy⟩ := hmov _ (oddQuotMk_mem_modOdd hbB hbC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC)
  exact hy (hcomm y hyL)

theorem alphaOf_inducedImage_eq_bot_of_rows (hB : CFSG.Open.IsElemAbelian 2 B)
    {L : Subgroup (OddQuot c)} (P : MulAut ↥L → Prop) (hrow : AutOddFreeOn ↥L P)
    (hne : ∃ x ∈ inducedImage L (modOdd c B), x ≠ 1)
    (hP : ∀ x ∈ inducedImage L (modOdd c B), x ≠ 1 →
      P ((x : ↥(inducedAutOn L)) : MulAut ↥L)) :
    alphaOf (inducedImage L (modOdd c B)) = ⊥ := by
  refine alphaOf_eq_bot_of_on L P hrow _ ?_ hne hP
  rintro _ ⟨w, hw, rfl⟩
  have hww : w * w = 1 := by
    apply Subtype.ext
    obtain ⟨k, hkB, hk⟩ := hw
    have hk' : oddQuotMk c k = (w : OddQuot c) := hk
    have hkk : k * k = 1 := Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB hkB)
    show (w : OddQuot c) * w = 1
    rw [← hk', ← map_mul, hkk, map_one]
  rw [← map_mul, hww, map_one]

end Anchor

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
