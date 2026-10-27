module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSO
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.GH74.GLS.Stage2.Final.ClassicalClosed
public import CFSG.RankThree.OddKernel.OddLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_core (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (h52a : Asc82Lemma52a) (hM1 : Asc82FactRhoStar) (h38 : Asc82Lemma38)
    (h311 : Asc82Lemma311) (h7 : AschOmega7)
    (hOne : CFSG.GH74.GLS.Stage2.Final.ModelOneClass)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {i i' j j' : Fin 4}
    (hi : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0)) (hj : (j = 2 ∧ j' = 3) ∨ (j = 3 ∧ j' = 2))
    {α β : G} (hα : α ∈ Kfam5 K₁ K₂ h i) (hβ : β ∈ Kfam5 K₁ K₂ h j) (hα2 : α * α = z)
    (hβ2 : β * β = z) (hdt : (α * β) * t = t * (α * β))
    (hds : (α * β) * (h⁻¹ * t * h) = (h⁻¹ * t * h) * (α * β)) (hβt : β * t = t * β)
    (hαs : α * (h⁻¹ * t * h) = (h⁻¹ * t * h) * α) :
    ∃ I : Subgroup G, IsComponentIn I (centralizer ({α * β} : Set G)) ∧ InF I ∧
      IsTwoU43 (I ⧸ oddCore I) ∧ Kfam5 K₁ K₂ h i' ≤ I ∧ Kfam5 K₁ K₂ h j' ≤ I := by
  obtain ⟨I, hI, -, hpk, hi'I, hj'I, hM₁, hE₁I, -, -⟩ :=
    l515S_reduced h36 h37 h514 h52a hM1 c hi hj hα hβ hα2 hβ2 hdt hds hβt hαs
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  obtain ⟨hij, -, -, hi'j', -, -⟩ := l515S_idx hi hj
  obtain ⟨hd2', hd1, -⟩ := hq.mul_invol hij hα hβ hα2 hβ2
  have hd2 : orderOf (α * β) = 2 := l515S_orderOf_eq_two hd2' hd1
  have hIq : IsQuasisimple I := hI.isQuasisimple
  have hdvd : 6048 ∣ ctrQ I := by
    have := ctrQ_dvd_of_le hE₁I
    rwa [l515S_ctrQ_of_u33 hM₁] at this
  have hInF : InF I := by
    by_contra hnot
    have hL3 : IsL3Eps3 I := hpk.resolve_left hnot
    have hc : ctrQ I = 6048 := by
      rcases ctrQ_mem_of_isL3Eps3 hIq hL3 with h5616 | h6048
      · rw [h5616] at hdvd
        omega
      · exact h6048
    have hEI : layerCent L (α * β) = I :=
      eq_of_le_of_ctrQ_eq hIq hE₁I (by rw [hc, l515S_ctrQ_of_u33 hM₁])
    have h0 : layerCent L (α * β) ≤ L ⊓ centralizer ({α * β} : Set G) := inSubgroup_le _ _
    have hIL : I ≤ L := by
      calc I = layerCent L (α * β) := hEI.symm
        _ ≤ L := h0.trans inf_le_left
    have hj'23 : j' = 2 ∨ j' = 3 := by
      rcases hj with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
    exact l515S_pocket_not_le_L h514 c hj'23 (hj'I.trans hIL)
  have hSet : Sec3SettingLB G (α * β) I :=
    ⟨⟨c.simple, c.a1, c.a2, c.notChev3, hd2, hI, hInF⟩, c.lBalance, c.kProper, c.notCat⟩
  refine ⟨I, hI, hInF, ?_, hi'I, hj'I⟩
  have hF' : IsQuasisimple I ∧
      (SmallF3OmegaQuotient (I ⧸ oddCore I) ∨ IsTwoU43 (I ⧸ oddCore I)) := hInF
  rcases hF'.2 with hO | hT
  · exfalso
    unfold SmallF3OmegaQuotient at hO
    rcases hO with h5 | h43 | hu43 | h7m | h8p | h8m
    · rw [ctrQ_of_psp4 hIq h5] at hdvd
      omega
    · rw [ctrQ_of_l43 hIq h43] at hdvd
      omega
    ·
      obtain ⟨a', ha', ha'2⟩ := hq.exists_sq i'
      obtain ⟨b', hb', hb'2⟩ := hq.exists_sq j'
      obtain ⟨he2, he1, -⟩ := hq.mul_invol hi'j' ha' hb' ha'2 hb'2
      have hzI : z ∈ I := hi'I (hq.z_mem i')
      have heI : a' * b' ∈ I := I.mul_mem (hi'I ha') (hj'I hb')
      have hz2 : orderOf z = 2 := l515S_orderOf_eq_two hq.z_sq hq.z_ne
      have he2' : orderOf (a' * b') = 2 := l515S_orderOf_eq_two he2 he1
      have hone := hOne (↥I ⧸ oddCore ↥I) 3 1 Nat.prime_three (by norm_num)
        (Or.inr ⟨by norm_num, hu43⟩)
      have hconj : IsConj (⟨z, hzI⟩ : ↥I) ⟨a' * b', heI⟩ :=
        CFSG.RankThree.OddKernel.isConj_of_isConj_quotient (oddCore ↥I)
          (CFSG.ABGLocalTools.odd_card_oddCore (H := ↥I)) hone
          (by rw [Subgroup.orderOf_mk]; exact hz2) (by rw [Subgroup.orderOf_mk]; exact he2')
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hu' : (u : G) * z * (u : G)⁻¹ = a' * b' := by
        simpa using congrArg Subtype.val hu
      refine l515S_z_not_conj_mixed h36 h37 h514 h52a hM1 c (i := i') (i' := i) (j := j')
        (j' := j) ?_ ?_ ha' hb' ha'2 hb'2 (u : G)⁻¹ ?_
      · rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
        exacts [Or.inr ⟨h2, h1⟩, Or.inl ⟨h2, h1⟩]
      · rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        exacts [Or.inr ⟨h2, h1⟩, Or.inl ⟨h2, h1⟩]
      · rw [inv_inv]
        exact hu'
    · exact h7 G (α * β) I hSet h7m
    · exact h311 G (α * β) I hSet h8p
    · exact h38 G (α * β) I hSet h8m
  · exact hT

end CFSG.OddStandard.SmallF3.Omega
