module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageMChain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootFivePerm
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageFPartner

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv AltStdBal AltStdSec CFSG.ComponentClassification.RestrictedStd.Spor

namespace StageM

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem caseIIIAt_of_fusionAll (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (c : StageF.Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n)) (hF : FusionAll L z)
    {S : Finset (Fin n)} (hS : S.card = 3) : CaseIIIAt e z S := by
  have hn := c.hn
  have hm : 9 ≤ n - S.card := by omega
  have hRD := c.rootData hlookup hHN hOut hFour e (Or.inl hS) hm
  rcases c.zstar_or_wreath_of_rootData hlookup hHN hFour (corr_le e (altSub S))
      (corr_le e (altSub Sᶜ)) hRD hm (exists_ne_one_of_card_ge_three e (by omega)) with hz | hW
  swap
  · exact ⟨hRD.hz, hW⟩
  exfalso
  obtain ⟨b', hb'2, hb'sign, hb'1, hb'S, hb'card⟩ :=
    rootFive_exists_involution_gen (S := S) (by omega)
  have hb'A : b' ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 hb'sign
  set y : G := ((e.symm ⟨b', hb'A⟩ : L) : G) with hy
  have hyL : y ∈ L := (e.symm ⟨b', hb'A⟩).2
  have heb : e ⟨y, hyL⟩ = ⟨b', hb'A⟩ := by
    have : (⟨y, hyL⟩ : L) = e.symm ⟨b', hb'A⟩ := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hb'ord : orderOf b' = 2 := orderOf_eq_prime (by rw [sq]; exact hb'2) hb'1
  have hy2 : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hb'ord
  obtain ⟨g, hg⟩ := hF y hyL hy2
  have hyY : y ∈ FusionSet L z := ⟨hyL, hy2, g, hg⟩
  have hfS : ∀ i ∈ S, ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i := by
    rw [heb]
    exact hb'S
  have hcardF : n - 4 ≤ (fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card := by
    rw [heb]
    exact hb'card
  obtain ⟨S₁, hS₁c, hS₁⟩ := c.exists_common_root_of_fix e hyL hy2 hg (by omega) (by omega) hfS
  have hz₁ : IsZStar (rootGroup e S₁) z :=
    (c.isZStar_rootGroup_iff e hS₁c.symm (by omega)).1 hz
  exact c.false_of_zstar_common_root hlookup hHN hOut hFour e hyY hg (Or.inl hS)
    (mem_centralizer_rootGroup_of_fix e hyL hfS) hS₁ hz hz₁

theorem wreathPair_of_caseIII (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (c : StageF.Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)}
    (hS₀ : S₀.card = 3) (hIII : CaseIIIAt e z S₀) : ∃ M : Subgroup G, WreathPair L z n M := by
  have hn := c.hn
  exact exists_wreathPair_of_caseIII_root_w (weakShape_of_cyc c.std.standard e c.cyc c.card) e
    (by omega) (fun S hS => c.rootData hlookup hHN hOut hFour e (Or.inl hS) (by omega)) hS₀ hIII

end StageM

theorem cycTwoInnerStageM_of_inputs (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : FourExactOuterInput) : CycTwoInnerStageM := by
  intro G _ _ L Q n θ z h hn hE hF
  have c : StageF.Inner G L Q n z := ⟨h.std, hn, ⟨θ⟩, h.cyc, h.card, hE⟩
  obtain ⟨S₀, -, hS₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := 3) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  exact StageM.wreathPair_of_caseIII hlookup hHN hOut hFour c θ hS₀
    (StageM.caseIIIAt_of_fusionAll hlookup hHN hOut hFour c θ hF hS₀)

end CFSG.OddStandard.AltStdCycTwo
