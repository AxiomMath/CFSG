module

public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem dsA_caseI_of_leaves (hNF : LeafDSANoField) (hZS : LeafZiStructure) (hS3 : LeafDSACaseIIStep3)
    (hS4 : LeafDSACaseIIStep4) {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G}
    (h : DSAHyp L1 L2 S) : ⁅dsZi L1 S, L1⁆ ≠ ⊥ ∧ ⁅dsZi L2 S, L2⁆ ≠ ⊥ := by
  have h' : DSAHyp L2 L1 S := h.symm
  by_cases c1 : ⁅dsZi L1 S, L1⁆ = ⊥ <;> by_cases c2 : ⁅dsZi L2 S, L2⁆ = ⊥
  ·
    exfalso
    have hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := (hNF h).2.2
    have zs1 : ZSetting L1 L2 S := ⟨h.hyp, hB⟩
    have zs2 : ZSetting L2 L1 S := zs1.symm
    obtain ⟨hne, -, -, -, -, hn1, -⟩ := hZS zs1
    obtain ⟨-, -, -, -, -, hn2, -⟩ := hZS zs2
    rw [dsZi_eq_dsZ_of_commutator_eq_bot c1] at hn1
    rw [dsZi_eq_dsZ_of_commutator_eq_bot c2, bigB_comm] at hn2
    have hZS' : dsZ S ≤ S := by
      have : centerOf S ≤ S := by unfold centerOf; exact inf_le_left
      exact (dsZ_le_center S).trans this
    have hp : IsPGroup 2 (dsZ S) := h.hyp.hyp.h1.pgroup.to_le hZS'
    have hSN : S ≤ Subgroup.normalizer (dsZ S : Set G) :=
      (le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right.trans hn1)
    exact hne (coreFree h.hyp.hyp hp (hZS'.trans le_sup_right) (le_sup_left.trans hn1)
      (le_sup_left.trans hn2) hSN)
  ·
    exfalso
    exact hS4 h' c1 c2 (hS3 h' c1 c2)
  ·
    exfalso
    exact hS4 h c2 c1 (hS3 h c2 c1)
  · exact ⟨c1, c2⟩

theorem dsALoc_F4_of_leaves
    (hNF : LeafDSANoField) (hZS : LeafZiStructure) (hS3 : LeafDSACaseIIStep3)
    (hS4 : LeafDSACaseIIStep4) (hV : LeafDSAVertex) : DSALoc_F4 := by
  intro G _ _ L1 L2 S hyp _hq hS hns1 hns2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hyp
  have h : DSAHyp L1 L2 S := ⟨hR, hns1, hns2, hS⟩
  obtain ⟨c1, c2⟩ := dsA_caseI_of_leaves hNF hZS hS3 hS4 h
  obtain ⟨hs1, hl1, hp1, hSL1, hz1⟩ := hV h c1 c2
  obtain ⟨hs2, hl2, hp2, hSL2, hz2⟩ := hV h.symm c2 c1
  refine ⟨⟨⟨hs1, le_rfl, ?_⟩, hl1, ⟨hs2, le_rfl, ?_⟩, hl2⟩, ⟨hp1, hp2, hSL1, hSL2⟩, hz1, hz2⟩
  all_goals rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top

theorem dsBLoc_F4_of_leaves
    (hRed : LeafDSBReduce) (hJQ1 : LeafDSBJQ1) (hJQ2 : LeafDSBJQ2) (hUQ1 : LeafDSBUQ1)
    (hUQ2 : LeafDSBUQ2) (hSh : LeafShort2OfA5) (hAlt : LeafAlt5OfOrth)
    (hOm : LeafOmega4MinusOfOrth) (hZSU : LeafDSBZSU) (hZSJ : LeafDSBZSJ) : DSBLoc_F4 := by
  intro G _ _ L1 L2 S hyp _hq _hS hns h3
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hyp
  have hL1 : IsL2Quot 2 (oTwoQuot ↥L1) :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 Finite4.gen4 hR.hyp.h1 hns
  have hL2 : IsL2Quot 1 (oTwoQuot ↥L2) := isL2Quot_one_iff_perm3.mpr h3
  have h := hRed (⟨hR, hns, h3⟩ : DSBHyp0 L1 L2 S)
  by_cases cJ : ⁅dsZi L1 ((S ⊓ L1) ⊔ (S ⊓ L2)), L1⁆ = ⊥
  ·
    right
    obtain ⟨-, -, hQ8⟩ := hJQ1 h cJ
    obtain ⟨-, h64⟩ := hJQ2 h cJ
    exact ⟨⟨hL1, hQ8, hL2, h64⟩, hZSJ hR hL1 hQ8⟩
  ·
    left
    obtain ⟨-, -, hCT, hEA, hcard, hNat, -, -⟩ := hUQ1 h cJ
    obtain ⟨-, -, hSp⟩ := hUQ2 h cJ
    refine ⟨⟨hL2, hSp, ⟨hSh hL1 hCT hEA hcard, le_rfl, ?_⟩, hL1,
      hOm hL1 hCT hEA hcard hNat, hAlt hL1 hCT hEA hcard hNat⟩, hZSU hR h3 hSp⟩
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top

end CFSG.GH74.QTGen4.DSGen4
