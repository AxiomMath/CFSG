module

public import CFSG.CGT.PushingUpLit.SolKAb.Rank
public import CFSG.CGT.PushingUpLit.SolKAb.Residue
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
import CFSG.CGT.PushingUpLit.SolKAb.CyclicEight

public section

namespace CFSG.CGT.PushingUpLit.SolKAb

open CFSG.ComponentClassification.AschbacherKnownGroup
open CFSG.Assembly (pCoreOf)
open CFSG.Open (IsElemAbelian)
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open CFSG.RankThree.GF2n.Tim78 (omegaTwoSub)
open CFSG.RankThree.PartTwo (omegaOneSub)
open CFSG.CGT.PushingUpLit.SolKMT (SolomonTimmesfeldMain)

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

section Main


theorem STSetting.abelian_half (hL25 : Asc76Lemma25) (S : STSetting G K) (R : Sylow 2 K)
    (h : IsCommSubgroup (sylowImg R))
    (hres : ¬ (¬ IsElemAbelian 2 (sylowImg R) ∧ Nat.card ↥(omegaOneSub (sylowImg R)) = 4)) :
    (IsCyclic K ∧ Nat.card K = 4) ∨
      (sylowImg R = pCoreOf 2 K ∧ IsElemAbelian 2 (sylowImg R)) ∨
      (sylowImg R = K ∧ IsCyclic K ∧ 8 ≤ Nat.card K ∧
        (HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G)) := by
  by_cases hel : IsElemAbelian 2 (sylowImg R)
  · exact Or.inr (Or.inl ⟨S.sylowImg_eq_pCoreOf R h, hel⟩)
  · have h2grp : IsPGroup 2 (sylowImg R) := isPGroup_sylowImg R
    rcases omegaOne_card_cases h h2grp (S.sylowImg_ne_bot R) with h2 | h4 | h8
    · have hcyc : IsCyclic ↥(sylowImg R) := isCyclic_of_card_omegaOne_two h h2grp h2
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2grp
      have htop := S.eq_top_of_isCyclic_sylowImg R hcyc
      have hKR : sylowImg R = K := by
        show (R : Subgroup K).map K.subtype = K
        rw [htop, Subgroup.map_top, Subgroup.range_subtype]
      have hKcard : Nat.card ↥K = Nat.card ↥(sylowImg R) := by rw [hKR]
      have hKcyc : IsCyclic ↥K := by rw [← hKR]; exact hcyc
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | rfl | hm3
      · exfalso
        have h1 : Nat.card ↥(sylowImg R) = 1 := by rw [hm]; rfl
        exact S.sylowImg_ne_bot R (Subgroup.eq_bot_of_card_eq _ h1)
      · exact absurd (isElemAbelian_of_card_two h (by rw [hm]; rfl)) hel
      · exact Or.inl ⟨hKcyc, by rw [hKcard, hm]; rfl⟩
      · have h8 : 8 ≤ Nat.card ↥(sylowImg R) := by
          rw [hm]
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
        exact Or.inr (Or.inr ⟨hKR, hKcyc, hKcard ▸ h8,
          S.dihedral_of_cyclic_ge_eight hL25 R hcyc h8⟩)
    · exact absurd ⟨hel, h4⟩ hres
    · exact absurd (S.isElemAbelian_sylowImg_of_eight_le R h h8) hel

theorem solomonTimmesfeldMain_of_residue (hL25 : Asc76Lemma25)
    (h : SolomonTimmesfeldMainResidue) : SolomonTimmesfeldMain := by
  refine solomonTimmesfeldMain_iff.mpr ?_
  intro G _ _ hKP hs hna K hK hM hF R
  have S : STSetting G K := ⟨hs, hna, hK, hM, hF⟩
  by_cases hc : IsCommSubgroup (sylowImg R)
  · by_cases hres : ¬ IsElemAbelian 2 (sylowImg R) ∧ Nat.card ↥(omegaOneSub (sylowImg R)) = 4
    · exact h.rankTwo G hKP hs hna K hK hM hF R hc hres.1 hres.2
        ⟨omegaTwoSub (sylowImg R), fun x => CFSG.RankThree.GF2n.Tim78.mem_omegaTwoSub_iff hc,
          S.nonempty_omegaTwoSub_equiv_of_card_omegaOne_four R hc hres.1 hres.2⟩
    · rcases S.abelian_half hL25 R hc hres with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact h.nonabelian G hKP hs hna K hK hM hF R hc

end Main

end CFSG.CGT.PushingUpLit.SolKAb
