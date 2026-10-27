module

public import CFSG.GH74.RouteRefine
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import CFSG.GH74.Uniqueness.SU.SU0SUS
public import CFSG.GH74.AS16.E2.Leaves
public import CFSG.GH74.GLS.Assembly
public import CFSG.GH74.GLS.Prop27.Defs

public section

namespace CFSG.GH74

open GLS Subgroup Blueprint Assembly.LowTwoRank

namespace GLS

theorem isLBStar2Type_of_isLB2Type_G (hP27 : Prop27.S_prop27G) (hTT : S_twoThinOfB2G)
    {G : Type} [Group G] [Finite G] (hgen : Gen4 G) (hK : KGH G) (hG : IsKProperSimple G)
    (h3 : 3 ≤ pRank 2 G) (hLB : IsLB2Type G) : IsLBStar2Type G := by
  have hnoG2 : ¬ L2Meets G InG2 := hLB.isSpecialOddType.2
  by_cases hB : L2Meets G InB2
  · exact Or.inr (Or.inr (hTT G hgen hG h3 hnoG2 hB))
  · have hle : pRank 2 G ≤ 3 := hLB.2.1.resolve_left hB
    refine Or.inr (Or.inl ⟨hle, ?_⟩)
    have h33 : pRank 2 G = 3 := le_antisymm hle h3
    by_cases hC2 : L2Sub G InC2
    · have := hP27 G hG hgen hK hLB h33 hC2
      refine L2Meets.mono (fun K _ h => Or.inr ?_) this
      exact hasL2Model_odd_gt_three (fun q hq => isFM9_odd hq) h
    · simp only [L2Sub, not_forall] at hC2
      obtain ⟨x, hx, K, hK, hnK⟩ := hC2
      have hT : InT2 K := (hLB.1 x hx K hK).resolve_left hnK
      have hz : center K = ⊥ := by
        by_contra hz
        exact hB ⟨x, hx, K, hK, ⟨hT, hz⟩⟩
      refine ⟨x, hx, K, hK, ?_⟩
      rcases inT2_cases_of_center_bot hT hz with h | h
      · exact Or.inr (hasL2Model_odd_gt_three (fun q hq => hq.1) h)
      · exact Or.inl h

namespace Stage12

theorem c23List_of_isLB2Type_rank34_StdG
    (hSUS : S_SUS_KGH) (hP27 : Prop27.S_prop27G)
    (hTT : S_twoThinOfB2G) (hS4 : S_stage4_Std) (hCh6 : S_ch6_Std) (hS5 : S_C2starFour_Std)
    (hAsc : M12.S_Asc03_simple) {G : Type} [Group G] [Finite G] (hgen : Gen4 G) (hK : KGH G)
    (hnonab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) (hG : IsKProperSimple G)
    (h3 : 3 ≤ pRank 2 G) (h4 : pRank 2 G ≤ 4) (hLB : IsLB2Type G) : C23List G := by
  by_cases hU : HasTwoUniquenessSubgroup G
  · rcases hSUS G hG.1 hG.2.1 hK hLB hU with h | h | h
    · exact C23List.of_psl2_four h
    · exact C23List.of_U34 h
    · exact C23List.of_J1 h
  · have hStar := isLBStar2Type_of_isLB2Type_G hP27 hTT hgen hK hG h3 hLB
    have hStd : Std G := ⟨hG, hgen, hK, ⟨h3, h4⟩, hnonab, hLB, hU⟩
    rcases (by omega : pRank 2 G = 3 ∨ pRank 2 G = 4) with h | h
    · rcases hCh6 G hStd h (hS4 G hStd h hStar) with ⟨f, h⟩ | ⟨p, f, hp, hp2, hf, h3', h⟩ |
          ⟨p, f, hp, hp2, hf, h⟩ | h
      · exact C23List.of_twistedG2 h
      · exact C23List.of_g2 hp hp2 hf h3' h
      · exact C23List.of_trialityD4 hp hp2 hf h
      · obtain ⟨z, _, hz, hq⟩ := h
        exact C23List.of_M12 (hAsc G hG.1 z hz hq)
    · have hT : HasTwoThinConfiguration G := by
        rcases hStar with h2 | ⟨h2, -⟩ | hT
        · omega
        · omega
        · exact hT
      exact (hS5 G hStd h hT).toC23List

end Stage12

end GLS

theorem restrictedEven_of_ALSS_E2 (hQ : S_QTKE_Gen4) (hAS : AS16.E2.S_ALSS3121E2)
    (hE2 : S_restrictedEvenThin) : S_restrictedEven :=
  fun G _ _ hs hnonab hrank hgen hK hnab hLx hre => by
    have he : Assembly.evenRank G ≤ 2 := hE2 G hs hnonab hrank hgen hK hnab hLx hre
    have hH : E2.Hyp G := ⟨hs, hnonab, hrank, hgen, hK, hnab, hLx, hre⟩
    exact hQ G hs hnonab hrank hgen hK (hAS G hH he) he

end CFSG.GH74
