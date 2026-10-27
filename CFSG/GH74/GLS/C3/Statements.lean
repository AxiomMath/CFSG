module

public import CFSG.GH74.GLS.Gen4Exclusions

public section

namespace CFSG.GH74.GLS

open Blueprint Assembly.LowTwoRank

structure C3Hyp (G : Type) [Group G] [Finite G] : Prop where
  kproper : IsKProperSimple G
  gen4 : Gen4 G
  kgh : KGH G
  lt2o : IsLT2oType G
  notRE : ¬ IsRestrictedEvenType G

theorem C3Hyp.pRank_eq_four {G : Type} [Group G] [Finite G] (h : C3Hyp G) : pRank 2 G = 4 :=
  le_antisymm h.gen4.pRank_two_le h.lt2o.1

@[expose] def S_C3_gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ Nonempty (G ≃* alternatingGroup (Fin 10)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 11))

theorem S_C3_gen4_of_S_C3 (h : S_C3) : S_C3_gen4 :=
  fun G _ _ hG => h G hG.kproper hG.lt2o hG.notRE

theorem c23List_of_lb2_branch_gen4 {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    (hgen : Gen4 G) (hK : KGH G) (hSO : IsSpecialOddType G) (hC3 : S_C3_gen4)
    (hLB : IsLB2Type G → C23List G) : C23List G := by
  have hsub := l2Sub_of_not_l2Meets_g2 hG hSO.2
  by_cases hB : L2Meets G InB2 ∨ pRank 2 G ≤ 3
  · exact hLB ⟨hsub, hB, hSO.1⟩
  · rw [not_or] at hB
    have hrank : 4 ≤ pRank 2 G := by omega
    have hLT : IsLT2oType G := by
      refine ⟨hrank, fun x hx K hK => ?_⟩
      rcases hsub x hx K hK with h | h
      · exact Or.inl h
      · refine Or.inr (inU2_of_inT2_of_center_bot h ?_)
        by_contra hz
        exact hB.1 ⟨x, hx, K, hK, ⟨h, hz⟩⟩
    rcases hC3 G ⟨hG, hgen, hK, hLT, hSO.1⟩ with h | h | h
    · exact C23List.of_alt9 h
    · exact C23List.of_alt10 h
    · exact C23List.of_alt11 h

theorem specialOdd_of_gls6_gen4'
    (hSUS : S_SUS) (hC3 : S_C3_gen4)
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) (hS4 : S_stage4) (hS5 : S_C2starFour)
    (h161M12 : S_sixteenOne .M12) : S_specialOdd := by
  intro G _ _ hs hnonab hrank hgen hK _ _ hSO
  have hG := isKProperSimple_of_kgh hs hnonab hK
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hrank
  have h4 : pRank 2 G ≤ 4 := hgen.pRank_two_le
  exact c23List_of_lb2_branch_gen4 hG hgen hK hSO hC3 fun hLB =>
    c23List_of_isLB2Type_rank34_gen4 hSUS hP27 hTT hS4 hS5 h161M12 hgen hG h3 h4 hLB

theorem specialOdd_of_gls6_stages_gen4'
    (hSUS : S_SUS) (hC3 : S_C3_gen4)
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) (hS4 : S_stage4) (hS2 : S_stage2Four)
    (hSP : S_stage5_SP) (hLU : S_stage5_LU) (h161M12 : S_sixteenOne .M12)
    (h161McL : S_sixteenOne .McL) (h161Ly : S_sixteenOne .Ly) : S_specialOdd :=
  specialOdd_of_gls6_gen4' hSUS hC3 hP27 hTT hS4
    (S_C2starFour_of_stage5 hS2 hSP hLU h161McL h161Ly) h161M12

end CFSG.GH74.GLS
