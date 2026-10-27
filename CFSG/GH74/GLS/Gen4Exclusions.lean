module

public import CFSG.GH74.GLS.Assembly
public import CFSG.GH74.Filter.Sporadic.ON
public import CFSG.Sporadic.NativeFinite

public section

namespace CFSG.GH74

theorem SectionalTwoRankLE.of_sylow {X : Type*} [Group X] [Finite X] {r : ℕ} (S : Sylow 2 X)
    (h : SectionalTwoRankLE (S : Subgroup X) r) : SectionalTwoRankLE X r := by
  classical
  intro P hP
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S Q
  let f : (S : Subgroup X) →* X := (MulAut.conj g).toMonoidHom.comp (S : Subgroup X).subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.val_injective
  have hrange : P ≤ f.range := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup X) := hPQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨y, hy, rfl⟩ := hxQ
    exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨s, hs, hsP⟩ := h (P.comap f) (hP.comap_of_injective f hf)
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsP, Subgroup.map_comap_eq,
    inf_eq_right.mpr hrange]

theorem SectionalTwoRankLE.of_sylow_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G']
    {r : ℕ} {S : Sylow 2 G} {S' : Sylow 2 G'} (φ : (S : Subgroup G) ≃* (S' : Subgroup G'))
    (h : SectionalTwoRankLE G r) : SectionalTwoRankLE G' r :=
  SectionalTwoRankLE.of_sylow S' ((h.subgroup _).of_mulEquiv φ)

theorem Gen4.of_sameInvolutionFusionPattern {G G' : Type*} [Group G] [Group G'] [Finite G']
    (h : GLS.SameInvolutionFusionPattern G G') (hG : Gen4 G) : Gen4 G' := by
  obtain ⟨S, S', φ, -⟩ := h
  exact SectionalTwoRankLE.of_sylow_mulEquiv φ hG

namespace GLS

open Blueprint Assembly.LowTwoRank

theorem not_isApproxTo_ONan {G : Type} [Group G] (hG : Gen4 G) :
    ¬ IsApproxTo G (NativeSporadic.Carrier .ONan) := by
  rintro ⟨⟨S, S', φ, -, -⟩, -⟩
  have : Finite (NativeSporadic.Carrier .ONan) :=
    Sporadic.finite_carrier_of_ne_M .ONan (by decide)
  exact Filter.not_gen4_ON (SectionalTwoRankLE.of_sylow_mulEquiv φ hG)

theorem c23List_of_isLB2Type_rank34_gen4
    (hSUS : S_SUS) (hP27 : S_prop27)
    (hTT : S_twoThinOfB2) (hS4 : S_stage4) (hS5 : S_C2starFour) (h161M12 : S_sixteenOne .M12)
    {G : Type} [Group G] [Finite G] (hgen : Gen4 G) (hG : IsKProperSimple G)
    (h3 : 3 ≤ pRank 2 G) (h4 : pRank 2 G ≤ 4) (hLB : IsLB2Type G) : C23List G := by
  by_cases hU : HasTwoUniquenessSubgroup G
  · rcases hSUS G hG hLB hU with h | h | h
    · exact C23List.of_psl2_four h
    · exact C23List.of_U34 h
    · exact C23List.of_J1 h
  · have hStar := isLBStar2Type_of_isLB2Type hP27 hTT hG h3 hLB
    rcases (by omega : pRank 2 G = 3 ∨ pRank 2 G = 4) with h | h
    · rcases hS4 G hG hStar h hU with ⟨f, h⟩ | ⟨p, f, hp, hp2, hf, h3', h⟩ |
          ⟨p, f, hp, hp2, hf, h⟩ | h | h
      · exact C23List.of_twistedG2 h
      · exact C23List.of_g2 hp hp2 hf h3' h
      · exact C23List.of_trialityD4 hp hp2 hf h
      · exact C23List.of_M12 (isSporadic_of_isApproxTo (by decide) h161M12 hG h)
      · exact absurd h (not_isApproxTo_ONan hgen)
    · have hT : HasTwoThinConfiguration G := by
        rcases hStar with h2 | ⟨h2, -⟩ | hT
        · omega
        · omega
        · exact hT
      exact (hS5 G hG h hT hU).toC23List

theorem specialOdd_of_gls6_gen4
    (hSUS : S_SUS) (hC3 : S_C3)
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) (hS4 : S_stage4) (hS5 : S_C2starFour)
    (h161M12 : S_sixteenOne .M12) : S_specialOdd := by
  intro G _ _ hs hnonab hrank hgen hK _ _ hSO
  have hG := isKProperSimple_of_kgh hs hnonab hK
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hrank
  have h4 : pRank 2 G ≤ 4 := hgen.pRank_two_le
  exact c23List_of_lb2_branch hG hSO hC3 fun hLB =>
    c23List_of_isLB2Type_rank34_gen4 hSUS hP27 hTT hS4 hS5 h161M12 hgen hG h3 h4 hLB

theorem specialOdd_of_gls6_stages_gen4
    (hSUS : S_SUS) (hC3 : S_C3)
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) (hS4 : S_stage4) (hS2 : S_stage2Four)
    (hSP : S_stage5_SP) (hLU : S_stage5_LU) (h161M12 : S_sixteenOne .M12)
    (h161McL : S_sixteenOne .McL) (h161Ly : S_sixteenOne .Ly) : S_specialOdd :=
  specialOdd_of_gls6_gen4 hSUS hC3 hP27 hTT hS4
    (S_C2starFour_of_stage5 hS2 hSP hLU h161McL h161Ly) h161M12

end GLS

end CFSG.GH74
