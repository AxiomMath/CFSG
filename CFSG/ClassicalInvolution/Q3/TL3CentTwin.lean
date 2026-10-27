module

public import CFSG.ClassicalInvolution.Q3.TL3CentStep
public import CFSG.ClassicalInvolution.Q3.TL3GluePair

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


@[expose] def TightCentTwinLift (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) →
        ∀ c ∈ Subgroup.center Y, c ≠ 1 → (∃ y : Y, y * t * y⁻¹ = t * c) → ¬ TightE4 Y →
          GoodThreeElement R t

theorem tightCentTwinLift_of_lift (h : ∀ n, TightLargeLift n) : ∀ n, TightCentTwinLift n := by
  intro n hA hb Y _ _ hn R S t hd hc hE2 hQ hsmall c hcZ hc1 hy _
  obtain ⟨y, hy⟩ := hy
  exact h n hA hb Y hn R S t hd hc hE2 hQ hsmall (hd.not_edgeless_of_twin hcZ hc1 hy)

theorem tightStep_of_parts₅ (htw : ∀ n, TightTwistAllTwin n) (h1 : TightSmallBase)
    (h2 : ∀ n, TightLargeEdgeS n) (h3 : ∀ n, TightLargeLiftS n)
    (h4 : ∀ n, TightCentTwinLift n) : ∀ n, TightStep n := by
  intro n hA hb Y _ _ hn R S t hd hc
  by_cases hE2 : TightInO2 t
  · exact Or.inl (Or.inl hE2)
  rcases (tightDichotomy_holds n Y hn R S t hd hc).resolve_left hE2 with hQ | htw'
  swap
  · exact tightTwistStep_of_allTwin htw n hA hb Y hn R S t hd hc hE2 htw'
  by_cases hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)
  · exact h1 Y (by rw [hn]; exact hA) R S t hd hc hE2 hQ hsmall
  by_cases hZ : Subgroup.center Y = ⊥
  ·
    have hZF : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
      have h := hd.center_genFittingFStar_le hc hE2
      rw [hZ, le_bot_iff,
        Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h
      exact h
    obtain ⟨hs, hnab⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hQ hZF
    exact Or.inr (h3 n hA hb Y hn R S t hd hc hE2 hQ hsmall
      (h2 n hA hb Y hn hnab R S t hd hc hE2 hsmall) hZ)
  · obtain ⟨c, hcZ, hc2⟩ := exists_central_involution_of_center_ne_bot hc.2.2 hZ
    by_cases htwin : ∃ y : Y, y * t * y⁻¹ = t * c
    · have hc1 : c ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hc2
        exact absurd hc2 (by norm_num)
      by_cases hE4 : TightE4 Y
      · exact Or.inl (Or.inr (Or.inr (Or.inr hE4)))
      · exact Or.inr (h4 n hA hb Y hn R S t hd hc hE2 hQ hsmall c hcZ hc1 htwin hE4)
    · push Not at htwin
      exact tightExOrGood_of_central hb hn hd hc hE2 hcZ hc2 htwin

end Cit3

section Leaves

theorem tightHasMember3LargeBelow_of_leaves₂
    (hF1 : TightF1S fun m => CIT3Below m ∧ TightBelow m)
    (hEnd : TightEndGameOdd fun m => CIT3Below m ∧ TightBelow m)
    (htw : ∀ n, TightTwistAllTwin n) (hsmall : TightSmallBase)
    (hliftS : ∀ n, TightLargeLiftS n) (hliftC : ∀ n, TightCentTwinLift n)
    (hR4 : TightR4) : Q3T.MFS.TightHasMember3LargeBelow := by
  have h11b :=
    tightC19_11bS_of_F1_endgame hF1 (tightEndGameS_of_solv (tightEndGameSolv_of_odd hEnd))
  have hE := tightLargeEdgeS_of_core h11b
  exact tightHasMember3LargeBelow_of_inductive₂
    (tightInductive_of_step (tightStep_of_parts₅ htw hsmall hE hliftS hliftC)) hE hR4

end Leaves

end CFSG.ClassicalInvolution.Q3
