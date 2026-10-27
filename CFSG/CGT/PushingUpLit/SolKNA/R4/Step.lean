module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Twist
public import CFSG.CGT.PushingUpLit.SolKNA.R4.Dich
public import CFSG.CGT.PushingUpLit.SolKNA.TightR4Reduce

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


@[expose] def TightEdgeFalseSR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowR r n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightClsR r Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R →
          Subgroup.center Y = ⊥ → False

@[expose] def TightCentTwinLiftR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowR r n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightClsR r Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) →
        ∀ c ∈ Subgroup.center Y, c ≠ 1 → (∃ y : Y, y * t * y⁻¹ = t * c) → ¬ TightE4 Y → False

@[expose] def TightStepR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowR r n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightClsR r Y R S t →
      TightEx Y R S t

theorem tightStepR_of_parts {r : ℕ} (hr : 4 ≤ r) (htw : ∀ n, TightTwistAllTwinR r n)
    (h1 : TightSmallBaseR r) (h2 : ∀ n, TightLargeEdgeSR r n) (h3 : ∀ n, TightEdgeFalseSR r n)
    (h4 : ∀ n, TightCentTwinLiftR r n) : ∀ n, TightStepR r n := by
  intro n hA hb Y _ _ hn R S t hd hc
  by_cases hE2 : TightInO2 t
  · exact Or.inl hE2
  rcases (tightDichotomyR_holds r n Y hn R S t hd hc).resolve_left hE2 with hQ | htw'
  swap
  · exact tightTwistStepR_of_allTwin hr htw n hA hb Y hn R S t hd hc hE2 htw'
  by_cases hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)
  · exact h1.tightEx hr hd hc hE2 hQ hsmall
  by_cases hZ : Subgroup.center Y = ⊥
  ·
    have hZF : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
      have h : TA3.fstarCenter Y ≤ Subgroup.center Y := fstarCenter_le_center_R hd hc hE2
      rw [hZ, le_bot_iff] at h
      have h' : (Subgroup.center ↥(genFittingFStar Y)).map (genFittingFStar Y).subtype = ⊥ := h
      rwa [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h'
    obtain ⟨hs, hnab⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hQ hZF
    exact (h3 n hA hb Y hn R S t hd hc hE2 hQ hsmall
      (h2 n hA hb Y hn hnab R S t hd hc hE2 hsmall) hZ).elim
  · obtain ⟨c, hcZ, hc2⟩ := exists_central_involution_of_center_ne_bot hc.2.2 hZ
    by_cases htwin : ∃ y : Y, y * t * y⁻¹ = t * c
    · have hc1 : c ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hc2
        exact absurd hc2 (by norm_num)
      by_cases hE4 : TightE4 Y
      · exact Or.inr (Or.inr (Or.inr hE4))
      · exact (h4 n hA hb Y hn R S t hd hc hE2 hQ hsmall c hcZ hc1 htwin hE4).elim
    · push Not at htwin
      exact tightEx_of_centralR hr hb hn hd hc hE2 hcZ hc2 htwin

theorem tightBelowR_of_step {r : ℕ} (h : ∀ n, TightStepR r n) (N : ℕ) :
    CIT3Below N → TightBelowR r N := by
  intro hA
  have hmono : ∀ m, m ≤ N → CIT3Below m := fun m hm Y _ _ hY Λ hΛ =>
    hA Y (lt_of_lt_of_le hY hm) Λ hΛ
  have key : ∀ n, n ≤ N → TightBelowR r n := by
    intro n
    induction n with
    | zero =>
      intro _ Y _ _ hlt
      exact absurd hlt (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk Y _ _ hlt R S t hd hc
      by_cases hY : Nat.card Y < k
      · exact ih (by omega) Y hY R S t hd hc
      · exact Or.inl (h k (hmono k (by omega)) (ih (by omega)) Y (by omega) R S t hd hc)
  exact key N le_rfl

theorem tightBelowR_of_parts {r : ℕ} (hr : 4 ≤ r) (htw : ∀ n, TightTwistAllTwinR r n)
    (h1 : TightSmallBaseR r) (h2 : ∀ n, TightLargeEdgeSR r n) (h3 : ∀ n, TightEdgeFalseSR r n)
    (h4 : ∀ n, TightCentTwinLiftR r n) (N : ℕ) : CIT3Below N → TightBelowR r N :=
  tightBelowR_of_step (tightStepR_of_parts hr htw h1 h2 h3 h4) N

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
