module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONHyp31

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

theorem fourAFacts_of_lamLike2 {IsK : GroupClass} {S : List TauCeti.SporadicName} (e : ℕ)
    (h24 : TwoSylowStd S)
    (hautC : ∀ (G : Type) [Group G] [Finite G] (L K₁ N₀ T : Subgroup G) (s : G),
      (∃ s' ∈ S, OddCover s' L) → T ≠ ⊥ → Sol78Link5bData K₁ L T s → CFSG.IsQuasisimple ↥K₁ →
        IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → CanLoc K₁ N₀ →
          Group.IsSolvable ↥(autCentralizer L N₀) ∧
          (∀ A : Subgroup ↥(autCentralizer L N₀), IsPGroup 2 A →
            (∀ x ∈ A, x * x = 1) ∧ Nat.card A ≤ e) ∧
          (∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g))
    (hfix : ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
      (∃ (X : Type) (_ : Group X), IsK X ∧ Nonempty ((K₂ ⧸ center K₂) ≃* (X ⧸ center X))) →
      InvolutionFixesNotLam2 K₂ (2 * e))
    (hsec : ∀ (G : Type) [Group G] [Finite G] (K₁ N₀ : Subgroup G), CFSG.IsQuasisimple ↥K₁ →
      IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → CanLoc K₁ N₀ →
        ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
          TwoSubgroupsAbelian ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))))) :
    FourAFacts IsK S := by
  refine ⟨fun X _ => LamLike2 (2 * e) X, True, fun _ => h24,
    fun X Y _ _ f hf h => h.of_injective hf, ?_, hfix, ?_⟩
  · intro G _ _ L K₁ N₀ T s hL hT hdata hq hK hcan _ htw
    obtain ⟨hAs, hA2, hin⟩ := hautC G L K₁ N₀ T s hL hT hdata hq hK hcan
    obtain ⟨s', -, hcov⟩ := hL
    have hN₀L : N₀ ≤ L := hcan.le.trans hdata.le_left
    exact lam_isLamLike2 (htw trivial) hAs hA2 hin hN₀L hcov.2.1
  · intro G _ _ K₁ N₀ hq hK hcan Y _ _ hY hsecY
    have hab : TwoSubgroupsAbelian Y := fun P hP x hx y hy =>
      commute_of_exp_two (hY.2 P hP).1 x hx y hy
    obtain ⟨A, f, hf⟩ := hsecY
    have : Group.IsSolvable Y := hY.1
    have hsolA : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective A.subtype_injective
    exact hsec G K₁ N₀ hq hK hcan ⟨Group.isSolvable_of_surjective hf,
      twoSubgroupsAbelian_of_section hab ⟨A, f, hf⟩⟩

end CFSG.EvenSporadicStandard.Induction
