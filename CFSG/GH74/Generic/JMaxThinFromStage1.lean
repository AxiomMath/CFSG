module

public import CFSG.GH74.Generic.JMaxThinGen4
public import CFSG.GH74.GLS.Stage2.Local.Prop28Weak

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local.Prop28

@[expose] def ThinStage1Interface : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GLS.IsKProperSimple G → Gen4 G → KGH G →
    (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) → 3 ≤ Open.twoRank G →
      GLS.HasTwoThinConfiguration G →
        ∃ (z : G) (S : Subgroup G) (k : Kind), k ≠ Kind.m12 ∧ IsCentralInvolution z ∧
          CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) ∧ Stage1Data G z S k ∧
          ∀ y : G, Prop27Y z y → CompsGood y

theorem s_corTwoThinGen4_of_thinStage1Interface (h : ThinStage1Interface) : S_corTwoThinGen4 := by
  intro G _ _ hG hgen hK hnab hr hg hthin
  obtain ⟨z, S, k, hk, hz, hS, hd, hP⟩ := h G hG hgen hK hnab hr hthin
  exact GLS.Stage2.Local.Prop28.not_l2Meets_inG2_of_stage1Data_comps hk hz hS hd hP hg

theorem thinStage1Interface_of_leaves
    (Std0 : ∀ (G : Type) [Group G] [Finite G], Prop)
    (Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop)
    (hstd : ∀ (G : Type) [Group G] [Finite G], GLS.IsKProperSimple G → Gen4 G → KGH G →
      (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) → 3 ≤ pRank 2 G →
        pRank 2 G ≤ 4 → Std0 G)
    (hdata : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → Stage1Data G z S k)
    (h3 : ∀ (G : Type) [Group G] [Finite G], Std0 G → pRank 2 G = 3 →
      GLS.HasTwoThinConfiguration G →
        ∃ (z : G) (S : Subgroup G), IsCentralInvolution z ∧
          CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) ∧ Ctx G z Kind.g2 S)
    (h4 : ∀ (G : Type) [Group G] [Finite G], Std0 G → pRank 2 G = 4 →
      GLS.HasTwoThinConfiguration G →
        ∃ (z : G) (S : Subgroup G) (k : Kind), (k = Kind.psp4 ∨ (∃ ε : Bool, k = Kind.l4 ε) ∨
          k = Kind.mcl ∨ k = Kind.ly) ∧ IsCentralInvolution z ∧
          CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) ∧ Ctx G z k S)
    (hP27 : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx G z k S →
      ∀ y : G, Prop27Y z y → CompsGood y) :
    ThinStage1Interface := by
  intro G _ _ hG hgen hK hnab hr hthin
  have hle : Open.twoRank G ≤ 4 := hgen.twoRank_le
  have hr3 : 3 ≤ pRank 2 G := by rw [GLS.pRank_two_eq_twoRank]; exact hr
  have hr4 : pRank 2 G ≤ 4 := by rw [GLS.pRank_two_eq_twoRank]; exact hle
  have hs0 : Std0 G := hstd G hG hgen hK hnab hr3 hr4
  rcases (by omega : pRank 2 G = 3 ∨ pRank 2 G = 4) with h | h
  · obtain ⟨z, S, hz, hS, hc⟩ := h3 G hs0 h hthin
    exact ⟨z, S, Kind.g2, by simp, hz, hS, hdata G z Kind.g2 S hc, hP27 G z Kind.g2 S hc⟩
  · obtain ⟨z, S, k, hk, hz, hS, hc⟩ := h4 G hs0 h hthin
    refine ⟨z, S, k, ?_, hz, hS, hdata G z k S hc, hP27 G z k S hc⟩
    rcases hk with rfl | ⟨ε, rfl⟩ | rfl | rfl <;> simp

end CFSG.GH74.Generic
