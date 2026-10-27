module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThm4
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Generic CFSG.Blueprint

@[expose] def NoDatum4R (r : ℕ) (F : Type) [Group F] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], Nonempty (↥N ≃* F) →
    Subgroup.centralizer (N : Set G) = ⊥ → TwoSubgroupsFourGenerated ↥N →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) → False

@[expose] def OtherFamily (F : Type) [Group F] : Prop :=
  (SmallG2 F ∨ SmallD4 F ∨ SmallPSp4 F ∨ SmallTwistedG2 F ∨ SmallL4 F ∨ SmallU4 F ∨ SmallL5 F ∨
    SmallU5 F ∨ SmallM12 F ∨ SmallM11 F ∨ LieModel F .PSL 3 3 1 ∨ LieModel F .PSU 3 3 1) ∨
    Nobq.ExcludedSmall F

@[expose] def NoDatumOtherR (r : ℕ) : Prop :=
  4 ≤ r → ∀ (F : Type) [Group F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    OtherFamily F → NoDatum4R r F

@[expose] def SmallListR : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    TwoSubgroupsFourGenerated F → SmallFamily F ∨ Nobq.ExcludedSmall F

@[expose] def EdgelessSection {G : Type} [Group G] [Finite G] (K W : Subgroup G) : Prop :=
  K ≤ W ∧ IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : G) K) = W ∧
    ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W) ∧ TightEdgeless (K.subgroupOf W)

@[expose] def EdgelessClassUniqueR (r : ℕ) (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  4 ≤ r → ∀ (G : Type) [Group G] [Finite G] (J L L₀ : Subgroup G), F2ConfigR r J L L₀ →
    P ↥(L₀.map (QuotientGroup.mk' (Subgroup.center G))) →
    (∃ W : Subgroup G, EdgelessSection J W) → (∃ W : Subgroup G, EdgelessSection L W) →
    ∃ a : G ⧸ Subgroup.center G, J.map (QuotientGroup.mk' (Subgroup.center G)) =
      conjSub a (L.map (QuotientGroup.mk' (Subgroup.center G)))

@[expose] def EdgelessFamily (F : Type) [Group F] : Prop :=
  SmallL2 F ∨ SmallL3Ne3 F ∨ SmallU3Ne3 F

theorem edgelessClassUniqueR_edgelessFamily_iff {r : ℕ} :
    EdgelessClassUniqueR r EdgelessFamily ↔
      EdgelessClassUniqueR r SmallL2 ∧ EdgelessClassUniqueR r SmallL3Ne3 ∧
        EdgelessClassUniqueR r SmallU3Ne3 := by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun ⟨h2, h3, h4⟩ => ?_⟩
  · exact fun hr G _ _ J L L₀ hc hP hJ hL => h hr G J L L₀ hc (Or.inl hP) hJ hL
  · exact fun hr G _ _ J L L₀ hc hP hJ hL => h hr G J L L₀ hc (Or.inr (Or.inl hP)) hJ hL
  · exact fun hr G _ _ J L L₀ hc hP hJ hL => h hr G J L L₀ hc (Or.inr (Or.inr hP)) hJ hL
  · intro hr G _ _ J L L₀ hc hP hJ hL
    rcases hP with hP | hP | hP
    · exact h2 hr G J L L₀ hc hP hJ hL
    · exact h3 hr G J L L₀ hc hP hJ hL
    · exact h4 hr G J L L₀ hc hP hJ hL

end CFSG.CGT.PushingUpLit.SolKNA.R4
