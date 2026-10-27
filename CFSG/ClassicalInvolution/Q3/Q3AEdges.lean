module

public import CFSG.ClassicalInvolution.Q3.Q3NTAlpha
public import CFSG.ClassicalInvolution.Q3.Q3TMain

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap


@[expose] def LocCommute3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) →
      ∀ (L M : Subgroup G) (l m : G), L ∈ conjClass3 K → M ∈ conjClass3 K →
        IsClassicalMember3 L l → IsClassicalMember3 M m → l ≠ m → l * m = m * l →
        M ≤ Subgroup.centralizer ({l} : Set G) → Commutes L M

@[expose] def AlphaEdges3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥

theorem typeC3Alpha_of_edges (hE : AlphaEdges3) : TypeC3Alpha :=
  fun G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB _ K₁ K₂ z₁ z₂ he =>
    hE G hnab K z hz hBelow h3 h4 hΔ hB K₁ K₂ z₁ z₂ he

theorem alphaRank2_of_edges (hLC : LocCommute3) (hE : AlphaEdges3) :
    AlphaCent3Under fun K _ => ¬ BootData3 (conjClass3 K) := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB K₁ L z₁ w hK₁ hL hz₁ hw hne hLz
  have hzw : z₁ * w = w * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp (hLz hw.mem)).symm
  have hc : Commutes K₁ L :=
    hLC G hnab K z hz hBelow h3 h4 hΔ hB K₁ L z₁ w hK₁ hL hz₁ hw hne hzw hLz
  exact hE G hnab K z hz hBelow h3 h4 hΔ hB K₁ L z₁ w ⟨hK₁, hL, hz₁, hw, hc, hne⟩


theorem smallA2Setup3_of_edges (hLC : LocCommute3) (hE : AlphaEdges3) : SmallA2Setup3 :=
  smallA2Setup3_of_alphaCent3 fun G _ _ _ hnab K z hz hBelow h3 h4 hΔ hP K₁ L z₁ w hK₁ hL hz₁ hw
      hne hLz =>
    alphaRank2_of_edges hLC hE G hnab K z hz hBelow h3 h4 hΔ hP.1 K₁ L z₁ w hK₁ hL hz₁ hw hne hLz

theorem smallTypeCSetup3_of_edges (hE : AlphaEdges3) : SmallTypeCSetup3 :=
  smallTypeCSetup3_of_alpha (typeC3Alpha_of_edges hE)

theorem cit3LargeWeak_of_edges (hd : SmallDisconnected3) (hb3 : BootTriple3) (hb : BootNoTriple3)
    (hLC : LocCommute3) (hE : AlphaEdges3) (hrec : SetupRecognition3) : CIT3LargeWeak :=
  cit3LargeWeak_of_pieces hd hb3 hb (smallA2Setup3_of_edges hLC hE) (smallTypeCSetup3_of_edges hE)
    hrec

end CFSG.ClassicalInvolution.Q3
