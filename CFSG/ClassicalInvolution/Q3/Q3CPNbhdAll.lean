module

public import CFSG.ClassicalInvolution.Q3.Q3CPNbhd
public import CFSG.ClassicalInvolution.Q3.Q3YSFinal
public import CFSG.ClassicalInvolution.Q3.Q3YProd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}


theorem nbhd_shape3_proved (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) :
    ∃ (ι : Type) (_ : Finite ι)
      (D : LieSystemData3 ι (NbhdQuot (conjClass3 K) K₁) (nbhdFamily (conjClass3 K) K₁)),
      (z₁ ∉ nbrSpan3 (conjClass3 K) K₁ ∧ ShapeThin D ∧
        nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁)) ∨
      (∃ hzX : z₁ ∈ nbrSpan3 (conjClass3 K) K₁,
        ShapeDouble D (nbhdMk (conjClass3 K) K₁ z₁ hzX)) ∨
      (∃ hzX : z₁ ∈ nbrSpan3 (conjClass3 K) K₁,
        ShapeSp4 D (nbhdMk (conjClass3 K) K₁ z₁ hzX)) :=
  nbhd_shape3 (RouteD.Gaps.fundNoncentral 3) Q3YS.modelFourGroup3On_all Q3YS.sp4KleinQuat3 hz
    hBelow hB hA2 he

theorem nbhd_mem_or_thin_proved (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) :
    z₁ ∈ nbrSpan3 (conjClass3 K) K₁ ∨
      nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁) :=
  nbhd_mem_or_thin (RouteD.Gaps.fundNoncentral 3) Q3YS.modelFourGroup3On_all Q3YS.sp4KleinQuat3
    hz hBelow hB hA2 he

end CFSG.ClassicalInvolution.Q3.Q3CP

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.Assembly.Dichotomy

@[expose] def TypeC3NbhdNotThin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        ¬ nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁)

theorem typeC3NoThin_of_notThin (h : TypeC3NbhdNotThin) : Q3Y.TypeC3NoThin := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  rcases nbhd_mem_or_thin_proved hz hBelow hB hA2 he with hmem | hthin
  · exact hmem
  · exact absurd hthin (h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he)

end CFSG.ClassicalInvolution.Q3.Q3CP
