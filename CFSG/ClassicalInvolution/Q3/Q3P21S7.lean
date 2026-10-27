module

public import CFSG.ClassicalInvolution.Q3.Q3P21S6B

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

section Chain

theorem exists_shortNode_of_config3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {z : G} {K : Subgroup G} (c : Q3TP.TCtxS3 .PSU 4 Ω K z) {N K₂ : Subgroup G} {t : G}
    (hNt : IsClassicalMember3 N t) (hK₂ : K₂ ∈ centralizingMembers Ω {z}) (hK₂K : K₂ ≠ K)
    (hnotTwin : ∀ T : Subgroup G, IsTwinAt Ω K T z → K₂ ≠ T)
    (hKN : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K N)
    (hNK₂ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₂)
    (hlin : ∀ ht : t * z * t⁻¹ = z, TauLinear3 c ht) :
    ∃ Us : Subgroup G, Us ≤ ⁅Us, Us⁆ ∧ Commutes K Us ∧
      Us ≤ Subgroup.centralizer ({t} : Set G) ∧
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W K₂ Us := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  obtain ⟨T₁, hT₁, hT₁img⟩ := c.exists_twin
  have hT₁tw : IsTwinAt Ω K T₁ z :=
    ⟨hT₁, c.twin_ne hT₁ hT₁img.le, fun M hM hMT => c.commutes_T_of_ne hT₁ hT₁img.le hM hMT,
      fun M hM hMK => c.commutes_K_of_ne hM hMK⟩
  have hK₂Q : ¬ locImg Ω z K₂ ≤ c.d.Q₁ := fun h =>
    hnotTwin T₁ hT₁tw (c.eq_of_locImg_le_Q₁ hK₂ hT₁ h hT₁img.le)
  obtain ⟨W₁, hW₁⟩ := hKN
  have hcomm : z * t = t * z := RouteD.Gaps.standardPair_involutions_commute h2 hW₁ c.hz.mem
    hNt.mem c.hz.orderOf_eq_two hNt.orderOf_eq_two
  have ht : t * z * t⁻¹ = z := by
    rw [← hcomm, mul_inv_cancel_right]
  exact exists_shortNode_of_linear3 c hNt hK₂ hK₂K hK₂Q hNK₂ ht (hlin ht)

theorem twinSU4ShortNode3_of_linear3 (h3 : OddThreeFreeInput) (hlin : TwinSU4Linear3) :
    Q3TY.TwinSU4ShortNode3 := by
  intro G _ _ _ hnab K z hR hshape N K₂ t hNΩ hNt hK₂ hK₂K hnotTwin hKK₂ p1 p2
  obtain ⟨c⟩ := Q3TP.nonempty_tctxS3 Q3TY.yData3S_psu4 h3 hR hshape
  exact exists_shortNode_of_config3 c hNt hK₂ hK₂K hnotTwin p1 p2
    (hlin G hnab K z hR hshape c N K₂ t hNΩ hNt hK₂ hK₂K hnotTwin hKK₂ p1 p2)

end Chain

end CFSG.ClassicalInvolution.Q3.Q3P21
