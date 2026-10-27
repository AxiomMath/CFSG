module

public import CFSG.ClassicalInvolution.Q3.Q3JIWeak
public import CFSG.ClassicalInvolution.Q3.Q3AMTriBr
public import CFSG.ClassicalInvolution.Q3.Q3DBExactConn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.JI

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform

section Statements


@[expose] def DBridgeU3J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    CITBelowT (.sl2 3 1) (Nat.card G) → Asc77.CITBelowAll 3 (Nat.card G) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      CFSG.ClassicalInvolution.DeltaConnected K

end Statements

section Reduction


theorem oddCoreFree_of_oddCoreFreeA2DiscD3I (h : Q3AM.OddCoreFreeA2DiscD3I) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z) (hBelowT : CITBelowT (.sl2 3 1) (Nat.card G))
    (hAll : Asc77.CITBelowAll 3 (Nat.card G)) (hr : 3 ≤ CFSG.Open.twoRank G)
    (hlarge : ¬ TwoSubgroupsFourGenerated G)
    (hD : DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z))) :
    Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  by_cases hA2 : A2Configuration z (satU (.sl2 3 1) K z)
  · by_cases hΔ : CFSG.ClassicalInvolution.DeltaConnected (satU (.sl2 3 1) K z)
    · exact Q3DB.oddCentralizerFree_of_exact_sat hz
        (Q3DB.exactMembers3_of_omegaConnected hnab ((hz.satU_member).toQ3 (by norm_num))
          (oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num)))
          ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelowT)
          (omegaConnected_range_conjSub hΔ))
    · exact h G hnab K z hz hBelowT hAll hr hlarge hD hA2 hΔ
  · exact Q3DB.oddCentralizerFree_of_dConnected_sat_of_not_a2 hnab hz hBelowT hA2 hD

theorem dBridgeU3J_of_oddCoreFreeA2DiscD3I (h : Q3AM.OddCoreFreeA2DiscD3I) : DBridgeU3J :=
  fun _ _ _ _ hnab hBelowT hAll _ _ hz hr hlarge hD =>
    Q3DB.deltaConnected_of_oddCentralizerFree hnab hz hBelowT
      (oddCoreFree_of_oddCoreFreeA2DiscD3I h hnab hz hBelowT hAll hr hlarge hD) hD

theorem smallDisconnected3J_of_branchStatements (hb : DBridgeU3J) (h6 : Thm6DU 3 1)
    (h7 : Thm7DU 3 1) (h8 : Thm8DU 3 1) : SmallDisconnected3J := by
  intro G _ _ _ hnab K z hz hBelow hAll h3 h4 hΔ
  have hBelowT : CITBelowT (.sl2 3 1) (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mpr hBelow
  have hzU : IsClassicalMemberU (.sl2 3 1) K z := IsClassicalMemberU.ofQ3 hz
  by_cases hD : DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z))
  · exact absurd (hb G hnab hBelowT hAll K z hzU h3 h4 hD) hΔ
  · exact smallDisconnectedDU_of_aschbacher h6 h7 h8 G K z
      ⟨hnab, by norm_num, by norm_num, hBelowT, hzU, h3, h4, hD⟩

theorem smallDisconnected3J_of_oddCoreFreeA2DiscD3I (h : Q3AM.OddCoreFreeA2DiscD3I)
    (hs : Q3.Disc3.AscStand3OfBranch) (h6 : Q3.Disc3.Thm6A3) (h7 : Q3.Disc3.Thm7A3)
    (h8 : Q3.Disc3.Thm8A3) : SmallDisconnected3J :=
  smallDisconnected3J_of_branchStatements (dBridgeU3J_of_oddCoreFreeA2DiscD3I h)
    (Q3.Disc3.thm6DU_three_of hs h6) (Q3.Disc3.thm7DU_three_of hs h7)
    (Q3.Disc3.thm8DU_three_of hs h8)

end Reduction

end CFSG.ClassicalInvolution.Q3.JI
