module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadFin
public import CFSG.ClassicalInvolution.Q3.Q3AMBadStand
public import CFSG.ClassicalInvolution.Q3.Q3DBMain
public import CFSG.ClassicalInvolution.Q3.Q3ExD

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Statements


@[expose] def Thm5Bad3I : Prop :=
  Asc77.IHInterface8 3 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G),
    Q3T8.Asc77.BadStd8 Ω K J S R T W z t → IsIntrinsicU (.sl2 3 1) K z →
      Asc77.CITBelowAll 3 (Nat.card G) → False

@[expose] def OddCoreFreeA2DiscD3I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → Asc77.CITBelowAll 3 (Nat.card G) →
      3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      A2Configuration z (satU (.sl2 3 1) K z) →
      ¬ CFSG.ClassicalInvolution.DeltaConnected (satU (.sl2 3 1) K z) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥

end Statements

section Reduction


theorem oddCoreFreeA2DiscD3I_of_thm5Bad3I (hF : TwoElementsNormalizeU (.sl2 3 1))
    (hih : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n) (hIH : Asc77.IHInterface8 3)
    (h5 : Thm5Bad3I) (hT : TwinBridge3) : OddCoreFreeA2DiscD3I := by
  intro G _ _ _ hnab K z hz hBelowT hb9 hr hlarge hD hA2 hΔ
  by_cases htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 3 1) K z))
      (satU (.sl2 3 1) K z), K' ≠ satU (.sl2 3 1) K z
  · exact hT G hnab K z hz hBelowT hr hlarge hD hA2 hΔ htw
  push Not at htw
  have hz3 := (hz.satU_member).toQ3 (by norm_num)
  have hint : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ satU (.sl2 3 1) K z :=
    oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num))
  have hBelow3 : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelowT
  obtain ⟨M, N, a, t, hM, hN, ha, ht, -⟩ := Q3NH.exists_dEdge_distinct hnab hz3 hD
  by_cases hα : Balance.Bootstrap.alphaCore (Subgroup.closure ({a, t} : Set G)) = ⊥
  · exact Q3DB.oddCentralizerFree_of_exact_sat hz
      (Q3NH.exactMembers3_of_alphaDEdge hnab hz3 hint hBelow3 hN ha ht hα)
  exfalso
  have hbad : alphaOf (Subgroup.closure ({t, a} : Set G)) ≠ ⊥ := fun h0 => hα (by
    rw [Set.pair_comm]
    exact alphaCore_eq_bot_of_alphaOf_eq_bot h0)
  have hst3 := bridge_ascStand3 hF hih hnab hz hBelowT htw
  have htrans : ∀ J ∈ CoreAssembly.conjClass (satU (.sl2 3 1) K z),
      ∃ g : G, conjSub g (satU (.sl2 3 1) K z) = J := fun J hJ => by
    obtain ⟨g, rfl⟩ := hJ
    exact ⟨g, rfl⟩
  have hs := Q3T8.Asc77.AscStand.of_stand3 (hst3.rebase hM) hr hlarge
  have hntM := Asc77.T8.noTwins_of_mem hst3.hyp.conjInvariant htrans htw hM
  have haU : IsUniqueInvolution M a :=
    (IsClassicalMemberU.ofQ3 ha).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have htU : IsUniqueInvolution N t :=
    (IsClassicalMemberU.ofQ3 ht).isUniqueInvolution (MemberType.cert_sl2 3 1)
  obtain ⟨S, R, T, W, hB⟩ := badStd8_of_edge hs hntM hD haU hN htU hbad
  have hintM : IsIntrinsicU (.sl2 3 1) M a := by
    obtain ⟨g, rfl⟩ := hM
    have hzU : IsUniqueInvolution (satU (.sl2 3 1) K z) z :=
      hz.satU_member.isUniqueInvolution (MemberType.cert_sl2 3 1)
    have ha' : a = g * z * g⁻¹ := haU.eq (hzU.conj g)
    rw [ha']
    exact (isIntrinsicU_satU (.sl2 3 1) K z).conj g
  exact h5 hIH G _ M N S R T W a t hB hintM hb9

end Reduction

end CFSG.ClassicalInvolution.Q3.Q3AM
