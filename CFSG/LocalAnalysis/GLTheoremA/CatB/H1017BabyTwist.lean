module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeBChain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Defs


@[expose] def BabyTwistThreeB : Prop :=
  ∀ E D T : Subgroup NativeSporadic.B, IsElemAbelian 3 E → Nat.card E = 3 ^ 5 → D ≤ E →
    Nat.card D = 3 ^ 4 → (∀ x ∈ D, x ≠ 1 → IsConj x (BThreeFi23.phiB (BThreeFi23.t3 1))) →
    IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set NativeSporadic.B) →
    T ≤ Subgroup.centralizer (D : Set NativeSporadic.B) →
    T ≤ Subgroup.centralizer (E : Set NativeSporadic.B)

end Defs

section Assembly


theorem i1017BabyTwist_of_threeB
    (h : BabyTwistThreeB) : I1017BabyTwist := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ : Nonempty (NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group) :=
    CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  refine noTwistRank_of_model (s := .B) (r := 5) (X := NativeSporadic.B) ?_ ?_
  · with_reducible_and_instances exact ⟨b⟩
  intro E hE hcard T hT hET
  refine noTwist_of_hyperplane (r := 5) (by norm_num) ?_ E hE hcard T hT hET
  intro E' D T' hE' hE'c hDE hDc hT' hET' hTD
  by_cases hA : ∃ s ∈ D, s ≠ 1 ∧ ∃ d, BabyInv 0 d ∧ d * s * d⁻¹ = s⁻¹
  · obtain ⟨s, hsD, hs1, d, hd, hinv⟩ := hA
    exact BabyTwist.le_centralizer_of_threeA hE' hE'c.ge hT' hET' (hDE hsD) hs1 hd hinv
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hTD ht) s hsD).symm)
  · refine h E' D T' hE' hE'c hDE hDc (fun x hx hx1 => ?_) hT' hET' hTD
    exact uninverted_isConj_phiB_t3_one (orderOf_eq_prime (hE'.2 x (hDE hx)) hx1)
      fun d hd heq => hA ⟨x, hx, hx1, d, hd, heq⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.H1017
