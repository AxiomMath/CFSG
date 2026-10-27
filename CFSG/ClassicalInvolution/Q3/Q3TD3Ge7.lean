module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Pat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Ge7

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem toralNormalD3_of_fixed_member {m : ℕ} (hm : 7 ≤ m) (c : TCtx3 .POmegaPlus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    ToralNormalD3 c (partner_involution_commutes_z3 c.hz ht hKβ) := by
  obtain ⟨M, hMΩ, hKM, hβM, hMN⟩ := hfixM
  obtain ⟨u, rfl⟩ : ∃ u, m = u + 3 + 4 := ⟨m - 7, by omega⟩
  have hMN' : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMN fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_plus3 (by omega) c hsingle hβ ht hKβ hMΩ hKM hβM
  exact toralNormalD3_of_nodes c ht hKβ hMΩ hMN' nd h0 h1

theorem PartnerPatternPlus3.of_fixed_member_ge7 {m : ℕ} (hm : 7 ≤ m)
    (hMFZ : Gaps.FundNoncentral 3) (c : TCtx3 .POmegaPlus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    PartnerPatternPlus3 m Ω K β t :=
  PartnerPatternPlus3.of_toral_normal hm hMFZ (orthFacts3_plus (by omega)) c hsingle D hβ ht hKβ
    hfixM (toralNormalD3_of_fixed_member hm c hsingle hβ ht hKβ hfixM)

end Ge7

theorem partnerPatternStmtD3_ge7 (h3 : OddThreeFreeInput) {m : ℕ} (hm : 7 ≤ m) :
    PartnerPatternStmtD3 m := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  have hadm : StatedLieAdmissible .POmegaPlus m 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ m; omega⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_plus (by omega) hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨ι, hι, D, hcard, -⟩ := id hshape
  exact PartnerPatternPlus3.of_fixed_member_ge7 hm (Gaps.fundNoncentral 3) c hsingle D hβ ht hKβ
    hfix

end CFSG.ClassicalInvolution.Q3.Q3TD
