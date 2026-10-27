module

public import CFSG.ClassicalInvolution.Q3.Q3WATwinDRow
public import CFSG.ClassicalInvolution.Q3.Q3TY8
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.RouteD.TypeDChain
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.Q3.Q3TY5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

@[expose] def PartnerPatternPlus3 {G : Type} [Group G] (m : ℕ) (Ω : Set (Subgroup G))
    (K β : Subgroup G) (t : G) : Prop :=
  PartnerPatternD 3 1 m Ω K β t

section Chain

variable {G : Type} [Group G] [Finite G]

theorem chain_of_patternD3 {m : ℕ} (hm : 4 ≤ m) (hMFZ : Gaps.FundNoncentral 3) {K : Subgroup G}
    {z : G} (c : TCtx3 .POmegaPlus m (conjClass3 K) K z)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    {β : Subgroup G} (hβ : β ∈ conjClass3 K) {t : G} (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hpat : PartnerPatternPlus3 m (conjClass3 K) K β t) :
    ∃ U : Fin (m + 2) → Subgroup G, (∀ k, U k ∈ conjClass3 K) ∧
      (∀ i j : Fin (m + 2), i ≠ j → ¬ edgeD (m + 2) i j → ¬ edgeD (m + 2) j i →
        Commutes (U i) (U j)) ∧
      ∀ i j : Fin (m + 2), edgeD (m + 2) i j →
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j) := by
  obtain ⟨j, hjΩ, hjK, hjt, hjc, hjp, hβj0⟩ := hpat
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hβj : ∀ a : Fin m, 1 ≤ a.val → Commutes β (j a) := fun a ha =>
    c.commutes_partner_of_centralizes3 hMFZ hsingle D hβ ht hKβ
      (mem_centralizingMembers_of_commutes (hjΩ a) c.hz.mem (hjK a).symm) (hjt a ha) (hjK a)
  obtain ⟨hcomm, hpair⟩ := twinChain_relations_D (p := 3) (f := 1) hm hjK hβj hjc hjp hKβ hβj0
  refine ⟨twinChain K β j, ?_, hcomm, hpair⟩
  intro k
  by_cases h0 : k.val = 0
  · rw [twinChain_zero K β j h0]
    exact hK
  · by_cases h1 : k.val = 1
    · rw [twinChain_one K β j h1]
      exact hβ
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, k.val = a.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_node K β j ha]
      exact hjΩ a

end Chain

section Rows

@[expose] def PartnerPatternStmtD3 (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .POmegaPlus m) (conjClass3 K) z →
      ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        HasFixedMember (conjClass3 K) K β z → PartnerPatternPlus3 m (conjClass3 K) K β t

@[expose] def ChainPiece3TwinDOn (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ N : ℕ, 6 ≤ N → P N →
      LocalShapeC3 2 (CompData.model .POmegaPlus (N - 2)) (conjClass3 K) z →
      ∃ U : Fin N → Subgroup G, (∀ k, U k ∈ conjClass3 K) ∧
        (∀ i j : Fin N, i ≠ j → ¬ edgeD N i j → ¬ edgeD N j i → Commutes (U i) (U j)) ∧
        ∀ i j : Fin N, edgeD N i j →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)

theorem chainPiece3TwinDOn_of_pattern {P : ℕ → Prop} (h3 : OddThreeFreeInput)
    (hpat : ∀ N, 6 ≤ N → P N → PartnerPatternStmtD3 (N - 2)) : ChainPiece3TwinDOn P := by
  intro G _ _ _ hnab K z hR N hN hPN hshape0
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hm2 : m + 2 - 2 = m := by omega
  have hm : 4 ≤ m := by omega
  have hshape : LocalShapeC3 2 (CompData.model .POmegaPlus m) (conjClass3 K) z := by
    rw [hm2] at hshape0
    exact hshape0
  have hadm : StatedLieAdmissible .POmegaPlus m 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ m; omega⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_plus hm hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ :=
    c.exists_partner hsingle (nonempty_fund_plus (p := 3) (f := 1) hm)
  obtain ⟨ι, hι, D, hcard, -⟩ := id hshape
  have hpat' : PartnerPatternStmtD3 m := by
    have := hpat (m + 2) hN hPN
    rwa [hm2] at this
  exact chain_of_patternD3 hm (Gaps.fundNoncentral 3) c hsingle D hβ ht hKβ
    (hpat' G hnab K z hR hshape β hβ t ht hKβ hfix)

theorem chainPiece3TwinD_of_on {P : ℕ → Prop} (h1 : ChainPiece3TwinDOn P)
    (h2 : ChainPiece3TwinDOn fun N => ¬ P N) : ChainPiece3TwinD :=
  fun G _ _ _ hnab K z hR N hN hshape => by
    by_cases hPN : P N
    · exact h1 G hnab K z hR N hN hPN hshape
    · exact h2 G hnab K z hR N hN hPN hshape

theorem chainPiece3TwinD_of_pattern (h3 : OddThreeFreeInput)
    (hpat : ∀ m, 4 ≤ m → PartnerPatternStmtD3 m) : ChainPiece3TwinD :=
  chainPiece3TwinD_of_on (P := fun _ => True)
    (chainPiece3TwinDOn_of_pattern h3 fun N hN _ => hpat (N - 2) (by omega))
    (chainPiece3TwinDOn_of_pattern h3 fun _ _ h => absurd trivial h)

end Rows

end CFSG.ClassicalInvolution.Q3.Q3TD
