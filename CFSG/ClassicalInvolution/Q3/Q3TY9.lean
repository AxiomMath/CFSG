module

public import CFSG.ClassicalInvolution.Q3.Q3TY8
public import CFSG.ClassicalInvolution.Q3.Q3TWRowTD
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.Q3.Q3TY5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.Q3.Q3TW
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups


@[expose] def PartnerPatternMinus3 {G : Type} [Group G] (m : ℕ) (Ω : Set (Subgroup G))
    (K β : Subgroup G) (t : G) : Prop :=
  ∃ j : Fin (m - 1) → Subgroup G, (∀ a, Commutes K (j a)) ∧
    (∀ a : Fin (m - 1), a.val + 2 < m → j a ∈ Ω) ∧
    (∀ a : Fin (m - 1), ¬ a.val + 2 < m → j a ≤ ⁅j a, j a⁆) ∧
    (∀ a : Fin (m - 1), 1 ≤ a.val → j a ≤ Subgroup.centralizer ({t} : Set G)) ∧
    (∀ a b : Fin (m - 1), a.val + 1 < b.val → ∀ u ∈ j a, ∀ v ∈ j b, u * v = v * u) ∧
    (∀ a b : Fin (m - 1), a.val + 1 = b.val → b.val + 2 < m →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b)) ∧
    (∀ a b : Fin (m - 1), a.val + 3 = m → b.val + 2 = m →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (j a) (j b)) ∧
    (∀ a : Fin (m - 1), a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β (j a))

variable {G : Type} [Group G] [Finite G]

theorem chain_of_pattern3 {N : ℕ} (hN : 6 ≤ N) (hMFZ : Gaps.FundNoncentral 3) {K : Subgroup G}
    {z : G} (c : TCtx3 .POmegaMinus (N - 2) (conjClass3 K) K z)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K) {ι : Type} [Finite ι]
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    (hD : Nat.card ι ≤ 4) {β : Subgroup G} (hβ : β ∈ conjClass3 K) {t : G}
    (ht : IsClassicalMember3 β t) (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hpat : PartnerPatternMinus3 (N - 2) (conjClass3 K) K β t) :
    ∃ U : Fin (N - 1) → Subgroup G, U (twIdx0 (by omega : 3 ≤ N)) ∈ conjClass3 K ∧
      (∀ i j : Fin (N - 1), i.val + 1 < j.val → Commutes (U i) (U j)) ∧
      (∀ i j : Fin (N - 1), i.val + 1 = j.val → j.val + 2 < N →
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
      ∀ i j : Fin (N - 1), i.val + 3 = N → j.val + 2 = N →
        ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (U i) (U j) := by
  have hn3 : 3 ≤ N := by omega
  obtain ⟨j, hjK, hjΩ, hjperf, hjt, hjcomm, hjpair, hjtw, hβj⟩ := hpat
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hβj' : ∀ i : Fin (N - 2 - 1), 1 ≤ i.val → Commutes β (j i) := by
    intro i hi
    by_cases hlong : i.val + 2 < N - 2
    · exact c.commutes_partner_of_centralizes3 hMFZ hsingle D hβ ht hKβ
        (mem_centralizingMembers_of_commutes (hjΩ i hlong) c.hz.mem (hjK i).symm) (hjt i hi)
        (hjK i)
    · exact c.commutes_partner_of_perfect3 hMFZ hsingle D hD hβ ht
        (le_antisymm (commutator_self_le _) (hjperf i hlong)) (hjt i hi)
  let U : Fin (N - 1) → Subgroup G := fun k =>
    if h0 : k.val = 0 then K else if h1 : k.val = 1 then β else j ⟨k.val - 2, by omega⟩
  have hU0 : U (twIdx0 hn3) = K := by simp [U, twIdx0]
  have hU1 : U (twIdx1 hn3) = β := by simp [U, twIdx1]
  have hUj : ∀ k : Fin (N - 1), (h : 2 ≤ k.val) → U k = j ⟨k.val - 2, by omega⟩ := by
    intro k h
    simp only [U]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  refine ⟨U, by rw [hU0]; exact hK, ?_, ?_, ?_⟩
  · intro a b hab u hu v hv
    rcases Nat.lt_or_ge a.val 2 with ha | ha
    · rcases Nat.lt_or_ge a.val 1 with ha0 | ha1
      · obtain rfl : a = twIdx0 hn3 := Fin.ext (by simp only [twIdx0]; omega)
        rw [hU0] at hu
        rw [hUj b (by omega)] at hv
        exact hjK _ u hu v hv
      · obtain rfl : a = twIdx1 hn3 := Fin.ext (by simp only [twIdx1]; omega)
        rw [hU1] at hu
        rw [hUj b (by omega)] at hv
        exact hβj' ⟨b.val - 2, by omega⟩ (by simp only; omega) u hu v hv
    · rw [hUj a ha] at hu
      rw [hUj b (by omega)] at hv
      exact hjcomm _ _ (by simp only; omega) u hu v hv
  · intro a b hab hb
    rcases Nat.lt_or_ge a.val 2 with ha | ha
    · rcases Nat.lt_or_ge a.val 1 with ha0 | ha1
      · obtain rfl : a = twIdx0 hn3 := Fin.ext (by simp only [twIdx0]; omega)
        obtain rfl : b = twIdx1 hn3 := Fin.ext (by simp only [twIdx0, twIdx1] at hab ⊢; omega)
        rw [hU0, hU1]
        exact hKβ
      · obtain rfl : a = twIdx1 hn3 := Fin.ext (by simp only [twIdx1]; omega)
        rw [hU1, hUj b (by simp only [twIdx1] at hab; omega)]
        have hb0 : (⟨b.val - 2, by omega⟩ : Fin (N - 2 - 1)) = ⟨0, by omega⟩ :=
          Fin.ext (by simp only [twIdx1] at hab ⊢; omega)
        rw [hb0]
        exact hβj ⟨0, by omega⟩ rfl
    · rw [hUj a ha, hUj b (by omega)]
      exact hjpair _ _ (by simp only; omega) (by simp only; omega)
  · intro a b ha hb
    rw [hUj a (by omega), hUj b (by omega)]
    exact hjtw _ _ (by simp only; omega) (by simp only; omega)


section Rows


@[expose] def PartnerPatternStmt3 (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .POmegaMinus m) (conjClass3 K) z →
      ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        HasFixedMember (conjClass3 K) K β z → PartnerPatternMinus3 m (conjClass3 K) K β t

@[expose] def ChainPiece3TwinTDOn (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (N : ℕ) (hN : 6 ≤ N), P N →
      LocalShapeC3 2 (CompData.model .POmegaMinus (N - 2)) (conjClass3 K) z →
      ∃ U : Fin (N - 1) → Subgroup G, U (twIdx0 (by omega : 3 ≤ N)) ∈ conjClass3 K ∧
        (∀ i j : Fin (N - 1), i.val + 1 < j.val → Commutes (U i) (U j)) ∧
        (∀ i j : Fin (N - 1), i.val + 1 = j.val → j.val + 2 < N →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
        ∀ i j : Fin (N - 1), i.val + 3 = N → j.val + 2 = N →
          ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (U i) (U j)

theorem chainPiece3TwinTDOn_of_pattern {P : ℕ → Prop} (h3 : OddThreeFreeInput)
    (hMFZ : Gaps.FundNoncentral 3) (hpat : ∀ N, 6 ≤ N → P N → PartnerPatternStmt3 (N - 2)) :
    ChainPiece3TwinTDOn P := by
  intro G _ _ _ hnab K z hR N hN hPN hshape
  have hm : 4 ≤ N - 2 := by omega
  have hadm : StatedLieAdmissible .POmegaMinus (N - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ N - 2; omega⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_minus hm hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner hsingle (nonempty_fund_minus3 hm)
  obtain ⟨ι, hι, D, hcard, -⟩ := id hshape
  have : Finite ι := hι
  have hD : Nat.card ι ≤ 4 := by omega
  exact chain_of_pattern3 hN hMFZ c hsingle D hD hβ ht hKβ
    (hpat N hN hPN G hnab K z hR hshape β hβ t ht hKβ hfix)

theorem chainPiece3TwinTD_of_on {P : ℕ → Prop} (h1 : ChainPiece3TwinTDOn P)
    (h2 : ChainPiece3TwinTDOn fun N => ¬ P N) : ChainPiece3TwinTD :=
  fun G _ _ _ hnab K z hR N hN hshape => by
    by_cases hPN : P N
    · exact h1 G hnab K z hR N hN hPN hshape
    · exact h2 G hnab K z hR N hN hPN hshape

end Rows

end CFSG.ClassicalInvolution.Q3.Q3TY
