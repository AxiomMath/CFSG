module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankSpanNormal
public import CFSG.Assembly.BalancedOddCoreCompletion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.Dichotomy

theorem connected_derived_involution_unbalancing_triple {G : Type} [Group G] [Finite G]
    (hconn : LargeEvenClassification.Conn3 G) :
    (∀ t : G, orderOf t = 2 → t ∈ commutator G →
      ¬ (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ≤
        pPrimeCore 2 G →
      ∃ (a x : G) (J : Subgroup G), orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
        GSUnbalancingTriple a x J) ∧
    (Group.IsPerfect G → (∃ t : G, orderOf t = 2 ∧
        ¬ (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ≤
          pPrimeCore 2 G) →
      ∃ (a x : G) (J : Subgroup G), orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
        GSUnbalancingTriple a x J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmain : ∀ t : G, orderOf t = 2 → t ∈ commutator G →
      ¬ (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ≤
        pPrimeCore 2 G →
      ∃ (a x : G) (J : Subgroup G), orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
        GSUnbalancingTriple a x J := by
    intro t ht htG hunb
    by_contra hno
    have hinv : ∀ a : G, involutionOddCore a =
        (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype :=
      fun a => by rw [involutionOddCore, Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    have hbal : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
        involutionOddCore a ⊓ centralizer ({b} : Set G) ≤ involutionOddCore b := by
      intro a b ha hb hab
      rcases commuting_involution_odd_core_unbalancing_triple hb ha hab.symm with h | ⟨J, hJ⟩
      · rw [hinv, hinv]
        exact h
      · exact (hno ⟨b, a, J, hb, ha, hab.symm, hJ⟩).elim
    have hcomp : ∀ D ∈ LargeEvenClassification.E3 G, Odd (Nat.card (oddCoreSpan D)) ∧
        D ≤ normalizer (oddCoreSpan D : Set G) ∧
        ∀ d ∈ D, d ≠ 1 → oddCoreSpan D ⊓ centralizer ({d} : Set G) = involutionOddCore d := by
      intro D hD
      obtain ⟨hDe, hD8⟩ := hD
      have hinvD : ∀ d ∈ D, d ≠ 1 → orderOf d = 2 := fun d hd hne =>
        orderOf_eq_prime (hDe.2 d hd) hne
      have hcommD : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d := fun d hd e he =>
        congrArg Subtype.val (hDe.1.is_comm.comm (⟨d, hd⟩ : D) ⟨e, he⟩)
      obtain ⟨⟨h1, h2, h3⟩, -⟩ := balanced_oddCoreSpan_completed D hDe (by rw [hD8])
        fun a ha hne b hb hne' => hbal a b (hinvD a ha hne) (hinvD b hb hne') (hcommD a ha b hb)
      exact ⟨h2, h1, h3⟩
    have hspan := UnbalancedGS.connected_completed_odd_core_span_normal hconn hcomp
    obtain ⟨A, hA⟩ := hconn.1
    have hrank : 3 ≤ Open.twoRank G :=
      SectionRank.le_pRank (p := 2) one_lt_two (le_top : A ≤ ⊤) hA.1 (by rw [hA.2]; norm_num)
    obtain ⟨E, hE, hE8, htE⟩ :=
      ProperTwoGeneratedCore.derived_involution_rank_three_coverage hrank t ht htG
    have hEmem : E ∈ LargeEvenClassification.E3 G := ⟨hE, hE8⟩
    have hEO : oddCoreSpan E ≤ pPrimeCore 2 G := by
      unfold pPrimeCore
      exact le_sSup ⟨(hspan E hEmem).1, Nat.coprime_two_left.mpr (hcomp E hEmem).1⟩
    have ht1 : t ≠ 1 := fun h => by
      rw [h, orderOf_one] at ht
      exact absurd ht (by norm_num)
    apply hunb
    rw [← hinv t, ← (hcomp E hEmem).2.2 t htE ht1]
    exact inf_le_left.trans hEO
  refine ⟨hmain, fun hperf hex => ?_⟩
  obtain ⟨t, ht, hunb⟩ := hex
  exact hmain t ht (by rw [hperf.commutator_eq_top]; exact mem_top t) hunb

end CFSG.ComponentClassification.UnbalancedCorr
