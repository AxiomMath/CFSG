module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.LocalAnalysis.SectionRank.QTK.A134Pi
import CFSG.LocalAnalysis.SectionRank.QTK.A134Defs

public section

namespace CFSG.SectionRank.QTK

open Subgroup
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def OddLocalWitness (S : Type) [Group S] [Finite S] : Prop :=
  ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup S) ∧ 1 ≤ localRank r S

theorem OddLocalWitness.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) (h : OddLocalWitness T) : OddLocalWitness S := by
  obtain ⟨r, hr, hr2, h2, h1⟩ := h
  refine ⟨r, hr, hr2, ?_, ?_⟩
  · rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact h2
  · rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
    exact h1

variable {S : Type} [Group S] [Finite S]

theorem exists_twoLocal_eq_localRank {r : ℕ} (hr : 1 < r) (h : 1 ≤ localRank r S) :
    ∃ R : Subgroup S, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      CFSG.Open.pRank r (normalizer (R : Set S)) = localRank r S := by
  set A := {k | ∃ H : Subgroup S, CFSG.Assembly.IsTwoLocal H ∧ CFSG.Assembly.pRank r H = k}
  have hbdd : BddAbove A := by
    refine ⟨Nat.card S, fun k hk => ?_⟩
    obtain ⟨H, -, rfl⟩ := hk
    refine csSup_le' fun j hj => ?_
    obtain ⟨F, -, -, hF⟩ := hj
    have h1 : j < r ^ j := Nat.lt_pow_self hr
    have h2 : Nat.card F ≤ Nat.card S := Subgroup.card_le_card_group F
    omega
  have hne : A.Nonempty := by
    by_contra hA
    rw [Set.not_nonempty_iff_eq_empty] at hA
    have h0 : localRank r S = 0 := by
      change sSup A = 0
      rw [hA, csSup_empty]
      rfl
    omega
  obtain ⟨H, ⟨R, hR, hR2, rfl⟩, hk⟩ := Nat.sSup_mem hne hbdd
  exact ⟨R, hR, hR2, hk⟩

theorem one_le_localRank_of_mem_normalizer {r : ℕ} (hr : 1 < r) {R : Subgroup S} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) {x : S} (hx : x ∈ normalizer (R : Set S)) (hxr : orderOf x = r) :
    1 ≤ localRank r S := by
  have hxp : x ^ r = 1 := by rw [← hxr]; exact pow_orderOf_eq_one x
  have h1 : 1 ≤ CFSG.Open.pRank r (normalizer (R : Set S)) :=
    le_pRank_of_le hr (zpowers_le.2 hx) (isElemAbelian_zpowers hxp)
      (by rw [Nat.card_zpowers, hxr, pow_one])
  refine h1.trans (le_csSup ⟨Nat.card S, fun k hk => ?_⟩ ⟨_, ⟨R, hR, hR2, rfl⟩, rfl⟩)
  obtain ⟨H, -, rfl⟩ := hk
  refine csSup_le' fun j hj => ?_
  obtain ⟨F, -, -, hF⟩ := hj
  have h3 : j < r ^ j := Nat.lt_pow_self hr
  have h4 : Nat.card F ≤ Nat.card S := Subgroup.card_le_card_group F
  omega

theorem not_bound_of_oddLocalWitness (h : OddLocalWitness S) :
    ¬ ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ R : Subgroup S, R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank r (normalizer (R : Set S)) + CFSG.Open.pRank r (⊤ : Subgroup S) ≤ 2 := by
  intro hb
  obtain ⟨r, hr, hr2, h2, h1⟩ := h
  obtain ⟨R, hR, hR2, hk⟩ := exists_twoLocal_eq_localRank hr.one_lt h1
  have := hb r hr hr2 R hR hR2
  omega

theorem oddLocalWitness_of_two_le_localRank {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : 2 ≤ localRank r S) : OddLocalWitness S := by
  have h1 : 1 ≤ localRank r S := le_trans (by norm_num) h
  refine ⟨r, hr, hr2, ?_, h1⟩
  obtain ⟨R, -, -, hk⟩ := exists_twoLocal_eq_localRank hr.one_lt h1
  obtain ⟨E, hEN, hE, hEc⟩ := exists_eq_pRank hr.one_lt (normalizer (R : Set S))
  have := le_pRank_of_le hr.one_lt (le_top : E ≤ ⊤) hE hEc
  omega

end CFSG.SectionRank.QTK
