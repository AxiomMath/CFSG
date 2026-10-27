module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineTwelveOneCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionAutomizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem kFactNineThreeAutSection_of
    (hlin : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ (V : Type) [Group V] [Finite V], IsPGroup q V →
      Open.pRank q (⊤ : Subgroup V) ≤ 3 → HasSmallLinearModel q V)
    (hauto : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → AutomizerBound p q)
    (hent : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ i : TauCeti.CFSGIndex, IsNineThreeIndex p i →
      ¬ (p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .suzuki 2) →
      ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → ¬ SmallAutomizer p K)
    (hSz : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 → ∀ d : TauCeti.ValidLieTypeIndex,
      d.1 = .suzuki 2 → ∀ (V : Type) [Group V] [Finite V], IsPGroup q V →
      Open.pRank q (⊤ : Subgroup V) ≤ 3 →
      ∀ (A : Subgroup (MulAut V)) (φ : ↥A →* (TauCeti.CFSGIndex.lie d).Group),
        ¬ Function.Surjective φ) :
    RankThreeTheoremC.KFactNineThreeAutSection := by
  intro p q hp hp2 hp3 hq hq2 hqp i hi V _ _ hV hr A φ hφ
  by_cases hSzi : p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .suzuki 2
  · obtain ⟨rfl, d, rfl, hd⟩ := hSzi
    exact hSz q hq hq2 hqp d hd V hV hr A φ hφ
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : Finite (MulAut V) := MulEquiv.finite_left
    haveI : Finite i.Group := Finite.of_surjective φ hφ
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h hp3
      · exact absurd (h ▸ hp) (by norm_num)
      · exact h
    exact hent p hp hp2 hp3 i hi hSzi i.Group ⟨MulEquiv.refl _⟩
      (smallAutomizer_of_surjective hp5 hqp.symm (hauto p q hp hq hqp.symm) (hlin q hq2 V hV hr)
        A φ hφ)

theorem automizerBound_holds {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    AutomizerBound p q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  intro W _ _ _ hW P hP hab g hg
  refine automizer_pow_three_or_four hW ?_ hP hab hg
  rw [Nat.card_zmod]
  exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)

theorem kFactNineThreeAutSection_of_entries
    (hent : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ i : TauCeti.CFSGIndex, IsNineThreeIndex p i →
      ¬ (p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .suzuki 2) →
      ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → ¬ SmallAutomizer p K)
    (hSz : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 → ∀ d : TauCeti.ValidLieTypeIndex,
      d.1 = .suzuki 2 → ∀ (V : Type) [Group V] [Finite V], IsPGroup q V →
      Open.pRank q (⊤ : Subgroup V) ≤ 3 →
      ∀ (A : Subgroup (MulAut V)) (φ : ↥A →* (TauCeti.CFSGIndex.lie d).Group),
        ¬ Function.Surjective φ) :
    RankThreeTheoremC.KFactNineThreeAutSection :=
  kFactNineThreeAutSection_of (fun _ _ hq2 _ _ _ hV hr => hasSmallLinearModel hq2 hV hr)
    (fun _ _ hp hq hpq => automizerBound_holds hp hq hpq) hent hSz

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
