module



public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.LocalAnalysis.RankThreeUC.WitnessNoncyclicUniqueness
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NonTI.NonTIHelpers
public import CFSG.LocalAnalysis.RankThreeUC.NormalModules

public section


namespace CFSG.LocalAnalysis.RankThreeUC


namespace Section12


namespace NoncyclicCentralizerTI


variable {G : Type} [Group G] [Finite G]


theorem isTI_of_one_lt_pRank_centralizer {M T V : Subgroup G} (hc : Context G M T)
    (hV : V ∈ normalElemAbelian2 M) {p : ℕ} (hp : p ∈ SourceSetting.sigmaOf G M)
    (hrank : 1 < CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (V : Set G))) :
    CFSG.CGT.Timmesfeld75.IsTI V := by
  obtain ⟨-, hVab, hVM, hMn⟩ := mem_normalElemAbelian2.mp hV
  obtain ⟨q, P, -, -, hw⟩ := SourceSetting.IsInMSigma.exists hc.mSigma
  have hMmax : CFSG.Open.rankThreeIsMaxTwoLocal M := hw.maxLocal
  have hpprime : p.Prime := by
    have h := hp.1
    unfold CFSG.Open.rankThreeSigmaA at h
    simp only at h
    split_ifs at h <;> exact h.1
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨E, hEH, hE, hcard⟩ : ∃ E : Subgroup G, E ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
      CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (V : Set G)) := by
    set S := {k | ∃ E : Subgroup G, E ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} with hS
    have hdef : CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (V : Set G)) = sSup S := rfl
    have hmem : CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (V : Set G)) ∈ S := by
      rw [hdef] at hrank ⊢
      by_cases hb : BddAbove S
      · have hne : S.Nonempty := by
          by_contra hne
          rw [Set.not_nonempty_iff_eq_empty] at hne
          rw [hne, csSup_empty] at hrank
          exact absurd hrank (by norm_num)
        exact Nat.sSup_mem hne hb
      · rw [Nat.sSup_of_not_bddAbove hb] at hrank
        exact absurd hrank (by norm_num)
    obtain ⟨E, hE1, hE2, hE3⟩ := hmem
    exact ⟨E, hE1, hE2, hE3⟩
  have hpE : IsPGroup p E := by
    rw [IsPGroup.iff_card]
    exact ⟨_, hcard⟩
  have hnc : ¬ IsCyclic E := by
    intro hcyc
    have hexp : Monoid.exponent E ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g
      exact Subtype.ext (by simpa using hE.2 (g : G) g.2)
    have h1 : Nat.card E ≤ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact Nat.le_of_dvd hpprime.pos hexp
    have hk : 1 < CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (V : Set G)) := hrank
    have h2 : p ^ 2 ≤ p ^ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (V : Set G)) :=
      Nat.pow_le_pow_right hpprime.pos hk
    rw [hcard] at h1
    have h3 : 2 ≤ p := hpprime.two_le
    nlinarith
  have hXM : E ≤ M := le_trans hEH inf_le_left
  have hmax : SourceSetting.maxTwoLocalsContaining E = {M} :=
    WitnessNoncyclicUniqueness.maxTwoLocalsContaining_eq_singleton hp hMmax hXM hpE hnc
  have huniq : ∀ N, CFSG.Open.rankThreeIsMaxTwoLocal N →
      M ⊓ Subgroup.centralizer (V : Set G) ≤ N → N = M := by
    intro N hN hle
    have hNmem : N ∈ SourceSetting.maxTwoLocalsContaining E :=
      ⟨hN, le_trans hEH hle⟩
    rw [hmax] at hNmem
    exact hNmem
  exact NonTI.isTI_of_unique hMmax hVM hMn hVab huniq


end NoncyclicCentralizerTI

end Section12

end CFSG.LocalAnalysis.RankThreeUC
