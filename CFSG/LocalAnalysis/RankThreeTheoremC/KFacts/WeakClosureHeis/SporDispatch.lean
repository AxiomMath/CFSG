module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def SDSporAt (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* NativeSporadic.Carrier s) → SylowDichotomyAt K p

section Dispatch


theorem sdSpor_offPair (hBM : SporadicBMData) (s : TauCeti.SporadicName) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hnot : ¬ SporadicOnePair s p) : SDSporAt s p := by
  intro K _ _ ⟨e⟩
  have hcard : Nat.card K = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
  have hN : Nat.card K ≠ 0 := Nat.card_pos.ne'
  apply SylowDichotomyAt.of_factorization_le
  rcases offPair_carrier hBM s p hp (by omega) hnot with h | ⟨h, -⟩
  · by_contra hlt
    exact h (hcard ▸ (hp.pow_dvd_iff_le_factorization hN).2 (by omega))
  · by_contra hlt
    exact h (hcard ▸ (hp.pow_dvd_iff_le_factorization hN).2 (by omega))

theorem sdSpor_of_pairs (hBM : SporadicBMData) (hHN : SDSporAt .HN 5) (hLy : SDSporAt .Ly 5)
    (hCo1 : SDSporAt .Co1 5) (hB : SDSporAt .B 5) (hM5 : SDSporAt .M 5) (hM7 : SDSporAt .M 7) :
    SDSpor := by
  intro K _ _ hs hnab ⟨s, ⟨e⟩⟩ p hp h5 hpK
  by_cases hone : SporadicOnePair s p
  · rcases hone with ⟨h3, -⟩ | ⟨hp5, hs'⟩ | ⟨hp7, hs'⟩
    · omega
    · subst hp5
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl | rfl | rfl | rfl
      · exact hCo1 K ⟨e⟩
      · exact hHN K ⟨e⟩
      · exact hLy K ⟨e⟩
      · exact hB K ⟨e⟩
      · exact hM5 K ⟨e⟩
    · subst hp7
      subst hs'
      exact hM7 K ⟨e⟩
  · exact sdSpor_offPair hBM s hp h5 hone K ⟨e⟩

end Dispatch

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
