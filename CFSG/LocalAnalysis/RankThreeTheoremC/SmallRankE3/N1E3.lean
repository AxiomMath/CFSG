module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4P65Seven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFactP65RankThreeS KFactP65RankTwoS)

namespace N1

theorem stepP65OddFive_of_kfactsE3 (hK1 : KFactP65RankThreeS) (hK2 : KFactP65RankTwoS)
    (hK3 : KFactP65SingleE3) (hβ : NoTwoComponentsE3) : StepP65OddFive := by
  intro G _ _ hSet hD1 P M hsit x z hx hz F hF1 hFM hcop5 hodd hBF
  have hU0 : FullCoreLocal G := fullCoreLocal_of_theoremD1_situation_five hSet hD1 hsit
  have hS : Sit G 5 P M := ⟨hSet, hU0, hsit, le_rfl⟩
  refine p65_engineAt (hK1 G hSet) (hK2 G hSet) hK3.toAt hβ.toAt hS hx hz ?_ hF1 hFM hcop5 hodd hBF
  intro f F Fs R hf hf2 hfp _ _ _ hFsM hFsp _ _ _ _ _ hM2 hRH hR3 hcyc
  have hprime : (5 : ℕ).Prime := Nat.prime_five
  obtain ⟨hDM, hMD, hDp⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 5 M
  have hX3 : Open.pRank f M ≤ 3 :=
    (local_pRank_le_evenRank f hf hf2 M hS.isTwoLocal).trans hSet.rank.le
  have hX7 : 7 ≤ f → Open.pRank f M ≤ 2 := fun h7 =>
    pRank_le_two_of_five_mem hSet.rank hsit.mem_sigmaA hf (by omega) hS.isTwoLocal
  exact lemma69_e3 (X := M) (D := rankThreePrimeCore 5 M) (Fs := Fs) (R := R) rfl hf hf2 hfp
    (fun N _ hN => hS.eq_top_of_isPGroup_quotient N hN) hDM
    (fun y hy d hd => (mem_normalizer_iff.mp (hMD hy) d).mp hd)
    ((Nat.Prime.coprime_iff_not_dvd hprime).mp hDp)
    hFsp hFsM hM2 hRH hR3 hcyc hX3 hX7

theorem slotProp65Five_of_kfactsE3 (hK1 : KFactP65RankThreeS) (hK2 : KFactP65RankTwoS)
    (hK3 : KFactP65SingleE3) (hβ : NoTwoComponentsE3) : SlotProp65Five :=
  slotProp65Five_of_stepP65OddFive (stepP65OddFive_of_kfactsE3 hK1 hK2 hK3 hβ)

end N1

theorem stepP65OddSevenU0_of_clauseBE3 (hclB : P65ClauseBResidue) (hK1 : KFactP65RankThreeS)
    (hK2 : KFactP65RankTwoS) (hKA : ∀ p : ℕ, 7 ≤ p → N1.KFactP65SingleAt p)
    (hβ : ∀ p : ℕ, 7 ≤ p → N1.NoTwoComponentsAt p) : StepP65OddSevenU0 := by
  intro G _ _ hS hD1 hU0 p hp7 P M hsit x z hx hz F hF1 hFM hcop hodd hBF
  have hSit : N1.Sit G p P M := ⟨hS, hU0, hsit, by omega⟩
  exact N1.p65_engineAt (hK1 G hS) (hK2 G hS) (hKA p hp7) (hβ p hp7) hSit hx hz
    (p65AfterLemma68_of_clauseB hclB hS hD1 hU0 hp7 hsit hx hz) hF1 hFM hcop hodd hBF

theorem stepP65OddSevenU0_of_kfactsE3 (hK1 : KFactP65RankThreeS) (hK2 : KFactP65RankTwoS)
    (hKA : ∀ p : ℕ, 7 ≤ p → N1.KFactP65SingleAt p)
    (hβ : ∀ p : ℕ, 7 ≤ p → N1.NoTwoComponentsAt p) : StepP65OddSevenU0 :=
  stepP65OddSevenU0_of_clauseBE3 (p65ClauseBResidue_of_kfactS hK1) hK1 hK2 hKA hβ

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
