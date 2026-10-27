module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGTwoSetup
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGTwoModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrPow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo


theorem parabIrrOn_idxG2_of (hGA : CFSG.Open.GriessAllModelsStatement) :
    ParabIrrOn (IsLieOf IdxG2) := by
  intro G _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hBp hBnc hBY hBP hW hNY hNP hNB hirr
  left
  obtain ⟨f, hf, A, i, aut, hBA, hI, hA, hWA, hker⟩ := exists_g2_model hGA hY h2 hF hpar hne hna
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpow : ∀ n (hn : n ∈ N), ∃ e : ℤ, ActsAsPow aut B hBY ⟨n, hNY hn⟩ e := by
    intro n hn
    obtain ⟨k, hk⟩ := g2_model_pow hf hK hBA hI (hA ⟨n, hNY hn⟩ (hNP hn))
    refine ⟨((2 ^ k : ℕ) : ℤ), actsAsPow_of_two_pow (ρ := aut) hp hp2 hBY hBp ?_ _ ?_⟩
    · intro b hb
      exact (Subgroup.mem_normalizer_iff.1 (hNB hn) b).1 hb
    · intro b hb
      obtain ⟨j, hj⟩ := hk (aut ⟨b, hBY hb⟩) (hA _ (hBP hb)) (hWA _ (hBP hb) (hW b hb))
      exact ⟨j, by rwa [zpow_natCast]⟩
  have h1 := forall_eq_one_of_actsAsPow hBY hNY hBnc hirr hNB hpow
  intro b hb y hy
  exact hker ⟨b, hBY hb⟩ (h1 b hb) y hy

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
