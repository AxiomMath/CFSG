module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamAModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamASylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisArith

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

theorem heisFamA_two_le_padicValNat {p f f₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hf₀ : f = p * f₀) :
    2 ≤ padicValNat p ((2 ^ f) ^ orderOf ((2 ^ f : ℕ) : ZMod p) - 1) := by
  have hf0 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · rw [h, mul_zero] at hf₀
      omega
    · exact h
  have hc : ¬ p ∣ 2 ^ f₀ := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hc1 : 2 ≤ 2 ^ f₀ :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf0
  have h := heis_two_le_padicValNat hp hc hc1
  have heq : (2 ^ f₀) ^ p = 2 ^ f := by rw [← pow_mul, hf₀, mul_comm]
  rw [heq] at h
  exact h

theorem heisCoreOn_idxA_of_rank_facts
    (hF : HeisARankFacts) : HeisCoreOn IdxA := by
  intro L _ _ hperf hodd hrk hsimple d hd e p hp hp5
  left
  obtain ⟨n, f, hn, hf, hmodel, ⟨eX⟩⟩ := heisFamA_model d hd e
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨hgcd, hlt, hZ⟩ :=
    hF L hperf hodd hrk hsimple n f (GaloisField 2 f) hcard hn hf eX p hp hp5
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hCyc, hout⟩ := heis_out_data hp hp5 hmodel (by decide) (fun _ => hgcd)
    (fun h => absurd h (by decide))
  haveI := hperf
  haveI := hsimple
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hcard]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hgcd' : ¬ p ∣ Nat.gcd n (Nat.card (GaloisField 2 f) - 1) := by rwa [hcard]
  have hlt' : n / orderOf (Nat.card (GaloisField 2 f) : ZMod p) < p := by rwa [hcard]
  have hX := heisSylGood_sylow_of_mulEquiv eX (heisFamA_sylow_psl hp hp2 hpK (by omega) hgcd' hlt')
  refine noHeisAut_of_abelian_sylow hp hp5 (heis_conj_injective L) hCyc
    (heis_rank_quotient hrk hp hp2 hZ) fun S => ?_
  obtain ⟨h1, h2⟩ := (hX S).mem
  refine ⟨h1, fun hα => Or.inr (h2 ?_)⟩
  obtain ⟨f₀, hf₀⟩ := hout hα
  rw [hcard]
  exact heisFamA_two_le_padicValNat hp hp2 hf hf₀

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
