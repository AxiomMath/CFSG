module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNoTwo
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem stmtSmallBZeroOdd_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits) :
    StmtSmallBZeroOdd := by
  intro G _ _ p P M H R Rbar K hd _ z hz hB0 hodd hIso hExo _ hFi hLa
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  obtain ⟨hcardR, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa
  have hQz := hd.twoCore_inf_centralizer_le hNo2 hz hB0 hodd hIso hFi hcardR
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  have hexpR : ∀ r ∈ R, r ^ p = 1 := by
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hdec r hr
    have hc : Commute t (z ^ i) := Commute.pow_right
      (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
        (hRC (d1LiftX_le p H R K ht))) i
    rw [hc.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
      one_pow, one_mul]
  obtain ⟨T₁, hT₁, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  rcases hShape K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small with h2 | ⟨-, hZ⟩
  · have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup _) = p ^ 2 := by
      rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, h2]
    exact hd.false_of_ab hOrb hz hB0 hQz hdec hexpR hFi hExo hcard
  · exact hd.false_of_na hz hB0 hQz hdec hexpR hT₁ hZ

end CFSG.AGLEmbedding
