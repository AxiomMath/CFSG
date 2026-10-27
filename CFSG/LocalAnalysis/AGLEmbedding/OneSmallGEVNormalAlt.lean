module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormal
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltOuter
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltToral
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1SmallAltConfig.false {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}
    (hc : D1SmallAltConfig p P M H R Rbar K z) (hB : D1AltBlockInputs)
    (hOrb : KFactSmallOrbits) : False := by
  obtain ⟨L, hL⟩ := hc.phase.exists_weakSBlock hB.h84 hB.hD2
  rcases hc.split hB hOrb hL with hR | ⟨hBL, hTC | hBC⟩
  · exact hc.false_of_le_rPart hB hL hR
  · exact hc.false_of_d1LiftX_le hB hOrb hL hBL hTC
  · exact hc.false_of_rPart_eq_bot hB hL hBL hBC

theorem d1SmallGEVNormalAlt_of (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hΓ : KFactAltTwoPGamma) (hOP : KFactBlockOutPrime) (hAI : KFactBlockAutAltInner)
    (hOR : KFactBlockOutRankAlt) (hTA : KFactBlockToralAlt) (hC3T : CitedBlockThreeToralAlt) :
    D1SmallGEVNormalAlt := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 _ _ hFi hAlt _ _ _ hCz _ hnorm hp5 hA
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have hp57 : p = 5 ∨ p = 7 := by
    have h11 : p < 11 := by
      by_contra h
      exact hAlt ⟨hA, by omega, Or.inl (by omega)⟩
    interval_cases p <;> first | (left; rfl) | (right; rfl) | exact absurd hp (by decide)
  have hL : ¬ (p = 3 ∧ IsLinThreeFour K) := fun h => by omega
  have hLa : D1SmallLa p M H Rbar K := fun h3 => absurd h3 (by omega)
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa
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
  obtain ⟨T₁, -, hs, hn, hcat, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hcfg : D1SmallAltConfig p P M H R Rbar K z :=
    { data := hd
      elt := hz
      ia := hI
      b0 := hB0
      cz_le := hCz
      normal := hnorm
      prime57 := hp57
      alt := hA
      not_fi22 := hFi
      phase := hd.toPhaseThree hUP hL hFi
      dec := hdec
      exp := hexpR
      rbar_le := hd.rbar_le_sup_centralizer hOut hLa
      out := hSch K hs hn hcat
      uprime := hUP K hs hn hcat p hp hp2 T₁ hTnc hΓT hd.small hL hFi }
  exact hcfg.false ⟨h84, h85, h86, h93, hD2, hK2, hC3, hK5, hΓ, hOP, hAI, hOR, hTA, hC3T⟩ hOrb

end CFSG.AGLEmbedding
