module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSide
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
public import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section MSide

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.primeCore_inf_eq_of_uPrime (hd : D1OneSmallData p P M H R Rbar K)
    (hU : KFactUPrime p K) : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H := by
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  exact hd.cfg.ext.primeCore_inf_eq_iff.mpr (hd.cfg.red.primeComplementCore_eq_bot_of_uPrimeHyp
    (hd.cfg.red.uPrimeHyp_of_rankOne hd.comp hd.noncyclic hzR hzK hzp hzc hU))

theorem D1OneSmallData.false_of_four_le_pRank (h3 : D1PhaseThree p P M H R)
    (hU : KFactUPrime p K) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p)
    (h4 : 4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)) : False :=
  h3.false_of_four_le_pRank_of_primeCore (hd.primeCore_inf_eq_of_uPrime hU) h84 hD2 hs hs2 hsp h4

theorem D1OneSmallData.le_centralizer_pCore (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K)
    (hYX : pCorePreimage p M ⊓ d1LiftX p H R K = ⊥) :
    barM M (d1LiftX p H R K) ≤ Subgroup.centralizer
      ((CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hd.toCore.le_centralizer_pCore h3 h84 hD2 hYX

theorem D1OneSmallData.pCorePreimage_inf_ne_bot_of_core (h3 : D1PhaseThree p P M H R)
    (hU : KFactUPrime p K) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {X₁ : Subgroup G} (hX₁X : X₁ ≤ d1LiftX p H R K)
    (hX₁ : X₁ ≠ ⊥)
    (hcomp : ∀ L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L ⊤ →
      barM M X₁ ≤ Subgroup.centralizer (L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
      barM M X₁ ≤ Subgroup.centralizer
        ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)) :
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ := by
  intro hYX
  have : Fact p.Prime := ⟨h3.prime⟩
  have hX₁p : IsPGroup p (barM M X₁) :=
    ((hd.cfg.ext.isPGroup.to_le (hX₁X.trans (d1LiftX_le p H R K))).comap_subtype).map _
  have hcen : barM M X₁ ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_pCore_of_le_centralizer_components hX₁p hcomp fun l hl => ?_
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    by_cases hlp : l = p
    · rw [hlp]
      exact (Subgroup.map_mono (Subgroup.comap_mono hX₁X)).trans
        (hd.le_centralizer_pCore h3 h84 hD2 hYX)
    rcases hodd l hl hl2 hlp with h | h
    · exact h
    · exact (hd.false_of_four_le_pRank h3 hU h84 hD2 hl hl2 hlp h).elim
  apply hX₁
  rw [eq_bot_iff, ← hYX]
  refine le_inf (fun x hx => ?_) hX₁X
  have hxM : x ∈ M := (d1LiftX_le p H R K).trans hd.cfg.ext.le_M (hX₁X hx)
  exact ⟨⟨x, hxM⟩, hcen ⟨⟨x, hxM⟩, hx, rfl⟩, rfl⟩

end MSide

end CFSG.AGLEmbedding
