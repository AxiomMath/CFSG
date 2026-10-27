module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideBlocks
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideComp
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideOdd
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem pCore_le_centralizer_component {Y : Type} [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime]
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    CFSG.pCore p Y ≤ Subgroup.centralizer (L : Set Y) := by
  have : Group.IsNilpotent (CFSG.pCore p Y) :=
    (CFSG.pCore_isPGroup (p := p) (G := Y)).isNilpotent
  have h := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal L
    (CFSG.pCore p Y) hL (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (CFSG.pCore_normal (p := p) (G := Y)).isSubnormal)
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact h

theorem pCore_le_centralizer_pCore {Y : Type} [Group Y] [Finite Y] {p s : ℕ} [Fact p.Prime]
    [Fact s.Prime] (hsp : s ≠ p) :
    CFSG.pCore p Y ≤ Subgroup.centralizer (CFSG.pCore s Y : Set Y) := by
  have hinf : CFSG.pCore p Y ⊓ CFSG.pCore s Y = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes ?_
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p) (G := Y))
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := s) (G := Y))
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hsp))
  have h : ⁅CFSG.pCore p Y, CFSG.pCore s Y⁆ = ⊥ :=
    le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf _ _)
  rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h

theorem stmtOneLieCore_of (hC3 : StmtOneLieCompThree)
    (hB3 : StmtOneLieBlocksThree) (hMD : StmtOneLieMData) :
    KFactOneLie → KFactOneLieTorus → Asc81bEightFour → Asc81bEightFive → Asc81bEightSix →
      D1NoXBlock → StmtBlockThree → StmtLemmaBRelCyc → KFactThreeOrFiveDvd →
      KFactOutElemRankOdd → D1OneLieMSideCore := by
  have hO := @stmtOneLieOddCore
  have hC1 := @stmtOneLieCompNotLe
  have hC5 := @stmtOneLieCompFive
  have hB5 := @stmtOneLieBlocksFive
  intro hK hT h84 h85 h86 hD2 hBT hLB hα hβ G _ _ p P M H R Rbar K hd _huniq
  have hp : p.Prime := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcase : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    have hp2 := hd.cfg.red.ne_two
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · interval_cases p
      · exact absurd rfl hp2
      · exact Or.inl rfl
      · exact absurd hp (by decide)
    · exact Or.inr h5
  set X := d1LiftX p H R K with hXdef
  by_cases hYX : pCorePreimage p M ⊓ X = ⊥
  · obtain ⟨n, e, h⟩ := hMD hK hT hd
    set Z := d1LiftX p H R
      (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) with hZdef
    have hZX : Z ≤ X := Subgroup.map_mono (inf_le_inf_left _ (Subgroup.comap_mono
      ((inf_le_left : centerOf _ ≤ _).trans inf_le_right)))
    have hZ1 : Z ≠ ⊥ := by
      intro hZ
      obtain ⟨φ, -⟩ := h.torus
      have hn := h.two_le
      have hc := Nat.card_congr φ.toEquiv
      rw [Nat.card_congr Multiplicative.toAdd, GaloisField.card p n (by omega)] at hc
      have h1 : Nat.card Z = 1 := by rw [hZ]; exact Subgroup.card_bot
      rw [h1] at hc
      exact (Nat.one_lt_pow (by omega) hp.one_lt).ne' hc
    have hYZ : pCorePreimage p M ⊓ Z = ⊥ := le_bot_iff.mp (hYX ▸ inf_le_inf_left _ hZX)
    refine ⟨Z, hZX, hZ1, fun Lb hLb => ?_, fun s hs hs2 hsp => hO h s hs hs2 hsp⟩
    obtain ⟨L, hL2, rfl, hw | hle⟩ := h.ph3.exists_weakSBlock_or_le_inf hLb
    · rcases hcase with hp3 | hp5
      · exact hB3 hLB hBT h84 h85 h86 hD2 h hp3 hYZ L hw
      · exact hB5 hLB hBT h85 hD2 h hp5 L hw
    · by_cases hLN : L ≤ GLBPrimeCore p H
      · rcases hcase with hp3 | hp5
        · exact hC3 hα hβ hBT h hp3 L hL2 hLN
        · exact hC5 hα (kFactOutElemRank_of_odd hβ) h hp5 L hL2 hLN
      · exact hC1 h L hL2 hle hLN
  · refine ⟨pCorePreimage p M ⊓ X, inf_le_right, hYX, fun Lb hLb => ?_, fun s hs _ hsp => ?_⟩
    · have hle : barM M (pCorePreimage p M ⊓ X) ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
        rw [← barM_preimage (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_left)
      exact hle.trans (pCore_le_centralizer_component p hLb)
    · have : Fact s.Prime := ⟨hs⟩
      have hle : barM M (pCorePreimage p M ⊓ X) ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
        rw [← barM_preimage (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_left)
      exact Or.inl (hle.trans (pCore_le_centralizer_pCore hsp))

theorem d1OneLieMSideCore_of_stmts (hC3 : StmtOneLieCompThree) (hB3 : StmtOneLieBlocksThree)
    (hMD : StmtOneLieMData) (hK : KFactOneLie) (hT : KFactOneLieTorus) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hBT : StmtBlockThree)
    (hLB : StmtLemmaBRelCyc) (hα : KFactThreeOrFiveDvd) (hβ : KFactOutElemRankOdd) :
    D1OneLieMSideCore :=
  stmtOneLieCore_of hC3 hB3 hMD hK hT h84 h85 h86 hD2 hBT hLB hα hβ

end CFSG.AGLEmbedding
