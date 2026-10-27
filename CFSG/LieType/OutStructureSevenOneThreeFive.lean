module

public import CFSG.LieType.OutStructureHInputFiveUnitary
public import CFSG.LieType.OutStructureOuterLiftUnitary
public import CFSG.LieType.OutStructureFixRankUnitary
public import CFSG.LieType.OutStructureSevenOneThreeThirdFive
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenPClosedFive
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenTwoOneHolds
public import CFSG.LieType.OutStructureHInputFiveLinear

public section

namespace CFSG.LieType.OutStructure

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

theorem hInput_unitary_five
    {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {N r f : ℕ}
    (hcl : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU N r f) (hN : 6 ≤ N) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
      ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
        ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
          Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a := by
  have := hLn
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hLX : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
    intro hdvd
    have h3 := CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactCenterRankFive_holds
      X hK L hL p hp hp5 hdvd
    omega
  have hrkS : CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≤ 3 := by
    rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      hp hZ, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    omega
  obtain ⟨hpq, hq1⟩ := not_dvd_of_pRank_le_three_of_statedPSU hcl hN hp hp2 hrkS
  obtain ⟨⟨hr, hf, -, h32⟩, K, _, _, hKcard, ⟨eS⟩⟩ := hcl
  let hU : UnitaryFieldData r f K := ⟨hr, hf, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have hq : ¬(N = 3 ∧ r ^ f = 2) := by
    rintro ⟨h1, h2⟩
    exact h32 (by rw [h1, h2])
  let ePU : primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ≃* unitaryPSU hU N :=
    Classical.choice (nonempty_primeFormP_mulEquiv hU isPrimeFormGram_one)
  let e : (↥L ⧸ Subgroup.center ↥L) ≃*
      primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) :=
    eS.trans (ePU.trans (unitaryPSUEquiv hU (by omega))).symm
  have hpr : p ≠ r := fun h => hpq (h ▸ dvd_pow_self p (by omega))
  have hdiv : ¬ p ∣ Nat.gcd N (r ^ f + 1) := fun h => hq1 (h.trans (Nat.gcd_dvd_right _ _))
  exact hInput_unitary_of_exists_of_cross hL hU e (by omega) hq hp hp2 hpr hZ hdiv
    (fun hnot hc => exists_orderOf_eq_not_mem_of_primeFormP hL hU e (by omega) hq hp hdiv hnot hc)

theorem hInput_five
    : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      ∀ p : ℕ, p.Prime → p ≠ 2 → 5 ≤ p →
      ∀ L : Subgroup X, L.Normal → CFSG.IsComponent L →
      CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 →
      ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
          (L ⊔ Subgroup.centralizer (L : Set X)) →
        (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
        ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
          ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
            Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a := by
  intro X _ _ hK p hp _ hp5 L hLn hL hX2 hnot
  by_cases hex : OutFiveExceptional (↥L ⧸ Subgroup.center ↥L) p
  · rcases hex with ⟨N, r, f, hcl, hN, -⟩ | ⟨N, r, f, hcl, hN, -⟩
    · exact hInput_linear_five hK hp hp5 hL hLn hX2 hcl (by omega) hnot
    · exact hInput_unitary_five hK hp hp5 hL hLn hX2 hcl (by omega) hnot
  · exact absurd (isPClosedMod_of_not_outFiveExceptional hK hp hp5 hL hLn hex) hnot

theorem sevenOneThree_holds
    : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneThree :=
  sevenOneThree_holds_of_hInput hInput_five

theorem sevenOneUsed_holds
    : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneUsed :=
  ⟨sevenOneThree_holds, CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactOmegaNotCentral_holds⟩

end CFSG.LieType.OutStructure
