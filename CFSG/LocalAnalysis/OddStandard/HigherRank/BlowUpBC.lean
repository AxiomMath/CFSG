module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit CFSG.ComponentClassification.GSThmB

theorem false_of_alternating_blowUp (hS : Solomon2AnInput) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hcat : ¬ Blueprint.Catalog G) {w : G} (hw2 : orderOf w = 2)
    {K : Subgroup G} (hK : IsTwoComponentIn K (centralizer ({w} : Set G))) (hwK : w ∈ K) {m : ℕ}
    (hm : 8 ≤ m) (hq : CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hZ : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2)
    (e : Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
      alternatingGroup (Fin m))) : False := by
  have hP : IsPComponent 2 (K.subgroupOf (centralizer ({w} : Set G))) :=
    (isTwoComponentIn_iff hK.1).1 hK
  have hperf : Group.IsPerfect (↥K ⧸ pPrimeCore 2 ↥K) := hq.1
  rcases hS G w hw2 K m hm hK.1 hP hwK hperf hZ e with e' | e'
  · exact hcat (Or.inr (Or.inr (Or.inr (Or.inr ⟨.McL, e'⟩))))
  · exact hcat (Or.inr (Or.inr (Or.inr (Or.inr ⟨.Ly, e'⟩))))

theorem false_of_blowUp_five (hS : Solomon2AnInput) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hcat : ¬ Blueprint.Catalog G) {w : G} (hw2 : orderOf w = 2)
    {K : Subgroup G} (hK : IsTwoComponentIn K (centralizer ({w} : Set G))) (hwK : w ∈ K)
    (h : ∃ n : ℕ, 4 ≤ n ∧ CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
        alternatingGroup (Fin (2 * n + 1)))) : False := by
  obtain ⟨n, hn, hq, hZ, e⟩ := h
  exact false_of_alternating_blowUp hS hcat hw2 hK hwK (by omega) hq hZ e

theorem false_of_blowUp_three (hS : Solomon2AnInput) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hcat : ¬ Blueprint.Catalog G) {w : G} (hw2 : orderOf w = 2)
    {K : Subgroup G} (hK : IsTwoComponentIn K (centralizer ({w} : Set G))) (hwK : w ∈ K)
    (h : ∃ n : ℕ, 4 ≤ n ∧ CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
        alternatingGroup (Fin (2 * n)))) : False := by
  obtain ⟨n, hn, hq, hZ, e⟩ := h
  exact false_of_alternating_blowUp hS hcat hw2 hK hwK (by omega) hq hZ e

end CFSG.OddStandard.HigherRank
