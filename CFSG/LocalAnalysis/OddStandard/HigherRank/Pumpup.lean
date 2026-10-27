module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.SLTwoUnique
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit

@[expose] def BlowUpOutcome {G : Type} [Group G] (p f : ℕ) (K : Subgroup G) : Prop :=
  (p = 7 ∧ f = 1 ∧ CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 16 ∧
      CFSG.ComponentClassification.GrSLit.IsL34Type
        ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))) ∨
    (p = 5 ∧ f = 1 ∧ ∃ n : ℕ, 4 ≤ n ∧ CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
        alternatingGroup (Fin (2 * n + 1)))) ∨
    (p = 3 ∧ f = 2 ∧ ∃ n : ℕ, 4 ≤ n ∧ CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
        alternatingGroup (Fin (2 * n))))

theorem exists_blowUp_of_fourGroup (hL35 : Harris81Lemma35Step)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    {W : Subgroup G} (hW2 : ∀ a ∈ W, a * a = 1) (hW4 : Nat.card ↥W = 4)
    {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer (W : Set G))) (hM : IsMTypeSchur p ↥J)
    (hsl : IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J))
    {w v : G} (hwJ : w ∈ J) (hwW : w ∈ W) (hw1 : w ≠ 1) (hvW : v ∈ W) (hvw : v ∉ zpowers w) :
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer ({w} : Set G)) ∧ w ∈ K ∧
      BlowUpOutcome p f K := by
  have hne : J ⊓ W ≠ ⊥ := fun h => hw1 (by
    have hw : w ∈ J ⊓ W := ⟨hwJ, hwW⟩
    rwa [h, Subgroup.mem_bot] at hw)
  obtain ⟨hwK, -, hKc, -, -, hcases⟩ := hL35 G hnab hKP hcat p hp hp2 W hW2 hW4 J hJ hM f hf h5
    hsl hne w ⟨hwJ, hwW⟩ hw1 v hvW hvw _ rfl
  exact ⟨_, hKc, hwK, pumpup_cases_of_isSLTwoOver hsl hcases⟩

end CFSG.OddStandard.HigherRank
