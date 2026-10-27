module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.LieType.Chevalley.C2E6BruhatBuilding
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.KE.CTRational
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix MatrixGroups

section RootData

theorem e8_root_bound : ∀ l ∈ Tag.E8.artifactRoots, ∀ x ∈ l, |x| ≤ 6 := by decide +kernel

theorem e8_root_simple : ∀ l ∈ Tag.E8.artifactRoots, ∀ i : Fin Tag.E8.rank,
    (∀ k : Fin Tag.E8.rank, k ≠ i → l.getD k 0 = 0) → l.getD i 0 = 1 ∨ l.getD i 0 = -1 := by
  decide +kernel

theorem e8_root_small : ∀ m : ℕ, 3 ≤ m → m ≤ 6 → ∀ l ∈ Tag.E8.artifactRoots,
    ∀ i : Fin Tag.E8.rank, (∀ k : Fin Tag.E8.rank, k ≠ i → (m : ℤ) ∣ l.getD k 0) →
      (m : ℤ) ∣ l.getD i 0 - 1 ∨ (m : ℤ) ∣ l.getD i 0 + 1 := by
  intro m h3 h6
  interval_cases m <;> decide +kernel

theorem e7_root_bound : ∀ l ∈ Tag.E7.artifactRoots, ∀ x ∈ l, |x| ≤ 4 := by decide +kernel

theorem e7_root_simple : ∀ l ∈ Tag.E7.artifactRoots, ∀ i : Fin Tag.E7.rank,
    (∀ k : Fin Tag.E7.rank, k ≠ i → l.getD k 0 = 0) → l.getD i 0 = 1 ∨ l.getD i 0 = -1 := by
  decide +kernel

theorem e7_root_small : ∀ m : ℕ, 3 ≤ m → m ≤ 4 → ∀ l ∈ Tag.E7.artifactRoots,
    ∀ i : Fin Tag.E7.rank, (∀ k : Fin Tag.E7.rank, k ≠ i → (m : ℤ) ∣ l.getD k 0) →
      (m : ℤ) ∣ l.getD i 0 - 1 ∨ (m : ℤ) ∣ l.getD i 0 + 1 := by
  intro m h3 h4
  interval_cases m <;> decide +kernel

theorem f4_root_bound : ∀ l ∈ Tag.F4.artifactRoots, ∀ x ∈ l, |x| ≤ 4 := by decide +kernel

theorem f4_root_simple : ∀ l ∈ Tag.F4.artifactRoots, ∀ i : Fin Tag.F4.rank,
    (∀ k : Fin Tag.F4.rank, k ≠ i → l.getD k 0 = 0) → l.getD i 0 = 1 ∨ l.getD i 0 = -1 := by
  decide +kernel

theorem f4_root_small : ∀ m : ℕ, 3 ≤ m → m ≤ 4 → ∀ l ∈ Tag.F4.artifactRoots,
    ∀ i : Fin Tag.F4.rank, (∀ k : Fin Tag.F4.rank, k ≠ i → (m : ℤ) ∣ l.getD k 0) →
      (m : ℤ) ∣ l.getD i 0 - 1 ∨ (m : ℤ) ∣ l.getD i 0 + 1 := by
  intro m h3 h4
  interval_cases m <;> decide +kernel

end RootData

theorem exists_char_data (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] :
    ∃ p₀ f : ℕ, p₀.Prime ∧ 1 ≤ f ∧ Nat.card K = p₀ ^ f ∧ CharP L p₀ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  exact ⟨ringChar K, f, hp, f.pos, by rw [Nat.card_eq_fintype_card, hcard],
    charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
