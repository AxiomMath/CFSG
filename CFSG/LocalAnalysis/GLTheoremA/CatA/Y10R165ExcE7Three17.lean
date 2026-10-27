module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7QTorus4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Open CFSG.RankThree.Classical2 CFSG.Blueprint.Chevalley
open scoped MatrixGroups Pointwise

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

theorem exists_elemAbelian_pRank_three_of_a5Layer_split_le
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹)
    {n : ℕ} (hKn : Nat.card K = 2 ^ n)
    {x : adjointGroup Tag.E7 K} {J : Subgroup (adjointGroup Tag.E7 K)}
    [Finite ↥(adjointGroup Tag.E7 K)] [Finite ↥J]
    (hJx : J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)))
    (ρ : ↥(fixSubgroup Φ') →* J) (hρ : Function.Surjective ρ)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z)
    (hk : Nat.card ρ.ker ∣ 6) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) :
    ∃ F : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian q F ∧
      F ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)) ∧
      F ≤ Subgroup.normalizer (J : Set (adjointGroup Tag.E7 K)) ∧
      3 ≤ CFSG.Open.pRank q F := by
  classical
  have hdiv' : q ∣ Nat.card K - 1 ∨ Nat.card K = 2 ∧ q = 3 := by
    rcases hdiv with h | ⟨h1, h2⟩
    · left
      rwa [hKn]
    · right
      rw [hKn, h1]
      norm_num
      exact h2
  obtain ⟨F₀, hF₀el, hF₀rank⟩ :=
    exists_elemAbelian_pRank_three_of_a5Layer_split hfix ρ hρ hc hk hq hq2 hdiv'
  refine ⟨F₀.map J.subtype, hF₀el.map J.subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le F₀).trans hJx
  · exact (Subgroup.map_subtype_le F₀).trans Subgroup.le_normalizer
  · rw [CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt J.subtype
      J.subtype_injective]
    exact hF₀rank

theorem exists_elemAbelian_pRank_three_of_a5Layer_unitary_le
    {ℓ f : ℕ} [Fact ℓ.Prime] [IsAlgClosure K L] [CharP L ℓ]
    (hℓ2 : ℓ = 2) (hK : Nat.card K = ℓ ^ f)
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (ℓ ^ f) 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹)
    {n : ℕ} (hKn : Nat.card K = 2 ^ n)
    {x : adjointGroup Tag.E7 K} {J : Subgroup (adjointGroup Tag.E7 K)}
    [Finite ↥(adjointGroup Tag.E7 K)] [Finite ↥J]
    (hJx : J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)))
    (ρ : ↥(fixSubgroup Φ') →* J) (hρ : Function.Surjective ρ)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z)
    (hk : Nat.card ρ.ker ∣ 6) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ 2 ^ n - 1) :
    ∃ F : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian q F ∧
      F ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)) ∧
      F ≤ Subgroup.normalizer (J : Set (adjointGroup Tag.E7 K)) ∧
      3 ≤ CFSG.Open.pRank q F := by
  classical
  have hdiv' : q ∣ Nat.card K - 1 := by
    rw [hKn]
    exact hdiv
  obtain ⟨F₀, hF₀el, hF₀rank⟩ :=
    exists_elemAbelian_pRank_three_of_a5Layer_unitary hℓ2 hK hfix ρ hρ hc hk hq hq2 hdiv'
  refine ⟨F₀.map J.subtype, hF₀el.map J.subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le F₀).trans hJx
  · exact (Subgroup.map_subtype_le F₀).trans Subgroup.le_normalizer
  · rw [CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt J.subtype
      J.subtype_injective]
    exact hF₀rank

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
