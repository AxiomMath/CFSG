module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)

@[expose] def LieThreeDichAt (K : Type) [Group K] [Finite K] : Prop :=
  (∀ S : Sylow 3 K, IsMulCommutative (S : Subgroup K)) ∨ HasNoncommPair 3 K ∨
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≠ 3 ∨ (Nat.card K).factorization 3 ≠ 5

@[expose] def LieThreeDich : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → (∃ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f ∧
      LieModel K t n ℓ f) → LieThreeDichAt K

theorem sylow3OmegaLie_of_lieThreeDich (h : LieThreeDich) : Sylow3OmegaLie := by
  intro K _ _ hs hnab hcat hmodel hrank S hS hΩ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h K hs hnab hcat hmodel with hab | ⟨x, y, hx, hy, hxy, hp⟩ | hr | hv
  · exact hab S
  · exfalso
    obtain ⟨g, hg⟩ := ThreeQuotient.exists_conj_le S hp
    have hxS := hg x (Subgroup.subset_closure (by simp))
    have hyS := hg y (Subgroup.subset_closure (by simp))
    have h3 : ∀ z : K, z ^ 3 = 1 → (g * z * g⁻¹) ^ 3 = 1 := fun z hz => by
      rw [conj_pow, hz, mul_one, mul_inv_cancel]
    apply hxy
    have hc := hΩ _ hxS _ hyS (h3 x hx) (h3 y hy)
    have : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := hc
        _ = g * (y * x) * g⁻¹ := by group
    simpa using this
  · exact absurd hrank hr
  · exfalso
    apply hv
    have h1 := Sylow.card_eq_multiplicity S
    rw [hS] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.L28
