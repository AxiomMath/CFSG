module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSide
public import CFSG.HardMathSupport.Curtis.Proving.ToralQuotient

public section

namespace CFSG.HardMathSupport.Curtis.Proving

@[expose] def KFactSPLBlockTorusCaseB : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (p r : ℕ), CFSG.IsComponent L →
    p.Prime → p ≠ 2 → r.Prime → r ∣ p ^ 2 + 1 → ¬ r ∣ p ^ 2 - 1 → CFSG.AGLEmbedding.IsSPLBlockType p L →
    CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) →
    ∀ (u c : Y) (T X : Subgroup Y),
      u ∈ Subgroup.normalizer (L : Set Y) → u ^ p = 1 →
      u ∉ Subgroup.centralizer (L : Set Y) →
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({u} : Set Y)) →
      T ≤ Subgroup.normalizer (L : Set Y) → T ≤ Subgroup.centralizer ({u} : Set Y) → X ≤ T →
      T ⊓ Subgroup.centralizer (L : Set Y) = X →
      (∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) → (∀ a ∈ T, a ^ p ∈ X) →
      X.relIndex T = p ^ 4 →
      c ∈ Subgroup.normalizer (L : Set Y) → c ∈ Subgroup.centralizer ({u} : Set Y) →
      (∃ k : ℕ, c ^ r ^ k = 1) → (∀ t ∈ T, c * t * c⁻¹ ∈ T) →
      (∃ t ∈ T, c * t * c⁻¹ * t⁻¹ ∉ X) → False

theorem kFactSPLBlockTorus_of_caseB (hB : KFactSPLBlockTorusCaseB) :
    CFSG.AGLEmbedding.KFactSPLBlockTorus := by
  intro Y _ _ L p r hL hp hp2 hr hdvd hndvd hSPL hCat u c T X hu hup hunC hsolv hTN hTC hXT hTX
    hcomm hpow hidx hcN hcC hcr hcT hprem
  by_cases hnt : ∃ t ∈ T, c * t * c⁻¹ * t⁻¹ ∉ X
  · exact hB Y L p r hL hp hp2 hr hdvd hndvd hSPL hCat u c T X hu hup hunC hsolv hTN hTC hXT hTX
      hcomm hpow hidx hcN hcC hcr hcT hnt
  · simp only [not_exists, not_and, not_not] at hnt
    have : Fact p.Prime := ⟨hp⟩
    have : Fact r.Prime := ⟨hr⟩
    have hTX': ∃ t ∈ T, t ∉ X := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      have h1 : X.relIndex T = 1 := Subgroup.relIndex_eq_one.mpr (fun t ht => h t ht)
      rw [hidx] at h1
      have hpos : 1 < p ^ 4 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨t, ht, htX⟩ := hTX'
    exact not_premise_of_trivial_action hXT hcomm hpow hidx hnt ht htX hprem

end CFSG.HardMathSupport.Curtis.Proving

end
