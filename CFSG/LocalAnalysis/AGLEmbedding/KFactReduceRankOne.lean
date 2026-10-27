module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneUnitary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

@[expose] def KFactUPrimeSmallRest : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ (p = 3 ∧ IsLinThreeFour K) →
      ¬ (p = 5 ∧ IsFi22 K) → ¬ (IsSmallLinTwo p K ∨ IsSmallUnitary p K) → KFactUPrime p K

@[expose] def KFactOneSmallRest : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ (p = 3 ∧ IsLinThreeFour K) →
      ¬ (p = 5 ∧ IsFi22 K) → ¬ (IsSmallLinTwo p K ∨ IsSmallUnitary p K) → OneSmallFacts p K T

@[expose] def KFactOneLieNonUnitary : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ IsUnitaryGroup p K → OneLieFacts p K T

theorem smallRankOneData_of_small_of_ne_two {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsSmallLinTwo p K ∨ IsSmallUnitary p K)
    (T : Sylow p K) : SmallRankOneData p K T := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hK with hK | hK
  · exact smallRankOneData_of_isSmallLinTwo hp2 hK T
  · exact smallRankOneData_of_isSmallUnitary hp hK T

theorem smallRankOneData_of_isUnitaryGroup {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsUnitaryGroup p K) (T : Sylow p K) : SmallRankOneData p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, ⟨he⟩⟩ := hK
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd ⟨he⟩)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T S
  exact SmallRankOneData.of_equiv e' he'
    (UnitaryModel.smallRankOneData_psu J hJ hF hfix hq S hS hd ⟨e'.symm.trans he⟩)

theorem kFactUPrimeSmall_of_rest (h : KFactUPrimeSmallRest) : KFactUPrimeSmall := by
  intro K _ _ hs hnab hcat p hp hp2 T hnc hΓ hrk h34 hfi
  by_cases hK : IsSmallLinTwo p K ∨ IsSmallUnitary p K
  · exact kFactUPrime_of_data hp (smallRankOneData_of_small_of_ne_two hp hp2 hK)
  · exact h K hs hnab hcat p hp hp2 T hnc hΓ hrk h34 hfi hK

theorem kFactOneSmall_of_rest (h : KFactOneSmallRest) : KFactOneSmall := by
  intro K _ _ hs hnab hcat p hp hp2 T hnc hΓ hrk h34 hfi
  by_cases hK : IsSmallLinTwo p K ∨ IsSmallUnitary p K
  · have hD := smallRankOneData_of_small_of_ne_two hp hp2 hK
    have hF := oneLieFacts_of_data hp hD T
    refine ⟨hF.pSubgroup_le, hF.torus, fun V hVT hV hVN => ?_⟩
    rcases hF.centralizer V hVT hV hVN with h1 | ⟨hVZ, hU⟩
    · exact Or.inl h1
    · refine Or.inr ⟨hVZ, fun hZT => ?_⟩
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨d, hd, ⟨e⟩⟩ := hU
      obtain ⟨hcard, hcomm, -, -⟩ := kFactUnitarySylowStructure K p d hp2 hd ⟨e⟩ T
      have hab : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        have : x ∈ centerOf (T : Subgroup K) := by rw [hZT]; exact hx
        exact this.2
      have hT : (T : Subgroup K) = ⊥ := by
        have : centerOf (T : Subgroup K) = ⊥ := by
          change (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) = ⊥
          rw [← hcomm, hab]
        rw [← hZT, this]
      have h1 : Nat.card (T : Subgroup K) = 1 := by rw [hT]; exact Subgroup.card_bot
      rw [hcard] at h1
      have hpos : 0 < 3 * d.1.fieldExponent := by
        obtain ⟨q, hqp, hdq⟩ := hd
        have : d.1.fieldExponent = q.exponent := by rw [hdq]; simp
        rw [this]
        have := q.exponent_pos
        omega
      have := Nat.one_lt_pow hpos.ne' hp.one_lt
      omega
  · exact h K hs hnab hcat p hp hp2 T hnc hΓ hrk h34 hfi hK

theorem kFactOneLie_of_nonUnitary (h : KFactOneLieNonUnitary) : KFactOneLie := by
  intro K _ _ hs hnab hcat p hp hp2 T hnc hΓ hbig
  by_cases hU : IsUnitaryGroup p K
  · exact oneLieFacts_of_data hp (smallRankOneData_of_isUnitaryGroup hp hU) T
  · exact h K hs hnab hcat p hp hp2 T hnc hΓ hbig hU

end CFSG.AGLEmbedding
