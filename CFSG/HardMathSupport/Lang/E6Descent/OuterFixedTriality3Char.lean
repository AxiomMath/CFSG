module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTrialityThreeChars
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Bruhat
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.G2Stage

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.Triality
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


theorem card_fixedSubgroup_dvd_G2_of_charP_three {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] [CharP K 3] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (3 ^ f)) {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hα3 : α ^ 3 = 1) (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (3 ^ f) := by
  obtain ⟨u, hu, hu3, hcard⟩ :=
    exists_unipotent_conj_fieldActor_of_order_three hf hK σ hσ α hα3 hαin
  rw [hcard]
  obtain ⟨w, s, r, r', hs, hr, hr', hw⟩ := exists_twistedConj_longForm hf hK σ hσ hu hu3
  have hcard2 :
      Nat.card (fixedSubgroup (MulAut.conj
        (longElt hf hK σ hσ (Or.inl rfl) s hs *
          longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') *
        fieldActor (t := TwistTag.D4) σ σ)) =
      Nat.card (fixedSubgroup (MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ)) := by
    rw [← hw, ← conj_mul_twisted hf hK σ hσ (fieldActor (t := TwistTag.D4) σ σ) u w]
    exact card_fixed_conj (MulAut.conj w⁻¹) _
  rw [← hcard2]
  by_cases hne : s = 0 ∧ r = 0 ∧ r' = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hne
    rw [longElt_zero hf hK σ hσ (Or.inl rfl) hs,
      longElt_zero hf hK σ hσ (Or.inr (Or.inl rfl)) hr,
      longElt_zero hf hK σ hσ (Or.inr (Or.inr rfl)) hr']
    simp only [mul_one, map_one, one_mul]
    exact dvd_of_eq (card_fixed_fieldActor_D4_of_frobenius Nat.prime_three hf hK σ hσ)
  · obtain ⟨ε, c, hc, hc0, hε⟩ := exists_conj_to_top_of_longForm hf hK σ hσ hs hr hr' hne
    have hcard3 :
        Nat.card (fixedSubgroup (MulAut.conj
          (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
          fieldActor (t := TwistTag.D4) σ σ)) =
        Nat.card (fixedSubgroup (MulAut.conj
          (longElt hf hK σ hσ (Or.inl rfl) s hs *
            longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
            longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') *
          fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [← hε]
      exact card_fixed_conj ε _
    rw [← hcard3]
    change Nat.card (fixSubgroup (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
      fieldActor (t := TwistTag.D4) σ σ)) ∣ lieOrderNumerator .G2 0 (3 ^ f)
    rw [fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0]
    refine (Subgroup.card_dvd_of_le inf_le_left).trans (dvd_of_eq ?_)
    exact card_fixed_fieldActor_D4_of_frobenius Nat.prime_three hf hK σ hσ

theorem outerFixedOrderTrialityThreeChar_three : OuterFixedOrderTrialityThreeChar (· = 3) := by
  intro K _ _ n ℓ f hℓ hadm hmodel α hα3 hαin
  subst hℓ
  refine Or.inr ?_
  rcases hmodel with ⟨ht, -⟩ | ⟨-, -, hM⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_three hadm.2.1 hM.2
    have hcard' : Nat.card K' = (3 ^ f) ^ 3 := hcard
    have hK3 : Nat.card K' = 3 ^ (3 * f) := by
      rw [hcard', ← pow_mul, Nat.mul_comm]
    have hk : 1 ≤ 3 * f := by have := hadm.2.1; omega
    have : CharP K' 3 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_three hk hK3
    have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    have hβout : MulAut.congr e α ∉ inner (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
      fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
    rw [← card_fixedSubgroup_congr e α]
    exact card_fixedSubgroup_dvd_G2_of_charP_three hadm.2.1 hcard' σ hσ hβ3 hβout
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.HardMathSupport.Lang.E6Descent
