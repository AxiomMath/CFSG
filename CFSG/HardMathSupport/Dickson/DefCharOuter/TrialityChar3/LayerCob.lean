module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerOrbit

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem exists_layer_cob {k : ℕ} (hk : k < (maxHeight TwistTag.D4.tag).toNat)
    (a : LayerCoord (K := K) k)
    (hN : a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1)
    (hz : ∀ O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)), O.1.card = 1 →
      Multiplicative.toAdd a O = 0) :
    ∃ c ∈ (layerPhi σ k).range, a = c * (layerTau σ k c)⁻¹ := by
  have hfix : Nat.card {c : K // σ c = c} = 3 ^ f :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun c => Iff.rfl)).trans
      (CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ)
  have hK' : Nat.card K = Nat.card {c : K // σ c = c} ^ 3 := by rw [hK, hfix]
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ1 : σ ≠ 1 := by
    intro h
    have hc : Nat.card {c : K // σ c = c} = Nat.card K := by
      rw [h]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun c => by simp)
    rw [hfix, hK] at hc
    have hp : 2 ≤ 3 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    have h2 : (3 ^ f) ^ 1 = (3 ^ f) ^ 3 := by rw [pow_one]; exact hc
    have h3 : 1 = 3 := Nat.pow_right_injective hp h2
    omega
  have e1 : ∀ (x : LayerCoord (K := K) k) (O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ))),
      Multiplicative.toAdd (layerTau σ k x) O = σ (Multiplicative.toAdd x O) :=
    fun _ _ => rfl
  have hcob : ∀ O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)), ∃ c : K,
      (O.1.card = 1 → σ c = c) ∧ Multiplicative.toAdd a O = c - σ c := by
    intro O
    by_cases hO : O.1.card = 1
    · exact ⟨0, fun _ => map_zero σ, by rw [hz O hO, map_zero, sub_zero]⟩
    · have htr0 : Multiplicative.toAdd a O + σ (Multiplicative.toAdd a O) +
          σ (σ (Multiplicative.toAdd a O)) = 0 := by
        have h := congrFun (congrArg Multiplicative.toAdd hN) O
        simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply, e1] at h
        linear_combination h
      have htr : -Multiplicative.toAdd a O + σ (-Multiplicative.toAdd a O) +
          σ (σ (-Multiplicative.toAdd a O)) = 0 := by
        simp only [map_neg]
        linear_combination -htr0
      obtain ⟨c, hc⟩ := exists_sub_of_trace_eq_zero σ hσ3 hσ1 hK' _ htr
      exact ⟨c, fun h => absurd h hO, by linear_combination -hc⟩
  choose γ hγ hγa using hcob
  have hmem : ∀ O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)),
      Multiplicative.ofAdd (Pi.single O (γ O)) ∈ (layerPhi σ k).range := fun O => by
    obtain ⟨x, hx, -⟩ := exists_orbitElt hf hK σ hσ hk O (γ O) (hγ O)
    exact ⟨x, hx⟩
  have hprod : (∏ O, Multiplicative.ofAdd (Pi.single O (γ O))) ∈ (layerPhi σ k).range :=
    Subgroup.prod_mem _ fun O _ => hmem O
  have hγeq : (∏ O, Multiplicative.ofAdd (Pi.single O (γ O))) = Multiplicative.ofAdd γ := by
    rw [← ofAdd_sum, Finset.univ_sum_single]
  rw [hγeq] at hprod
  refine ⟨Multiplicative.ofAdd γ, hprod, ?_⟩
  apply Multiplicative.toAdd.injective
  funext O
  simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, e1, toAdd_ofAdd]
  rw [hγa O, sub_eq_add_neg]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
