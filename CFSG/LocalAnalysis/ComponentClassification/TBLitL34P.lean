module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PTriv
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PGraph
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PRho
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbal
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PBase

public section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.TBLit.L34P
open scoped MatrixGroups


theorem l34PumpUp_local {X : Type} [Group X] [Finite X] {α β γ : X} (hα : orderOf α = 2)
    (hβ : orderOf β = 2) (hγ : orderOf γ = 2) (hαγ : α * γ = γ * α) (hβγ : β * γ = γ * β)
    {K : Subgroup X} (hKγ : K ≤ centralizer ({γ} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({γ} : Set X)))) (hγK : γ ∈ K)
    (hβN : β ∈ normalizer (K : Set X)) (hL : LieModel (K ⧸ Open.fusionZStar K) .PSL 3 2 2)
    {S : Subgroup X} (hSK : S ≤ K)
    (hSβγ : S ≤ centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X))
    (hS : IsPComponent 2 (S.subgroupOf (centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X))))
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (e : ↥S ⧸ pPrimeCore 2 ↥S ≃* SL(2, GaloisField p n)) {E : Subgroup X}
    (hEα : E ≤ oddCentralizerCore α)
    (hEβγ : E ≤ centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X))
    (hprop : ActsProperly α E S ((pPrimeCore 2 ↥S).map S.subtype)) :
    GSUnbalancingTriple γ α K ∧ IsL34Unitary K α ∧ HarrisLit.EndB.IsL34Field K β ∧
      Nat.card (zStarIn K) = 16 * Nat.card (oddIn K) ∧ p = 7 ∧ n = 1 ∧
      ∃ ρ ∈ K, ρ * β = β * ρ ∧ ρ ∈ zStarIn K ∧ ρ * ρ = γ ∧ α⁻¹ * ρ * α * ρ ∈ oddIn K := by
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hKγ hK
  have hSperf : ⁅S, S⁆ = S := UnbalancedCorr.commutator_eq_of_isPComponent hSβγ hS
  have htri : GSUnbalancingTriple γ α K := gsUnbalancingTriple_of_actsProperly hα hγ hαγ hKγ hK
    hSK hEα (hEβγ.trans inf_le_right) hprop
  have hunit : IsL34Unitary K α := l34UnbalancingUnitaryStep X γ α K htri hL
  have hβ2 : β * β = 1 := by rw [← pow_two, ← hβ, pow_orderOf_eq_one]
  have hSβ : S ≤ centralizer ({β} : Set X) := hSβγ.trans inf_le_left
  have hodd := odd_card_galoisField (p := p) hp2 hn
  obtain ⟨q, hqS, hqsurj, hqker, h3, ρ, hρ, hβq⟩ := exists_frame hL hβN hβ2
  rcases hρ with rfl | rfl | rfl | rfl | rfl
  · exact (false_of_trivial hKperf hKγ hβN hβ2 hSK hSβ hS hodd e hqS hqsurj hqker hβq).elim
  · exact (false_of_le_solvable hSK hSperf hodd e q hqker isSolvable_C₁
      (range_imageHom_le hSK hβN hSβ hqS hβq)).elim
  · have hfield := isL34Field_of_frame hβN hβ2 hqS hqsurj hqker hβq
    have h7 := card_eq_seven_of_field hSK hSperf hβN hSβ hodd e hqS hqker hβq
    exact ⟨htri, hunit, hfield, card_zStarIn_of_field hKperf hL hβN hβ2 hSK hSβ h7 e hfield,
      (eq_seven_of_card hn h7).1, (eq_seven_of_card hn h7).2,
      exists_rho hKperf hL hβN hβ2 hSK hSβ h7 e hfield hunit hγ hγK hKγ hβγ⟩
  · exact (false_of_graph hKperf hβN hSK hSβ hodd e hqS hqsurj hqker h3 hβq).elim
  · exact (false_of_le_solvable hSK hSperf hodd e q hqker isSolvable_C₄
      (range_imageHom_le hSK hβN hSβ hqS hβq)).elim

theorem l34PumpUpExclusion_of_fieldUnitary (h : L34FieldUnitaryExclusion) :
    L34PumpUpExclusion := by
  intro X _ _ _ hnab hKP hcore hU α β γ hα hβ hγ hαβ hαγ hβγ K hKγ hK hγK hαN hβN hL S hSK hSβγ
    hS hγS hSL E hEα hEβγ hprop
  obtain ⟨p, n, hp, hp2, hn, ⟨e⟩⟩ := hSL
  obtain ⟨htri, hunit, hfield, h16, -, -, -⟩ :=
    l34PumpUp_local hα hβ hγ hαγ hβγ hKγ hK hγK hβN hL hSK hSβγ hS hp2 hn e hEα hEβγ hprop
  exact h X hnab hKP hcore hU γ α β K htri hγK hL h16 hunit hβγ hαβ.symm hfield

end CFSG.ComponentClassification.TBLit
