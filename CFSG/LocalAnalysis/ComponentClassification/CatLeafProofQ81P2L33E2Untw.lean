module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2GFE
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem untwisted_not_isPGroup
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hopen : ∀ c : adjointGroup τ K, orderOf c = 2 →
      ¬ IsPGroup 2 ↥(centralizer ({c} : Set (adjointGroup τ K))))
    (β : MulAut (adjointGroup τ K)) (hβ : orderOf β = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_modGL (τ := τ) (K := K)
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  by_cases hin : β ∈ inner (adjointGroup τ K)
  · obtain ⟨c, rfl⟩ := hin
    have hc : orderOf c = 2 := by
      rw [← orderOf_injective _
        (mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot) c]
      exact hβ
    exact inner_not_isPGroup (MulEquiv.refl _)
      (fun c hc2 hc1 => isCharacteristicP_centralizer (RootWeightDatum.ordinary τ) hc2 hc1)
      hopen c hc
  · exact even_GFE_not_isPGroup hτ hf hG2 hK β hβ2 hin

theorem untwisted_model_not_isPGroup
    {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag} {f : ℕ}
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E7 ∨ t = .E8) (hopen : InvolutionCentralizerNotTwoGroup t)
    (hY : ChevalleyExceptionalModel Y t 2 f) (hs : IsSimpleGroup Y)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  have hopenY := hopen Y f hY hs
  obtain ⟨⟨-, hf, hadm⟩, hm⟩ := hY
  have key : ∀ {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8), (τ = .G2 → 2 ≤ f) →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
        Nonempty (Y ≃* adjointGroup τ K)) →
      ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
    intro τ hτ hG2 ⟨K, _, _, hK, ⟨e⟩⟩
    refine Ree.not_isPGroup_of_mulEquiv e (untwisted_not_isPGroup hτ hf hG2 hK ?_) a ha
    intro c hc hP
    exact hopenY (e.symm c) (by rw [MulEquiv.orderOf_eq]; exact hc)
      (hP.of_equiv (centralizerEquiv e.symm c))
  have h2f : 3 ≤ 2 ^ f → 2 ≤ f := fun h => by
    by_contra h'
    push Not at h'
    interval_cases f
    norm_num at h
  rcases ht with rfl | rfl | rfl | rfl
  · exact key (Or.inl rfl) (fun _ => h2f hadm.2)
      (nonempty_mulEquiv_adjointGroup .G2 hm)
  · exact key (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide))
      (nonempty_mulEquiv_adjointGroup .F4 hm)
  · exact key (Or.inr (Or.inr (Or.inl rfl))) (fun h => absurd h (by decide))
      (nonempty_mulEquiv_adjointGroup .E7 hm)
  · exact key (Or.inr (Or.inr (Or.inr rfl))) (fun h => absurd h (by decide))
      (nonempty_mulEquiv_adjointGroup .E8 hm)

end CFSG.ComponentClassification.HarrisLit.L33.E2
