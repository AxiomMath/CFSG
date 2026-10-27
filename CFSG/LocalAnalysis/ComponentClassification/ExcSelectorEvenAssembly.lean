module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

theorem noSmallComponent_adjointGroup_even {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    NoSmallComponent (adjointGroup τ K) := by
  intro β hβ2 hβ1 L hL hLn
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact even_GFE_noSmall (Or.inl rfl) hf hG2 hK β hβ2 hβ1 hL hLn
  · exact even_GFE_noSmall (Or.inr (Or.inl rfl)) hf hG2 hK β hβ2 hβ1 hL hLn
  · exact even_E6_noSmall hf hK β hβ2 hβ1 hL hLn
  · exact even_GFE_noSmall (Or.inr (Or.inr (Or.inl rfl))) hf hG2 hK β hβ2 hβ1 hL hLn
  · exact even_GFE_noSmall (Or.inr (Or.inr (Or.inr rfl))) hf hG2 hK β hβ2 hβ1 hL hLn

theorem two_le_of_three_le_two_pow {f : ℕ} (h : 3 ≤ 2 ^ f) : 2 ≤ f := by
  by_contra hf
  push Not at hf
  interval_cases f <;> norm_num at h

theorem noSmallComponent_of_model_even {W : Type} [Group W] {t : StatedLieTag} {f : ℕ}
    (hW : ChevalleyExceptionalModel W t 2 f) : NoSmallComponent W := by
  obtain ⟨⟨-, hf, hadm⟩, hm⟩ := hW
  cases t
  case G2 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
    exact noSmallComponent_of_equiv e (noSmallComponent_adjointGroup_even (Or.inl rfl) hf
      (fun _ => two_le_of_three_le_two_pow hadm.2) hK)
  case F4 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
    exact noSmallComponent_of_equiv e (noSmallComponent_adjointGroup_even (Or.inr (Or.inl rfl))
      hf (fun h => absurd h (by decide)) hK)
  case E6 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
    exact noSmallComponent_of_equiv e (noSmallComponent_adjointGroup_even
      (Or.inr (Or.inr (Or.inl rfl))) hf (fun h => absurd h (by decide)) hK)
  case E7 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
    exact noSmallComponent_of_equiv e (noSmallComponent_adjointGroup_even
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hf (fun h => absurd h (by decide)) hK)
  case E8 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
    exact noSmallComponent_of_equiv e (noSmallComponent_adjointGroup_even
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hf (fun h => absurd h (by decide)) hK)
  case twistedE6 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf hm
    exact noSmallComponent_of_equiv e fun β hβ2 hβ1 L hL hLn =>
      even_twistedE6_noSmall hf hK σ hσ β hβ2 hβ1 hL hLn
  case trialityD4 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hm
    exact noSmallComponent_of_equiv e fun β hβ2 hβ1 L hL hLn =>
      even_triality_noSmall hf hK σ hσ β hβ2 hβ1 hL hLn
  all_goals exact hm.elim

end CFSG.ComponentClassification.ExcSelector
