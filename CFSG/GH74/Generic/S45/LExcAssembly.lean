module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenAssembly
public import CFSG.GH74.Generic.S45.LExcGFE
public import CFSG.GH74.Generic.S45.LExcE6
public import CFSG.GH74.Generic.S45.LExcTri

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

theorem noSmallQ8Component_adjointGroup_even {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    NoSmallQ8Component (adjointGroup τ K) := by
  intro β hβ2 hβ1 L hL
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact even_GFE_noSmallQ8 (Or.inl rfl) hf hG2 hK β hβ2 hβ1 hL
  · exact even_GFE_noSmallQ8 (Or.inr (Or.inl rfl)) hf hG2 hK β hβ2 hβ1 hL
  · exact even_E6_noSmallQ8 hf hK β hβ2 hβ1 hL
  · exact even_GFE_noSmallQ8 (Or.inr (Or.inr (Or.inl rfl))) hf hG2 hK β hβ2 hβ1 hL
  · exact even_GFE_noSmallQ8 (Or.inr (Or.inr (Or.inr rfl))) hf hG2 hK β hβ2 hβ1 hL

theorem noSmallQ8Component_of_model_even {W : Type} [Group W] {t : StatedLieTag} {f : ℕ}
    (hW : ChevalleyExceptionalModel W t 2 f) : NoSmallQ8Component W := by
  obtain ⟨⟨-, hf, hadm⟩, hm⟩ := hW
  cases t
  case G2 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
    exact noSmallQ8Component_of_equiv e (noSmallQ8Component_adjointGroup_even (Or.inl rfl) hf
      (fun _ => two_le_of_three_le_two_pow hadm.2) hK)
  case F4 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
    exact noSmallQ8Component_of_equiv e (noSmallQ8Component_adjointGroup_even (Or.inr (Or.inl rfl))
      hf (fun h => absurd h (by decide)) hK)
  case E6 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
    exact noSmallQ8Component_of_equiv e (noSmallQ8Component_adjointGroup_even
      (Or.inr (Or.inr (Or.inl rfl))) hf (fun h => absurd h (by decide)) hK)
  case E7 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
    exact noSmallQ8Component_of_equiv e (noSmallQ8Component_adjointGroup_even
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hf (fun h => absurd h (by decide)) hK)
  case E8 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
    exact noSmallQ8Component_of_equiv e (noSmallQ8Component_adjointGroup_even
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hf (fun h => absurd h (by decide)) hK)
  case twistedE6 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf hm
    exact noSmallQ8Component_of_equiv e fun β hβ2 hβ1 L hL =>
      even_twistedE6_noSmallQ8 hf hK σ hσ β hβ2 hβ1 hL
  case trialityD4 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hm
    exact noSmallQ8Component_of_equiv e fun β hβ2 hβ1 L hL =>
      even_triality_noSmallQ8 hf hK σ hσ β hβ2 hβ1 hL
  all_goals exact hm.elim

end CFSG.ComponentClassification.ExcSelector
