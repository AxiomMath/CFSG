module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcInner
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcField
import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_untwisted_F4E8_false
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (β : MulAut (adjointGroup τ F)) (hβ1 : β ≠ 1) (hβ2 : β ^ 2 = 1)
    (hdvd : Nat.card ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ∣ 51840) :
    False := by
  classical
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have hq2 : ∀ {q e : ℕ}, 1 ≤ e → Nat.card F = (q ^ e) ^ 2 → q ≠ 2 := fun {q e} he hFe h => by
    rw [h, ← pow_mul] at hFe
    rw [hFe] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
  have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar F ≠ 3) := by
    rcases hτ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hτ4 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  have hτ3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := by
    rcases hτ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hodd hβ2 with ⟨g, a, hβg⟩ |
    ⟨q, e, hq, he, hFe, δ, hδ, g, a, hβg⟩
  · exact gomi_innerDiag_false hτ3 hodd hβg hβ2 hβ1 hdvd
  · exact gomi_quadField_false hτ4 hq (hq2 he hFe) he hFe δ hδ hβg hβ2 hdvd

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
