module

public import CFSG.Adapters.TauCetiExceptional.BigCellEndgame

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti

theorem innerFieldNormalForm_G2
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {f : ℕ}
    (hf : 1 ≤ f) (E : Type) [Field E] (hE : Nat.card E = p ^ f) : InnerFieldNormalForm .G2 E :=
  fun α => by
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf
      E hE .G2 (Or.inr ⟨rfl, hp3⟩)).1 α
    exact ⟨g, σ, hgσ⟩

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem le_adjointGroup_G2_of_ne_three
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (H : Subgroup (ModGL .G2 L))
    (hCH : adjointGroup .G2 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .G2 P →
      evalMat (natMat .G2 L (h : Module.End L (RootModule .G2 L))) P = 0) :
    H ≤ adjointGroup .G2 L :=
  le_adjointGroup_of_normalForm hasQuadraticNode_G2 hp2 (fun k hk => innerFieldNormalForm_G2
    Fact.out hp2 hp3 (Nat.one_le_iff_ne_zero.2 hk) _ (card_frobeniusFixedSubfield L p k hk))
    H hCH hH

end CFSG.TauCetiBridge.BigCell
