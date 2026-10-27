module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrStr

public section

namespace CFSG.EvenSporadicStandard.TwoHS

abbrev W8 : Type := RegularWreathProduct D8 (Multiplicative (ZMod 2))

instance : Fintype W8 :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 (Multiplicative (ZMod 2))).symm

instance : DecidableEq W8 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩; exact RegularWreathProduct.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩)

@[expose] def WrClassFact : Prop :=
  ∀ w : W8, (∃ a : W8, ∀ p : W8, p * w * p⁻¹ = w ∨ p * w * p⁻¹ = a) ↔
    (w.right = 1 ∧ ∀ q : Multiplicative (ZMod 2),
      w.left q = 1 ∨ w.left q = DihedralGroup.r 2)

instance : Decidable WrClassFact := by unfold WrClassFact; infer_instance

end CFSG.EvenSporadicStandard.TwoHS
