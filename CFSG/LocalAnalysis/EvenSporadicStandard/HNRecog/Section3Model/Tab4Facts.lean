module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.RowModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

structure Tab4Facts : Prop where
  stab_le : ∀ i : Fin 6, Nat.card ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row i).rowP wordB)) ≤
    (![768, 768, 1440, 64, 240, 240] : Fin 6 → ℕ) i
  ne : ∀ i : Fin 6, (tab4Row i).rowP wordB ≠ wordP wordB ∧
    (tab4Row i).rowP wordB ≠ wordP wordA * wordP wordB
  ab : IsConj (wordP wordB) (wordP wordA * wordP wordB)
  row0 : IsConj (wordP wordAZ) (wordP wordB * (tab4Row 0).rowP wordB)
  row1 : IsConj (wordP wordZ) (wordP wordB * (tab4Row 1).rowP wordB)
  row2 : (wordP wordB * (tab4Row 2).rowP wordB) ^ 2 = wordP wordA
  row3 : IsConj (wordP wordZ) ((wordP wordB * (tab4Row 3).rowP wordB) ^ 2)
  row4 : orderOf (wordP wordB * (tab4Row 4).rowP wordB) = 3
  row5 : (wordP wordB * (tab4Row 5).rowP wordB) ^ 3 = wordP wordA
  inj2 : ∃ f : ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row 2).rowP wordB)) →* Z 2 × Sym 6,
    Function.Injective f
  inj4 : ∃ f : ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row 4).rowP wordB)) →* Z 2 × Sym 5,
    Function.Injective f
  inj5 : ∃ f : ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row 5).rowP wordB)) →* Z 2 × Sym 5,
    Function.Injective f

end CFSG.EvenSporadicStandard.HNRecog.Section3Model

end
