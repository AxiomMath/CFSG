module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

structure WeakHyp (C : Type) [Group C] (Q : Subgroup C) [Q.Normal] : Prop
    extends IsExtraspecialPlusByA5WrTwoWith C Q where
  irreducible : ∀ W : Subgroup C, centerOf Q ≤ W → W ≤ Q →
    (∀ g ∈ commutator C, ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = centerOf Q ∨ W = Q

theorem WeakHyp.of_cIrreducible
    (hE : IsExtraspecialPlusByA5WrTwoWith C Q) (hI : Section3.CIrreducible C Q) : WeakHyp C Q :=
  { hE with irreducible := hI }

theorem WeakHyp.of_aschbacherHyp (hC : AschbacherHyp C Q) : WeakHyp C Q :=
  { hC.toIsExtraspecialPlusByA5WrTwoWith with irreducible := hC.irreducible }

theorem WeakHyp.finite_Q (hC : WeakHyp C Q) : Finite Q :=
  hC.plus.finite

theorem WeakHyp.finite (hC : WeakHyp C Q) : Finite C := by
  haveI : Finite Q := hC.finite_Q
  haveI : Finite (C ⧸ Q) := by
    obtain ⟨e⟩ := hC.quotient
    exact Finite.of_equiv _ e.toEquiv.symm
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := Q)).symm

theorem WeakHyp.isExtraspecialPGroup (hC : WeakHyp C Q) : IsExtraspecialPGroup 2 Q :=
  hC.plus.isExtraspecialPGroup

end CFSG.EvenSporadicStandard.HNRecog.CSide
