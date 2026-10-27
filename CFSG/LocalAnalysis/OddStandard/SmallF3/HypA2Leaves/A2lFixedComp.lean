module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ProperFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Defs

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.OddStandard.SmallF3.HypA2 (ProperFixedComp)

theorem a2l_properFixedComponent {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {P : Subgroup S} (hP : ProperFixedComp σ P) : CatLeaf.ProperFixedComponent σ P :=
  ⟨hP.1, hP.2.1, LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hP.2.2.2,
    hP.2.2.1⟩

theorem a2l_nonabelian {S : Type} [Group S] {σ : MulAut S} {P : Subgroup S}
    (hP : ProperFixedComp σ P) : ∃ x y : S, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := hP.2.2.2.1.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨((x : ↥(fixedSubgroup σ)) : S), ((y : ↥(fixedSubgroup σ)) : S), fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext (Subtype.ext h))

theorem a2l_orderOf_eq_two {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {σ : MulAut S}
    {P : Subgroup S} (hP : ProperFixedComp σ P) : orderOf σ = 2 := by
  have hpow : σ ^ 2 = 1 := by
    ext x
    simpa [pow_two] using hP.1 x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hpow (a2l_properFixedComponent hP).ne_one

theorem a2l_card_quot_le_fixed {S : Type} [Group S] [Finite S] {σ : MulAut S} {P : Subgroup S}
    (hPF : P ≤ fixedSubgroup σ) : Nat.card (P ⧸ center P) ≤ Nat.card (fixedSubgroup σ) :=
  (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥P))).trans
    (Subgroup.card_le_of_le hPF)

theorem a2l_card_quot_lt {S : Type} [Group S] [Finite S] {P : Subgroup S} (hP : P ≠ ⊤) :
    Nat.card (P ⧸ center P) < Nat.card S := by
  haveI : Nonempty ↥P := ⟨⟨1, P.one_mem⟩⟩
  have hcardP : Nat.card ↥P < Nat.card S := by
    rw [← P.card_mul_index]
    exact lt_mul_of_one_lt_right Nat.card_pos (P.one_lt_index_of_ne_top hP)
  exact lt_of_le_of_lt
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥P))) hcardP

theorem a2l_fusionZStar_equiv {S : Type} [Group S] [Finite S] {σ : MulAut S} {P : Subgroup S}
    (hP : ProperFixedComp σ P) :
    Nonempty (P ⧸ Open.fusionZStar P ≃* P ⧸ center P) := by
  obtain ⟨-, ⟨e⟩⟩ :=
    (a2l_properFixedComponent hP).fusionZStar_equiv_of_quasisimple hP.2.2.2.1
  exact ⟨e.trans (Sol78.centerQuotCongr (Subgroup.subgroupOfEquivOfLe hP.2.1))⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
