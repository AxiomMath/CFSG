module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1SmallRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Three
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Row
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1G2ThreeRow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1E8

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem nonempty_adjointGroup_equiv_adjointQuotient
    (τ : Tag) (K : Type) [Field K] : Nonempty (adjointGroup τ K ≃* AdjointQuotient τ K) :=
  ⟨QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field τ K).symm)⟩

theorem burgOddCoreRow_of_untwistedChevalleyModel
    {L : Type} [Group L] {τ : Tag} {q : ℕ} (h : UntwistedChevalleyModel L τ q)
    (hrow : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      BurgOddCoreRow (adjointGroup τ K)) : BurgOddCoreRow L := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := nonempty_adjointGroup_equiv_adjointQuotient τ K
  exact burgOddCoreRow_of_mulEquiv (e'.trans e.symm) (hrow K hK)

theorem burgOddCoreRow_G2
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : BurgOddCoreRow (adjointGroup .G2 K) := by
  by_cases hp3 : p = 3
  · subst hp3
    have hf := one_le_of_card_eq_pow hK
    have : CharP K ReeTag.G2.prime :=
      finite_field_prime_power_characteristic Nat.prime_three hf hK
    exact burgOddCoreRow_G2_three hf hK fun a ha =>
      burgE1ReeCosetInput_holds K a (by rw [hK, ha])
  · exact burgOddCoreRow_G2_of_ne_three hp hp2 hp3 hK

theorem burgoyneExcOddCoreInput_of_residue
    (h : BurgE1Residue) : Burgoyne.BurgoyneExcOddCoreInput := by
  refine burgoyneExcOddCoreInput_of_row fun L _ _ _ _ τ n p f hτ hτ' hp2 hL => ?_
  rcases hL with ⟨hcl, -⟩ | ⟨rfl, hex, hmod⟩ | ⟨rfl, hree, hmod⟩ | ⟨rfl, rfl, -⟩
  · exfalso
    cases τ <;> simp [classicalTags, Burgoyne.oddExceptionalTags] at hcl hτ
  · cases τ <;>
      try (exfalso; simp [chevalleyExceptionalTags, Burgoyne.torusExceptionalTags] at hex hτ'; done)
    ·
      obtain ⟨⟨hp, hf, -⟩, hU⟩ := hmod
      exact burgOddCoreRow_of_untwistedChevalleyModel hU fun K _ _ hK =>
        burgOddCoreRow_G2 hp hp2 hK
    ·
      obtain ⟨⟨hp, hf, -⟩, hU⟩ := hmod
      exact burgOddCoreRow_of_untwistedChevalleyModel hU fun K _ _ hK =>
        burgOddCoreRow_F4 hp hp2 hK
    ·
      obtain ⟨⟨hp, hf, -⟩, hU⟩ := hmod
      exact burgOddCoreRow_of_untwistedChevalleyModel hU fun K _ _ hK =>
        burgOddCoreRow_E8 hp hp2 hK
    ·
      obtain ⟨⟨hp, hf, -⟩, hT⟩ := hmod
      obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hT
      have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
      exact burgOddCoreRow_of_mulEquiv e.symm (burgE1D4RowInput_holds h (p ^ f) K σ hq hK hσ)
  · cases τ <;>
      try (exfalso; simp [reeTitsTags, Burgoyne.oddExceptionalTags] at hree hτ; done)
    obtain ⟨⟨hp, hf, -, hp3, -, hf3⟩, a, hfa, K, _, _, _, hK, ⟨e⟩⟩ :=
      ((ree_tits_relation_graph_identification).2 L p f).1.1 hmod
    subst hp3 hfa
    have ha1 : 1 ≤ a := by omega
    obtain ⟨e'⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 ha1 hK
    exact burgOddCoreRow_of_mulEquiv (e.trans e').symm
      (burgOddCoreRow_reeGamma ha1 hK (burgE1SmallReeInput_holds K a ha1 hK))
  · exfalso
    simp [Burgoyne.oddExceptionalTags] at hτ

theorem burgoyneExcOddCoreInput_holds
    : Burgoyne.BurgoyneExcOddCoreInput :=
  burgoyneExcOddCoreInput_of_residue burgE1D4OrderThreeInput_holds

end CFSG.ComponentClassification.CatLeafProof
