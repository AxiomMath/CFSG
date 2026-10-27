module

public import CFSG.CharacterTheory.Wreathed.ConditionalLinearAugmentationTwistsBlocks

public section

open scoped Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers

variable {E : Type} [Group E] [Fintype E]

theorem mem_coefficientBlock_of_odd_eq_span (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {χ : basis.index}
    {f : E → ℂ}
    (hf : f ∈ Submodule.span ℂ
      (BlocksBlockOf ideal E (basis.representation principal).character))
    (hχf : ∀ y : E, Odd (orderOf y) → (basis.representation χ).character y = f y) :
    χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
  by_contra hχ
  set D : Set E := {y | Odd (orderOf y)} with hDdef
  have hD : ∀ g h gp hp : E, g ∈ D → BlocksIsPPart 2 g gp → BlocksIsPPart 2 h hp →
      IsConj gp hp → h ∈ D := fun g h gp hp hg hgp hhp hconj =>
    odd_orderOf_of_isConj_pPart hg hgp hhp hconj
  have hχirr := CFSG.BlockBasics.basis_character_mem_irr basis χ
  set B := BlocksBlockOf ideal E (basis.representation χ).character with hBdef
  set C := BlocksBlockOf ideal E (basis.representation principal).character with hCdef
  have hB : BlocksIsBlock ideal E B := ⟨_, hχirr, rfl⟩
  have hC : BlocksIsBlock ideal E C :=
    ⟨_, CFSG.BlockBasics.basis_character_mem_irr basis principal, rfl⟩
  have hBC : B ≠ C := by
    intro h
    apply hχ
    rw [mem_coefficientBlock_iff_mem_blockOf, ← hCdef, ← h]
    exact mem_blockOf_self ideal hχirr
  obtain ⟨-, -, horth⟩ := CFSG.BlockBasics.block_section_restriction_stability 2 Nat.prime_two
    ideal inferInstance E B hB D hD
  have h0 := horth C hC hBC _ (Submodule.subset_span (mem_blockOf_self ideal hχirr)) f hf
  have hind : D.indicator f = D.indicator (basis.representation χ).character := by
    funext y
    by_cases hy : y ∈ D
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hχf y hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  rw [hind] at h0
  have h1 : (1 : E) ∈ D := by
    change Odd (orderOf (1 : E))
    rw [orderOf_one]
    exact odd_one
  have hzero := congrFun (CFSG.blocksInnerProduct_self_zero _ h0) 1
  rw [Set.indicator_of_mem h1, Pi.zero_apply] at hzero
  have hpos := CFSG.blocksIrr_identity_re_pos
    ⟨_, CFSG.BlockBasics.basis_character_mem_irr basis χ⟩
  change 0 < ((basis.representation χ).character 1).re at hpos
  rw [hzero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

theorem one_add_mem_span_principalBlock (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {Φ : E → ℂ}
    (hΦ : ∃ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation l).character = Φ) :
    (1 + Φ) ∈ Submodule.span ℂ
      (BlocksBlockOf ideal E (basis.representation principal).character) := by
  obtain ⟨l, hl, hlΦ⟩ := hΦ
  refine Submodule.add_mem _ (Submodule.subset_span ?_) (Submodule.subset_span ?_)
  · rw [← hprincipal]
    exact mem_blockOf_self ideal (CFSG.BlockBasics.basis_character_mem_irr basis principal)
  · rw [← hlΦ]
    exact (mem_coefficientBlock_iff_mem_blockOf basis ideal principal l).mp hl

end CFSG.Wreathed
