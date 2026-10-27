module

public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutQuotientFaithfulness
public import CFSG.LinearAlgebra.CoprimeActions.PrimeOrderBinaryLinearDimensionBound

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutomizerWidth

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

theorem order_le_twice_width {E : Type*} [Group E] [Finite E]
    (hE : CFSG.IsExtraspecialPGroup 2 E) {w : ℕ}
    (hcard : Nat.card E = 2 ^ (1 + 2 * w)) {q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2)
    (C : Subgroup (MulAut E)) (hC : Nat.card C = q) :
    orderOf (2 : ZMod q) ≤ 2 * w := by
  haveI : Fact (CFSG.IsExtraspecialPGroup 2 E) := ⟨hE⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; exact hq.ne_zero)
  haveI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by
    have : 1 < Nat.card C := by rw [hC]; exact hq.one_lt
    simpa [Nat.card_eq_fintype_card] using this)
  obtain ⟨g, hg⟩ := exists_ne (1 : C)
  have hinj := CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutQuotientFaithfulness.injective hq hq2 hE C
    (IsPGroup.of_card (n := 1) (by simpa using hC))
  have hgq : g ^ q = 1 := by
    rw [← hC]; exact pow_card_eq_one'
  have hdim := finrank_eq (E := E) hcard
  haveI : FiniteDimensional (ZMod 2) (QSpace E) := by
    haveI : Finite (QSpace E) := inferInstanceAs (Finite (Additive (E ⧸ Subgroup.center E)))
    exact Module.Finite.of_finite
  have := CFSG.LinearAlgebra.CoprimeActions.PrimeOrderBinaryLinearDimensionBound.order_le_finrank q hq2
    (linearAction E (g : MulAut E))
    (by rw [← map_pow]; rw [← Subgroup.coe_pow, hgq]; simp)
    (by
      intro h1
      apply hg
      apply hinj
      rw [map_one]
      show CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.quotientHom E (g : MulAut E) = 1
      ext x
      induction x using QuotientGroup.induction_on with | _ a => ?_
      have := congrArg (fun f => f (Additive.ofMul (a : E ⧸ Subgroup.center E))) h1
      rw [linearAction_ofMul_mk] at this
      exact Additive.ofMul.injective this)
  omega

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutomizerWidth
