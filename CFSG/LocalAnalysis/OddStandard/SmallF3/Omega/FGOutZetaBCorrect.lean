module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma zetaBCorrect_card_two {H : Type*} [Group H] (h2 : Nat.card H = 2)
    {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  letI := Fintype.ofFinite H
  have hcard : Fintype.card H = 2 := by rw [← Nat.card_eq_fintype_card, h2]
  have h3 : ({1, a, b} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩),
        Finset.card_insert_of_notMem (by simpa using hab),
        Finset.card_singleton]
  have hle := Finset.card_le_univ ({1, a, b} : Finset H)
  rw [h3, hcard] at hle
  omega

private lemma zetaBCorrect_units_zmod3 : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide

private lemma zetaBCorrect_neg_one_not_isSquare : ¬ IsSquare (-1 : (ZMod 3)ˣ) := by decide

private lemma zetaBCorrect_squareClass_neg_one_ne_zero :
    TauCeti.squareClass (-1 : (ZMod 3)ˣ) ≠ 0 := by
  intro h
  exact zetaBCorrect_neg_one_not_isSquare ((TauCeti.squareClass_eq_zero_iff _).mp h)

private lemma zetaBCorrect_squareClassGroup_zmod3 (x : TauCeti.SquareClassGroup (ZMod 3)) :
    x = 0 ∨ x = TauCeti.squareClass (-1 : (ZMod 3)ˣ) := by
  have h := zetaBCorrect_units_zmod3 (Additive.toMul (Quotient.out x))
  rw [← TauCeti.squareClass_toMul_out x]
  rcases h with h | h <;> rw [h]
  · left
    rw [TauCeti.squareClass_eq_zero_iff]
    exact ⟨1, by simp⟩
  · right
    rfl

private lemma zetaBCorrect_card_sqclass :
    Nat.card (Multiplicative (TauCeti.SquareClassGroup (ZMod 3))) = 2 := by
  rw [Nat.card_eq_two_iff' 1]
  refine ⟨Multiplicative.ofAdd (TauCeti.squareClass (-1 : (ZMod 3)ˣ)), ?_, fun y hy => ?_⟩
  · intro h
    exact zetaBCorrect_squareClass_neg_one_ne_zero
      (by simpa using congrArg Multiplicative.toAdd h)
  · rcases zetaBCorrect_squareClassGroup_zmod3 (Multiplicative.toAdd y) with h | h
    · exact absurd (by simpa using congrArg Multiplicative.ofAdd h : y = 1) hy
    · simpa using congrArg Multiplicative.ofAdd h

private lemma zetaBCorrect_inv_mul_mem (hQ : Q.Nondegenerate) {o g : OGroup Q}
    (ho1 : (detSpinorNorm hQ o).1 = 1) (ho2 : (detSpinorNorm hQ o).2 ≠ 1)
    (hg1 : (detSpinorNorm hQ g).1 = 1) (hg2 : (detSpinorNorm hQ g).2 ≠ 1) :
    o⁻¹ * g ∈ omegaGroup hQ := by
  rw [mem_omegaGroup_iff]
  have hcomp : detSpinorNorm hQ (o⁻¹ * g) =
      (detSpinorNorm hQ o)⁻¹ * detSpinorNorm hQ g := by
    rw [map_mul, map_inv]
  rw [hcomp]
  have heq2 : (detSpinorNorm hQ o).2 = (detSpinorNorm hQ g).2 :=
    zetaBCorrect_card_two zetaBCorrect_card_sqclass ho2 hg2
  apply Prod.ext
  · simp [ho1, hg1]
  · simp [heq2]

theorem zetaCorrect_holds : ZetaCorrect := by
  intro G _ _ L V _ _ _ Q hQ φ hφ w o hcover ho1 ho2 g hg1 hg2
  obtain ⟨ω, hω⟩ := hφ ⟨o⁻¹ * g, zetaBCorrect_inv_mul_mem hQ ho1 ho2 hg1 hg2⟩
  refine ⟨ω, fun l l' hl => ?_⟩
  have hwl'' : (l' : G) = w * ((ω * l * ω⁻¹ : ↥L) : G) * w⁻¹ := by
    rw [hl]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcov := hcover.2 (ω * l * ω⁻¹) l' hwl''
  rw [simAct_orthToSim] at hcov
  rw [hcov]
  have hωval : ((φ ω : omegaGroup hQ) : OGroup Q) = o⁻¹ * g := congrArg Subtype.val hω
  have hphi : ((φ (ω * l * ω⁻¹) : omegaGroup hQ) : OGroup Q) =
      (o⁻¹ * g) * ((φ l : omegaGroup hQ) : OGroup Q) * (o⁻¹ * g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hωval]
  rw [hphi]
  group

end CFSG.OddStandard.SmallF3.Omega
