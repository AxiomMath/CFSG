module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.PrincipalNorm

public noncomputable section

namespace CFSG.Wreathed

open CFSG.LargeEvenClassification.Helpers

universe u

@[expose] def additiveAutEquivEndUnits (A : Type u) [AddCommGroup A] :
    Multiplicative (AddAut A) ≃* (AddMonoid.End A)ˣ where
  toFun e := additiveAutomorphismUnits A e.toAdd
  invFun e := Multiplicative.ofAdd {
    toFun := e.val
    invFun := e.inv
    left_inv x := by
      exact congrArg (fun f : AddMonoid.End A => f x) e.inv_val
    right_inv x := by
      exact congrArg (fun f : AddMonoid.End A => f x) e.val_inv
    map_add' := map_add e.val }
  left_inv e := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro x
    rfl
  right_inv e := by
    apply Units.ext
    apply AddMonoid.End.ext
    intro x
    rfl
  map_mul' e f := by
    apply Units.ext
    apply AddMonoid.End.ext
    intro x
    rfl

@[expose] def cyclicTimesTwoAutEquivEndUnits (m : ℕ) :
    MulAut (Multiplicative (ZMod m) × Multiplicative (ZMod 2)) ≃*
      (AddMonoid.End (ZMod m × ZMod 2))ˣ :=
  ((MulAut.congr (MulEquiv.prodMultiplicative (ZMod m) (ZMod 2)).symm).trans
    (MulAutMultiplicative (ZMod m × ZMod 2))).trans
      (additiveAutEquivEndUnits (ZMod m × ZMod 2))

@[expose] def cyclicTimesTwoNativeEquiv (k : ℕ) :
    Multiplicative (CyclicTwoSpace k) ≃*
      Multiplicative (ZMod (2 ^ (k + 3))) × Multiplicative (ZMod 2) :=
  (MulEquiv.prodMultiplicative _ _).trans
    (((ZMod.ringEquivCongr (pow_succ 2 (k + 2)).symm).toAddEquiv.toMultiplicative).prodCongr
      (MulEquiv.refl _))

@[expose] def cyclicTimesTwoAutEquivNative (k : ℕ) :
    MulAut (Multiplicative (ZMod (2 ^ (k + 3))) × Multiplicative (ZMod 2)) ≃*
      CyclicTwoAut k :=
  ((MulAut.congr (cyclicTimesTwoNativeEquiv k).symm).trans
    (MulAutMultiplicative (CyclicTwoSpace k))).trans
      (additiveAutEquivEndUnits (CyclicTwoSpace k))

theorem cyclicTimesTwoAut_card_succ_three (k : ℕ) :
    Nat.card (MulAut (Multiplicative (ZMod (2 ^ (k + 3))) × Multiplicative (ZMod 2))) =
      2 ^ (k + 4) := by
  rw [Nat.card_congr (cyclicTimesTwoAutEquivNative k).toEquiv]
  exact cyclicTwoAut_card k

@[expose] def cyclicFourTimesTwoUnitCoefficients (c : CyclicPairCoefficients 2 2) : Prop :=
  (c.1.1 = 1 ∨ c.1.1 = 3) ∧ c.2.2 = 1

instance cyclicFourTimesTwoUnitCoefficients_decidable (c : CyclicPairCoefficients 2 2) :
    Decidable (cyclicFourTimesTwoUnitCoefficients c) :=
  inferInstanceAs (Decidable ((c.1.1 = 1 ∨ c.1.1 = 3) ∧ c.2.2 = 1))

theorem cyclicFourTimesTwoCoefficient_invertible_iff (c : CyclicPairCoefficients 2 2) :
    (∃ b : CyclicPairCoefficients 2 2,
      cyclicPairCoefficientProduct 2 2 c b = ((1, 0), (0, 1)) ∧
      cyclicPairCoefficientProduct 2 2 b c = ((1, 0), (0, 1))) ↔
      cyclicFourTimesTwoUnitCoefficients c := by
  simp only [cyclicPairCoefficientProduct, scaledCyclicInclusion_apply, cyclicReduction_apply]
  revert c
  decide +kernel

theorem cyclicFourTimesTwoEnd_isUnit_iff (f : AddMonoid.End (CyclicPair 2 2)) :
    IsUnit f ↔ cyclicFourTimesTwoUnitCoefficients (cyclicPairEndCoefficients 2 2 f) := by
  rw [← cyclicFourTimesTwoCoefficient_invertible_iff, isUnit_iff_exists]
  constructor
  · rintro ⟨g, hfg, hgf⟩
    refine ⟨cyclicPairEndCoefficients 2 2 g, ?_, ?_⟩
    · rw [← cyclicPairEndCoefficients_mul, hfg, cyclicPairEndCoefficients_one]
    · rw [← cyclicPairEndCoefficients_mul, hgf, cyclicPairEndCoefficients_one]
  · rintro ⟨b, hfb, hbf⟩
    refine ⟨cyclicPairEndFromCoefficients 2 2 b, ?_, ?_⟩
    · apply cyclicPairEndCoefficients_injective 2 2
      rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
        cyclicPairEndCoefficients_one]
      exact hfb
    · apply cyclicPairEndCoefficients_injective 2 2
      rw [cyclicPairEndCoefficients_mul, cyclicPairEndCoefficients_from,
        cyclicPairEndCoefficients_one]
      exact hbf

@[expose] def cyclicFourTimesTwoUnitCoefficientEquiv :
    (AddMonoid.End (CyclicPair 2 2))ˣ ≃
      {c : CyclicPairCoefficients 2 2 // cyclicFourTimesTwoUnitCoefficients c} :=
  (Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv).trans
    ((cyclicPairEndCoefficientEquiv 2 2).subtypeEquiv cyclicFourTimesTwoEnd_isUnit_iff)

theorem cyclicFourTimesTwoEndUnits_card : Nat.card (AddMonoid.End (CyclicPair 2 2))ˣ = 8 := by
  rw [Nat.card_congr cyclicFourTimesTwoUnitCoefficientEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem cyclicTimesTwoAut_card_two :
    Nat.card (MulAut (Multiplicative (ZMod 4) × Multiplicative (ZMod 2))) = 8 := by
  rw [Nat.card_congr (cyclicTimesTwoAutEquivEndUnits 4).toEquiv]
  exact cyclicFourTimesTwoEndUnits_card

theorem cyclicTimesTwoAut_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (MulAut (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2))) =
      2 ^ (n + 1) := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    exact cyclicTimesTwoAut_card_two
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : 3 ≤ n)
    rw [show n = k + 3 by omega]
    simpa only [Nat.add_assoc] using cyclicTimesTwoAut_card_succ_three k

theorem cyclicTimesTwoAut_isPGroup (n : ℕ) (hn : 2 ≤ n) :
    IsPGroup 2 (MulAut (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2))) :=
  IsPGroup.of_card (cyclicTimesTwoAut_card n hn)

theorem cyclicTimesTwoAut_card_of_equiv {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n)
    (e : G ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)) :
    Nat.card (MulAut G) = 2 ^ (n + 1) := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact cyclicTimesTwoAut_card n hn

theorem cyclicTimesTwoAut_isPGroup_of_equiv {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n)
    (e : G ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)) :
    IsPGroup 2 (MulAut G) :=
  (cyclicTimesTwoAut_isPGroup n hn).of_equiv (MulAut.congr e).symm

end CFSG.Wreathed
