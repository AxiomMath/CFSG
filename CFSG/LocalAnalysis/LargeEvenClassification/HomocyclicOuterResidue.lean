module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoBinaryEndResidue

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem rankTwoBinaryResidue_units_card :
    Nat.card (RankTwoBinaryResidue 1)ˣ = 6 ∧ Nat.card (RankTwoBinaryResidue 0)ˣ = 4 := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

@[expose] def binaryResidueConjugationDifference {F : Type*} [Ring F]
    [Module (ZMod 2) F] (j : Fˣ) : F →ₗ[ZMod 2] F :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := fun x => (j : F) * x * (j⁻¹ : Fˣ).val - x
    map_zero' := by simp
    map_add' := by
      intro x y
      simp only [mul_add, add_mul]
      abel }

theorem binaryResidueConjugationDifference_ker (j : (RankTwoBinaryResidue 1)ˣ)
    (x : RankTwoBinaryResidue 1) :
    binaryResidueConjugationDifference j x = 0 ↔ (j : RankTwoBinaryResidue 1) * x = x * j := by
  change (j : RankTwoBinaryResidue 1) * x * (j⁻¹ : (RankTwoBinaryResidue 1)ˣ).val - x = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    have h' := congrArg (fun z : RankTwoBinaryResidue 1 => z * j.val) h
    simpa only [mul_assoc, Units.inv_mul, mul_one] using h'
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]

theorem homocyclic_residue_involution_centralizer_card :
    ∀ j : (RankTwoBinaryResidue 1)ˣ, j ≠ 1 → j ^ 2 = 1 →
      Fintype.card {x : RankTwoBinaryResidue 1 // j.val * x = x * j.val} = 4 ∧
        Fintype.card {x : RankTwoBinaryResidue 1 // j.val * x = x * j.val ∧ x * x = x} = 2 := by
  decide

private theorem binaryHomocyclicSubmodule_card_bound
    (V : Submodule (ZMod 2) (RankTwoBinaryResidue 1)) {bound : ℕ}
    (hcard : Nat.card V ≤ 2 ^ bound) : Module.finrank (ZMod 2) V ≤ bound := by
  rw [← FiniteField.pow_finrank_eq_natCard 2 V] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard

theorem homocyclic_residue_outer_saving (j : (RankTwoBinaryResidue 1)ˣ)
    (hj : j ≠ 1) (hsquare : j ^ 2 = 1)
    (W : Submodule (ZMod 2) (RankTwoBinaryResidue 1)) :
    Module.finrank (ZMod 2) W ≤
      Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) +
        Module.finrank (ZMod 2) (W.map (binaryResidueConjugationDifference j)) + 1 := by
  let delta := binaryResidueConjugationDifference j
  let restriction := delta.domRestrict W
  have hdimension := restriction.finrank_range_add_finrank_ker
  have hrange : restriction.range = W.map delta := by
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, w.property, hw⟩
    · rintro ⟨w, hw, heq⟩
      exact ⟨⟨w, hw⟩, heq⟩
  rw [hrange] at hdimension
  have hcentral := homocyclic_residue_involution_centralizer_card j hj hsquare
  let toCentralizer : restriction.ker → {x : RankTwoBinaryResidue 1 // j.val * x = x * j.val} :=
    fun x => ⟨x.val.val, (binaryResidueConjugationDifference_ker j _).mp x.property⟩
  have hinjective : Function.Injective toCentralizer := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val) h
  have hcard := Nat.card_le_card_of_injective toCentralizer hinjective
  rw [Nat.card_eq_fintype_card (α := {x : RankTwoBinaryResidue 1 // j.val * x = x * j.val}),
    hcentral.1] at hcard
  have hkerRank : Module.finrank (ZMod 2) restriction.ker ≤ 2 := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 restriction.ker] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  by_cases hzero : residueSquareCommutatorSpan W = ⊥
  · have hidempotent (w : W) : (w : RankTwoBinaryResidue 1) * w = w := by
      have h := residue_square_mem_span W w.property
      rw [hzero] at h
      have h' : (w : RankTwoBinaryResidue 1) + w * w = 0 := h
      exact (eq_neg_of_add_eq_zero_right h').trans (ZModModule.neg_eq_self w.val)
    let toIdempotent : restriction.ker →
        {x : RankTwoBinaryResidue 1 // j.val * x = x * j.val ∧ x * x = x} :=
      fun x => ⟨x.val.val, (binaryResidueConjugationDifference_ker j _).mp x.property, hidempotent x.val⟩
    have hinj : Function.Injective toIdempotent := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z => z.val) h
    have hc := Nat.card_le_card_of_injective toIdempotent hinj
    rw [Nat.card_eq_fintype_card (α :=
      {x : RankTwoBinaryResidue 1 // j.val * x = x * j.val ∧ x * x = x}), hcentral.2,
      ← FiniteField.pow_finrank_eq_natCard 2 restriction.ker] at hc
    have hk : Module.finrank (ZMod 2) restriction.ker ≤ 1 :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
    change Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) +
      Module.finrank (ZMod 2) (W.map delta) + 1
    omega
  · have hc : Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) ≠ 0 :=
      mt Submodule.finrank_eq_zero.mp hzero
    change Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) +
      Module.finrank (ZMod 2) (W.map delta) + 1
    omega

end CFSG.LargeEvenClassification.Helpers
