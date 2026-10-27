module

public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourLiftSquare
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourSubgroup

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def smallCfourObstructionMatrix : RankTwoBinaryResidue 1 := ((1, 0), (1, 0))

theorem smallCfour_full_action_coordinate_contradiction :
    ∀ z c w : ZMod 4 × ZMod 4,
      smallCfourBinaryVector z ≠ 0 →
      smallCfourBinaryApply smallCfourUpper (smallCfourBinaryVector z) = 0 →
      smallCfourMatrixApply (smallCfourEvenMatrix smallCfourObstructionMatrix) z =
        z + smallCfourMatrixApply (smallCfourEvenMatrix smallCfourUpper) c + c →
      c + smallCfourMatrixApply (smallCfourEvenMatrix smallCfourObstructionMatrix) c =
        ((2 * w.2, 0) : ZMod 4 × ZMod 4) → False := by
  intro z c w hnonzero hkilled hfirst hsecond
  have hfirstCoordinate := congrArg Prod.fst hfirst
  have hsecondCoordinate := congrArg Prod.snd hsecond
  have hF : smallCfourEvenMatrix smallCfourObstructionMatrix = (((3, 0), (2, 1)) : ResidualRing 1) := by
    apply Prod.ext <;> apply Prod.ext <;> decide +kernel
  have hN : smallCfourEvenMatrix smallCfourUpper = (((1, 2), (0, 1)) : ResidualRing 1) := by
    apply Prod.ext <;> apply Prod.ext <;> decide +kernel
  rw [hF, hN] at hfirstCoordinate
  rw [hF] at hsecondCoordinate
  simp only [smallCfourMatrixApply, Prod.fst_add, Prod.snd_add, zero_mul, one_mul, add_zero]
    at hfirstCoordinate hsecondCoordinate
  change 3 * z.1 = z.1 + (c.1 + 2 * c.2) + c.1 at hfirstCoordinate
  change c.2 + (2 * c.1 + c.2) = 0 at hsecondCoordinate
  have h : ∀ z c : ZMod 4 × ZMod 4,
      smallCfourBinaryVector z ≠ 0 →
      smallCfourBinaryApply smallCfourUpper (smallCfourBinaryVector z) = 0 →
      3 * z.1 = z.1 + (c.1 + 2 * c.2) + c.1 → c.2 + (2 * c.1 + c.2) = 0 → False := by
    decide +kernel
  exact h z c hnonzero hkilled hfirstCoordinate hsecondCoordinate

theorem commuting_involution_lift_equations {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal]
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (t s : S) (a : A) (hsquare : (a : S) = t ^ 2)
    (htwoT : MulAut.conjNormal (H := A) t ^ 2 = 1)
    (htwoS : MulAut.conjNormal (H := A) s ^ 2 = 1)
    (hcommute : Commute (MulAut.conjNormal (H := A) t) (MulAut.conjNormal (H := A) s)) :
    ∃ c w : A,
      MulAut.conjNormal (H := A) s a = a * MulAut.conjNormal (H := A) t c * c ∧
      c * MulAut.conjNormal (H := A) s c = MulAut.conjNormal (H := A) t w * w⁻¹ := by
  let action : S →* MulAut A := MulAut.conjNormal
  have hkernel : action.ker = A := (conjNormal_ker_eq_centralizer A).trans hselfCentralizing
  have hcommutator : t⁻¹ * s * t * s⁻¹ ∈ A := by
    apply hkernel.le
    change action (t⁻¹ * s * t * s⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hcommute' : Commute (action t) (action s) := hcommute
    rw [mul_assoc (action t)⁻¹, hcommute'.eq.symm]
    group
  let c : A := ⟨t⁻¹ * s * t * s⁻¹, hcommutator⟩
  have hw : s ^ 2 ∈ A := by
    apply hkernel.le
    change action (s ^ 2) = 1
    rw [map_pow]
    exact htwoS
  let w : A := ⟨s ^ 2, hw⟩
  have htInverse : MulAut.conjNormal (H := A) t⁻¹ = MulAut.conjNormal (H := A) t := by
    rw [map_inv]
    have hproduct : MulAut.conjNormal (H := A) t * MulAut.conjNormal (H := A) t = 1 := by
      simpa only [pow_two] using htwoT
    exact (eq_inv_of_mul_eq_one_left hproduct).symm
  have hTc (b : A) : t⁻¹ * (b : S) * t = (MulAut.conjNormal (H := A) t b : S) := by
    rw [← htInverse, MulAut.conjNormal_apply, inv_inv]
  have hconjugateT : s * t * s⁻¹ = t * c := by
    change s * t * s⁻¹ = t * (t⁻¹ * s * t * s⁻¹)
    group
  refine ⟨c, w, ?_, ?_⟩
  · apply Subtype.ext
    change s * (a : S) * s⁻¹ = (a : S) * (MulAut.conjNormal (H := A) t c : S) * c
    rw [hsquare, ← hTc]
    calc
      s * t ^ 2 * s⁻¹ = (s * t * s⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = (t * c) ^ 2 := by rw [hconjugateT]
      _ = t ^ 2 * (t⁻¹ * (c : S) * t) * c := by simp only [pow_two]; group
  · have hdouble : s ^ 2 * t * (s ^ 2)⁻¹ = t * c * (MulAut.conjNormal (H := A) s c : S) := by
      rw [MulAut.conjNormal_apply]
      calc
        s ^ 2 * t * (s ^ 2)⁻¹ = s * (s * t * s⁻¹) * s⁻¹ := by simp only [pow_two]; group
        _ = s * (t * c) * s⁻¹ := by rw [hconjugateT]
        _ = (s * t * s⁻¹) * (s * (c : S) * s⁻¹) := by group
        _ = t * c * (s * (c : S) * s⁻¹) := by rw [hconjugateT]
    have hdoubleW : s ^ 2 * t * (s ^ 2)⁻¹ =
        t * (MulAut.conjNormal (H := A) t w : S) * w⁻¹ := by
      rw [← hTc]
      change (w : S) * t * (w : S)⁻¹ = t * (t⁻¹ * (w : S) * t) * (w : S)⁻¹
      group
    apply Subtype.ext
    change (c : S) * (MulAut.conjNormal (H := A) s c : S) =
      (MulAut.conjNormal (H := A) t w : S) * (w : S)⁻¹
    exact mul_left_cancel (by simpa only [mul_assoc, Subgroup.coe_inv] using hdouble.symm.trans hdoubleW)

theorem small_cfour_full_action_obstruction {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4))
    (hle : ((smallCfourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range ≤ smallCfourSylow) :
    ((smallCfourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range ≠ smallCfourSylow := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let equivalence := smallCfourAutomorphismEquiv hcommutative coordinates
  let action := equivalence.toMonoidHom.comp (MulAut.conjNormal (H := A))
  intro hfull
  have hN : smallCfourEvenUnit smallCfourUpper ∈ action.range := by
    rw [hfull]
    exact smallCfourEvenSubgroup_le_sylow ⟨Multiplicative.ofAdd smallCfourUpper, rfl⟩
  have hF : smallCfourEvenUnit smallCfourObstructionMatrix ∈ action.range := by
    rw [hfull]
    exact smallCfourEvenSubgroup_le_sylow ⟨Multiplicative.ofAdd smallCfourObstructionMatrix, rfl⟩
  obtain ⟨t, ht⟩ := hN
  obtain ⟨s, hs⟩ := hF
  change equivalence (MulAut.conjNormal (H := A) t) = smallCfourEvenUnit smallCfourUpper at ht
  change equivalence (MulAut.conjNormal (H := A) s) = smallCfourEvenUnit smallCfourObstructionMatrix at hs
  have hcentral (g : S) : Commute (smallCfourEvenUnit smallCfourUpper) (action g) :=
    smallCfourCentralShear _ (hle ⟨g, rfl⟩)
  obtain ⟨square, hsquare, _, hnonzero, hkilled, _⟩ := small_cfour_central_action_lift_square A
    hcommutative hselfCentralizing hnoEight coordinates smallCfourUpper (by decide +kernel)
    (by decide +kernel) hcentral t ht
  have htwoT : MulAut.conjNormal (H := A) t ^ 2 = 1 := by
    apply equivalence.injective
    rw [map_pow, map_one, ht]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_two]
    exact smallCfourEvenMatrix_square _
  have htwoS : MulAut.conjNormal (H := A) s ^ 2 = 1 := by
    apply equivalence.injective
    rw [map_pow, map_one, hs]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_two]
    exact smallCfourEvenMatrix_square _
  have hcommute : Commute (MulAut.conjNormal (H := A) t) (MulAut.conjNormal (H := A) s) := by
    apply equivalence.injective
    rw [map_mul, map_mul, ht, hs]
    exact (smallCfour_even_units_commute _ _ ⟨Multiplicative.ofAdd smallCfourUpper, rfl⟩
      ⟨Multiplicative.ofAdd smallCfourObstructionMatrix, rfl⟩).eq
  obtain ⟨c, w, heqSquare, heqDouble⟩ := commuting_involution_lift_equations A
    hselfCentralizing t s square hsquare htwoT htwoS hcommute
  have heq1 := congrArg (fun a : A => coordinates (Additive.ofMul a)) heqSquare
  have heq2 := congrArg (fun a : A => coordinates (Additive.ofMul a)) heqDouble
  change coordinates (Additive.ofMul (MulAut.conjNormal (H := A) s square)) =
    coordinates (Additive.ofMul square + Additive.ofMul (MulAut.conjNormal (H := A) t c) + Additive.ofMul c) at heq1
  change coordinates (Additive.ofMul c + Additive.ofMul (MulAut.conjNormal (H := A) s c)) =
    coordinates (Additive.ofMul (MulAut.conjNormal (H := A) t w) + Additive.ofMul (w⁻¹)) at heq2
  rw [map_add, map_add, smallCfourAutomorphismEquiv_apply hcommutative,
    smallCfourAutomorphismEquiv_apply hcommutative, ht, hs] at heq1
  rw [map_add, map_add, smallCfourAutomorphismEquiv_apply hcommutative,
    smallCfourAutomorphismEquiv_apply hcommutative, ht, hs] at heq2
  have hinverseCoordinates : coordinates (Additive.ofMul (w⁻¹)) = -coordinates (Additive.ofMul w) :=
    map_neg coordinates (Additive.ofMul w)
  rw [hinverseCoordinates] at heq2
  change coordinates (Additive.ofMul c) +
    smallCfourMatrixApply (smallCfourEvenMatrix smallCfourObstructionMatrix) (coordinates (Additive.ofMul c)) =
    smallCfourMatrixApply (smallCfourEvenMatrix smallCfourUpper) (coordinates (Additive.ofMul w)) +
      -coordinates (Additive.ofMul w) at heq2
  have hdifference : ∀ x : ZMod 4 × ZMod 4,
      smallCfourMatrixApply (smallCfourEvenMatrix smallCfourUpper) x + -x = (2 * x.2, 0) := by
    decide +kernel
  rw [hdifference] at heq2
  exact smallCfour_full_action_coordinate_contradiction _ _ _ hnonzero hkilled heq1 heq2

end CFSG.LargeEvenClassification.Helpers
