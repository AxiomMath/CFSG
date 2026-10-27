module

public import CFSG.LocalAnalysis.LargeEvenClassification.UnequalOuterResidue

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def binaryResidueTwistZeroHom (twist : ZMod 2) (htwist : twist = 0) :
    RankTwoBinaryResidue twist →+* RankTwoBinaryResidue 0 where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    change rankTwoBinaryResidueProduct twist x y = rankTwoBinaryResidueProduct 0 x y
    rw [htwist]

theorem cyclicPair_residual_binary_factor (scale modulus : ℕ)
    [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)]
    (hfour : 4 ∣ modulus) (htwo : 2 ∣ modulus)
    (f : AddMonoid.End (CyclicPair scale modulus)) :
    residualBinaryCoordinates (cyclicPairEndResidualHom scale modulus hfour f) =
      cyclicPairEndBinaryResidueHom scale modulus htwo f := by
  let reduction := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  have hsmall (x : ZMod modulus) :
      reduction (cyclicPairSmallReduction modulus hfour x) =
        cyclicPairSmallBinaryReduction modulus htwo x :=
    DFunLike.congr_fun (RingHom.ext_zmod
      (reduction.comp (cyclicPairSmallReduction modulus hfour))
      (cyclicPairSmallBinaryReduction modulus htwo)) x
  have hlarge (x : ZMod (scale * modulus)) :
      reduction (cyclicPairLargeReduction scale modulus hfour x) =
        cyclicPairLargeBinaryReduction scale modulus htwo x :=
    DFunLike.congr_fun (RingHom.ext_zmod
      (reduction.comp (cyclicPairLargeReduction scale modulus hfour))
      (cyclicPairLargeBinaryReduction scale modulus htwo)) x
  change ((reduction _, reduction _), (reduction _, reduction _)) = ((_, _), (_, _))
  exact Prod.ext (Prod.ext (hlarge _) (hsmall _)) (Prod.ext (hsmall _) (hsmall _))

theorem rank_two_unequal_full_action_generator_bound
    {Abelian : Type*} [AddCommGroup Abelian] (upper lower : ℕ)
    (hunequal : lower < upper) (hlarge : 3 ≤ lower)
    (coordinates : Abelian ≃+ (ZMod (2 ^ upper) × ZMod (2 ^ lower)))
    (Action : Subgroup (AddMonoid.End Abelian)ˣ) (hpgroup : IsPGroup 2 Action) :
    ∃ T : Subgroup Action, T.Normal ∧ CFSG.Open.IsElemAbelian 2 T ∧
      (∀ u : Action, u ∈ T ↔ u.val ∈ principalFourSubgroup (AddMonoid.End Abelian) ∧ u ^ 2 = 1) ∧
      pGeneratorRank 2 Action ≤ Nat.log 2 (Nat.card T) + 2 := by
  have hperiod : 2 ^ (upper - lower) * 2 ^ lower = 2 ^ upper := by
    rw [← pow_add, Nat.sub_add_cancel hunequal.le]
  let coordinates' : Abelian ≃+ CyclicPair (2 ^ (upper - lower)) (2 ^ lower) := by
    change Abelian ≃+ (ZMod (2 ^ (upper - lower) * 2 ^ lower) × ZMod (2 ^ lower))
    rw [hperiod]
    exact coordinates
  let R := AddMonoid.End Abelian
  let : Finite Abelian := Finite.of_equiv _ coordinates.symm.toEquiv
  let : Finite R := Finite.of_injective (fun f : R => (fun x : Abelian => f x)) (by
    intro f g h
    apply AddMonoid.End.ext
    exact congrFun h)
  let : Finite Action := Finite.of_injective (fun u : Action => u.val.val) (by
    intro u v h
    exact Subtype.ext (Units.ext h))
  have htwo : 2 ∣ 2 ^ lower := dvd_pow_self 2 (by omega : lower ≠ 0)
  have hfour : 4 ∣ 2 ^ lower := by
    change 2 ^ 2 ∣ 2 ^ lower
    exact Nat.pow_dvd_pow 2 (by omega)
  have hbinaryTwist : ((2 ^ (upper - lower) : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, show (2 : ZMod 2) = 0 from rfl,
      zero_pow (by omega : upper - lower ≠ 0)]
  let residue : R →+* RankTwoBinaryResidue 0 :=
    (binaryResidueTwistZeroHom _ hbinaryTwist).comp (abelianEndBinaryResidueHom _ _ htwo coordinates')
  have hresidue (r : R) : residue r = abelianEndBinaryResidueHom _ _ htwo coordinates' r := rfl
  have hkernel (r : R) : residue r = 0 ↔ ∃ s : R, r = 2 • s := by
    rw [hresidue]
    exact abelianEndBinaryResidueHom_zero _ _ htwo coordinates' r
  let e := addEndCoordinateTransport coordinates'
  have hcancel (n : ℕ) (hn : 0 < n) (hdivides : n * 2 ∣ 2 ^ lower)
      (r : R) (hr : n • r = 0) : residue r = 0 := by
    rw [hresidue]
    have hzero : n • e r = 0 := by rw [← map_nsmul, hr, map_zero]
    exact cyclicPairEndBinaryResidueHom_cancel _ _ htwo n hn hdivides (e r) hzero
  have hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0 :=
    hcancel 2 (by decide) (by
      change 2 ^ 2 ∣ 2 ^ lower
      exact Nat.pow_dvd_pow 2 (by omega))
  have hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0 :=
    hcancel 4 (by decide) (by
      change 2 ^ 3 ∣ 2 ^ lower
      exact Nat.pow_dvd_pow 2 hlarge)
  let fourResidue : R →+* ResidualRing ((2 ^ (upper - lower) : ℕ) : ZMod 4) :=
    (cyclicPairEndResidualHom _ _ hfour).comp e.toRingHom
  have hfactor (r : R) : residualBinaryCoordinates (fourResidue r) = residue r := by
    rw [hresidue]
    exact cyclicPair_residual_binary_factor _ _ hfour htwo (e r)
  have hfourKernel (u : Rˣ) : fourResidue u.val = 1 ↔ u ∈ principalFourSubgroup R := by
    rw [← addEndCoordinateTransport_principal_iff coordinates' u]
    let v := Units.map e.toMonoidHom u
    constructor
    · intro h
      exact (cyclicPairResidualUnits_kernel _ _ hfour v).mp (Units.ext h)
    · intro h
      exact congrArg Units.val ((cyclicPairResidualUnits_kernel _ _ hfour v).mpr h)
  have htwist : ((2 ^ (upper - lower) : ℕ) : ZMod 4) = 0 ∨
      ((2 ^ (upper - lower) : ℕ) : ZMod 4) = 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    obtain ⟨gap, hgap⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : upper - lower ≠ 0)
    rw [hgap, pow_succ]
    have h : ∀ x : ZMod 4, x * 2 = 0 ∨ x * 2 = 2 := by decide
    exact h _
  have hcharacteristic := rank_two_endomorphism_characteristic upper lower hunequal.le coordinates
  have hbound := unequal_fullAction_generator_rank_involution_bound residue hkernel hcancelTwo Action
    fourResidue hfactor hfourKernel hcancelFour hpgroup htwist hcharacteristic
  obtain ⟨T, hTnormal, hTelem, hTmem⟩ := principal_involution_subgroup_normal hcharacteristic Action
  refine ⟨T, hTnormal, hTelem, hTmem, ?_⟩
  let Deep := (Action ⊓ principalFourSubgroup R : Subgroup Rˣ)
  let Involutions := principalInvolutionSubgroup hcharacteristic Deep (fun u => u.property.2)
  have eqv : T ≃ Involutions := {
    toFun := fun u => ⟨⟨u.val.val, u.val.property, ((hTmem u.val).mp u.property).1⟩, by
      change (⟨u.val.val, u.val.property, ((hTmem u.val).mp u.property).1⟩ : Deep) ^ 2 = 1
      apply Subtype.ext
      exact congrArg (fun v : Action => v.val) ((hTmem u.val).mp u.property).2⟩
    invFun := fun u => ⟨⟨u.val.val, u.val.property.1⟩, (hTmem _).mpr
      ⟨u.val.property.2, by
        apply Subtype.ext
        exact congrArg (fun v : Deep => v.val) (show u.val ^ 2 = 1 from u.property)⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr eqv]
  exact hbound

theorem rank_two_unequal_full_action_minimum_generators
    {Abelian : Type*} [AddCommGroup Abelian] (upper lower : ℕ)
    (hunequal : lower < upper) (hlarge : 3 ≤ lower)
    (coordinates : Abelian ≃+ (ZMod (2 ^ upper) × ZMod (2 ^ lower)))
    (Action : Subgroup (AddMonoid.End Abelian)ˣ) (hpgroup : IsPGroup 2 Action) :
    ∃ finiteAction : Finite Action,
      let _ := finiteAction
      ∃ T : Subgroup Action, T.Normal ∧ CFSG.Open.IsElemAbelian 2 T ∧
        (∀ u : Action, u ∈ T ↔ u.val ∈ principalFourSubgroup (AddMonoid.End Abelian) ∧ u ^ 2 = 1) ∧
        Group.rank Action ≤ Nat.log 2 (Nat.card T) + 2 := by
  let : Finite Abelian := Finite.of_equiv _ coordinates.symm.toEquiv
  let : Finite (AddMonoid.End Abelian) := Finite.of_injective
    (fun f : AddMonoid.End Abelian => (fun x : Abelian => f x)) (by
      intro f g h
      apply AddMonoid.End.ext
      exact congrFun h)
  let finiteAction : Finite Action := Finite.of_injective (fun u : Action => u.val.val) (by
    intro u v h
    exact Subtype.ext (Units.ext h))
  let := finiteAction
  refine ⟨finiteAction, ?_⟩
  dsimp only
  obtain ⟨T, hTnormal, hTelem, hTmem, hbound⟩ :=
    rank_two_unequal_full_action_generator_bound upper lower hunequal hlarge coordinates Action hpgroup
  rw [pGeneratorRank_eq_group_rank Nat.prime_two hpgroup] at hbound
  exact ⟨T, hTnormal, hTelem, hTmem, hbound⟩

end CFSG.LargeEvenClassification.Helpers
