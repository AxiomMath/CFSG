module

public import CFSG.LocalAnalysis.LargeEvenClassification.HomocyclicOuterResidue
public import CFSG.LocalAnalysis.LargeEvenClassification.EvenActionGeneratorBound

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem principal_four_le_two (R : Type*) [Ring R] :
    principalFourSubgroup R ≤ principalCongruenceSubgroup R 2 := by
  intro u hu
  obtain ⟨r, hr⟩ := hu
  apply (principalCongruenceSubgroup_mem 2 u).mpr
  refine ⟨2 * r, ?_⟩
  rw [hr, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

section OuterLeading

variable {R F : Type*} [Ring R] [Ring F] [Module (ZMod 2) F]
variable (residue : R →+* F)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)
variable (hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0)

omit [Module (ZMod 2) F] in
include hkernel in
theorem residue_units_kernel (u : Rˣ) :
    Units.map residue.toMonoidHom u = 1 ↔ u ∈ principalCongruenceSubgroup R 2 := by
  rw [principalCongruenceSubgroup_mem]
  constructor
  · intro h
    have hval := congrArg Units.val h
    have hz : residue ((u : R) - 1) = 0 := by
      rw [map_sub, map_one]
      exact sub_eq_zero.mpr hval
    obtain ⟨r, hr⟩ := (hkernel _).mp hz
    exact ⟨r, (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)⟩
  · rintro ⟨r, hr⟩
    apply Units.ext
    exact residue_principal_two residue hkernel u ((principalCongruenceSubgroup_mem 2 u).mpr ⟨r, hr⟩)

theorem principal_outer_commutator_mem_two (u : Rˣ) (v : principalCongruenceSubgroup R 2) :
    u * v.val * u⁻¹ * v.val⁻¹ ∈ principalCongruenceSubgroup R 2 := by
  apply (principalCongruenceSubgroup R 2).mul_mem
  · exact Subgroup.Normal.conj_mem inferInstance v.val v.property u
  · exact (principalCongruenceSubgroup R 2).inv_mem v.property

include hkernel hcancelTwo in
theorem principal_outer_commutator_leading (u : Rˣ) (v : principalCongruenceSubgroup R 2) :
    principalLeadingResidue residue 2
      ⟨u * v.val * u⁻¹ * v.val⁻¹, principal_outer_commutator_mem_two u v⟩ =
        binaryResidueConjugationDifference (Units.map residue.toMonoidHom u)
          (principalLeadingResidue residue 2 v) := by
  let r := principalLeadingRepresentative 2 v
  have hidentity : (u : R) * v.val * (u⁻¹ : Rˣ).val * (v.val⁻¹ : Rˣ).val =
      1 + ((u : R) * v.val * (u⁻¹ : Rˣ).val - (v.val : R)) * (v.val⁻¹ : Rˣ).val := by
    rw [sub_mul, Units.mul_inv]
    abel
  have hr : ((u * v.val * u⁻¹ * v.val⁻¹ : Rˣ) : R) =
      1 + 2 • (((u : R) * r * (u⁻¹ : Rˣ).val - r) * (v.val⁻¹ : Rˣ).val) := by
    change (u : R) * v.val * (u⁻¹ : Rˣ).val * (v.val⁻¹ : Rˣ).val = _
    rw [hidentity, principalLeadingRepresentative_spec]
    change 1 + ((u : R) * (1 + 2 • r) * (u⁻¹ : Rˣ).val - (1 + 2 • r)) * _ = _
    have hunit := Units.mul_inv u
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    calc
      _ = 1 + ((u : R) * (u⁻¹ : Rˣ).val - 1) * (v.val⁻¹ : Rˣ).val +
          2 * (((u : R) * r * (u⁻¹ : Rˣ).val - r) * (v.val⁻¹ : Rˣ).val) := by noncomm_ring
      _ = _ := by rw [hunit]; simp
  rw [principalLeadingResidue_spec residue 2 hcancelTwo _ _ hr]
  rw [map_mul, map_sub, map_mul, map_mul,
    residue_principal_two residue hkernel v.val⁻¹ ((principalCongruenceSubgroup R 2).inv_mem v.property), mul_one]
  rfl

end OuterLeading

section FullAction

variable {R F : Type*} [Ring R] [Ring F] [Module (ZMod 2) F]
variable (residue : R →+* F)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)
variable (hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0)
variable (Action : Subgroup Rˣ)

@[expose] def fullActionEven : Subgroup Action :=
  (principalCongruenceSubgroup R 2).comap Action.subtype

instance fullActionEven_normal : (fullActionEven Action).Normal :=
  Subgroup.Normal.comap inferInstance Action.subtype

@[expose] def fullActionEvenImage : Subgroup Rˣ := Action ⊓ principalCongruenceSubgroup R 2

@[expose] def fullActionEvenEquiv : fullActionEven Action ≃* fullActionEvenImage Action where
  toFun u := ⟨u.val.val, u.val.property, u.property⟩
  invFun u := ⟨⟨u.val, u.property.1⟩, u.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def fullActionEvenLeadingHom : fullActionEven Action →* Multiplicative F :=
  (evenActionLeadingHom residue hkernel hcancelTwo (fullActionEvenImage Action) inf_le_right).comp
    (fullActionEvenEquiv Action).toMonoidHom

@[expose] def fullActionKilledEven : Subgroup (fullActionEven Action) :=
  (frattini Action).comap (fullActionEven Action).subtype

@[expose] noncomputable def fullActionKilledEvenResidueHom : fullActionKilledEven Action →* Multiplicative F :=
  (fullActionEvenLeadingHom residue hkernel hcancelTwo Action).comp (fullActionKilledEven Action).subtype

include hkernel hcancelTwo in
theorem fullAction_outer_difference_mem_killed [Finite Action] (hpgroup : IsPGroup 2 Action)
    (u : Action) (v : fullActionEven Action) :
    binaryResidueConjugationDifference (Units.map residue.toMonoidHom u.val)
      ((fullActionEvenLeadingHom residue hkernel hcancelTwo Action v).toAdd) ∈
        binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action) := by
  let g : principalCongruenceSubgroup R 2 := ⟨v.val.val, v.property⟩
  have heven : u * v.val * u⁻¹ * v.val⁻¹ ∈ fullActionEven Action :=
    principal_outer_commutator_mem_two u.val g
  let witness : fullActionKilledEven Action :=
    ⟨⟨u * v.val * u⁻¹ * v.val⁻¹, heven⟩,
      pGroup_commutator_mem_frattini Nat.prime_two hpgroup u v.val⟩
  apply (binaryHomRange_mem _ _).mpr
  refine ⟨witness, ?_⟩
  apply Multiplicative.toAdd.injective
  exact principal_outer_commutator_leading residue hkernel hcancelTwo u.val g

include hkernel hcancelTwo in
theorem fullAction_outer_difference_le_killed [Finite Action] (hpgroup : IsPGroup 2 Action) (u : Action) :
    (binaryHomRange (fullActionEvenLeadingHom residue hkernel hcancelTwo Action)).map
        (binaryResidueConjugationDifference (Units.map residue.toMonoidHom u.val)) ≤
      binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  obtain ⟨v, hv⟩ := (binaryHomRange_mem _ _).mp hx
  have h := fullAction_outer_difference_mem_killed residue hkernel hcancelTwo Action hpgroup u v
  rw [hv] at h
  exact h

theorem fullActionEvenLeadingHom_range :
    binaryHomRange (fullActionEvenLeadingHom residue hkernel hcancelTwo Action) =
      binaryHomRange (evenActionLeadingHom residue hkernel hcancelTwo (fullActionEvenImage Action) inf_le_right) := by
  ext x
  rw [binaryHomRange_mem, binaryHomRange_mem]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨fullActionEvenEquiv Action u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨(fullActionEvenEquiv Action).symm u, by
      change evenActionLeadingHom residue hkernel hcancelTwo (fullActionEvenImage Action) inf_le_right
        (fullActionEvenEquiv Action ((fullActionEvenEquiv Action).symm u)) = _
      rw [MulEquiv.apply_symm_apply]
      exact hu⟩

@[expose] def fullActionDeepEquiv :
    evenActionDeep (fullActionEvenImage Action) ≃* evenActionDeep Action where
  toFun u := ⟨⟨u.val.val, u.val.property.1⟩, u.property⟩
  invFun u := ⟨⟨u.val.val, u.val.property, principal_four_le_two R u.property⟩, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0)

include hkernel hcancelTwo hcancelFour in
theorem fullAction_generator_rank_double_saving [Finite Action] [Finite F]
    (hpgroup : IsPGroup 2 Action) (D : Submodule (ZMod 2) F)
    (hD : D ≤ binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action)) :
    let W := binaryHomRange (fullActionEvenLeadingHom residue hkernel hcancelTwo Action)
    pGeneratorRank 2 Action + Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) +
        Module.finrank (ZMod 2) D ≤
      pGeneratorRank 2 (Action ⧸ fullActionEven Action) + Module.finrank (ZMod 2) W +
        pGeneratorRank 2 (evenActionDeep Action) := by
  dsimp only
  let EvenImage := fullActionEvenImage Action
  let evenEquiv := fullActionEvenEquiv Action
  let deepEquiv := fullActionDeepEquiv Action
  let : Finite EvenImage := Finite.of_equiv (fullActionEven Action) evenEquiv.toEquiv
  let : Finite (evenActionDeep EvenImage) := inferInstance
  have hpEven := hpgroup.to_subgroup (fullActionEven Action)
  have hpEvenImage := hpEven.of_equiv evenEquiv
  have hpDeep := hpEvenImage.to_subgroup (evenActionDeep EvenImage)
  have houter := binary_leading_image_frattini_saving hpgroup (fullActionEven Action)
    (fullActionEvenLeadingHom residue hkernel hcancelTwo Action) D hD
  have hinner := evenAction_generator_rank_saving residue hkernel hcancelTwo hcancelFour EvenImage inf_le_right
    hpEvenImage
  have hrankEven : pGeneratorRank 2 (fullActionEven Action) = pGeneratorRank 2 EvenImage := by
    rw [pGeneratorRank_eq_group_rank Nat.prime_two hpEven,
      pGeneratorRank_eq_group_rank Nat.prime_two hpEvenImage]
    exact Group.rank_congr evenEquiv
  have hrankDeep : pGeneratorRank 2 (evenActionDeep EvenImage) = pGeneratorRank 2 (evenActionDeep Action) := by
    rw [pGeneratorRank_eq_group_rank Nat.prime_two hpDeep,
      pGeneratorRank_eq_group_rank Nat.prime_two (hpgroup.to_subgroup (evenActionDeep Action))]
    exact Group.rank_congr deepEquiv
  rw [hrankEven] at houter
  rw [hrankDeep] at hinner
  have hrange := fullActionEvenLeadingHom_range residue hkernel hcancelTwo Action
  rw [hrange]
  dsimp only [EvenImage, evenEquiv, deepEquiv] at houter hinner
  omega

end FullAction

theorem homocyclic_residue_two_image_card {G : Type*} [Group G] [Finite G]
    (hpgroup : IsPGroup 2 G) (f : G →* (RankTwoBinaryResidue 1)ˣ) :
    Nat.card f.range ≤ 2 ∧ ∀ u : G, (f u) ^ 2 = 1 := by
  have hpimage := hpgroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨rank, hrank⟩ := hpimage.exists_card_eq
  have hdivides : 2 ^ rank ∣ 6 := by
    rw [← hrank, ← rankTwoBinaryResidue_units_card.1]
    exact f.range.card_subgroup_dvd_card
  have hsmall : rank ≤ 1 := by
    by_contra h
    have hd : 2 ^ 2 ∣ 2 ^ rank := Nat.pow_dvd_pow 2 (by omega)
    have hbad := hd.trans hdivides
    norm_num at hbad
  have hcard : Nat.card f.range ≤ 2 := by
    rw [hrank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
  refine ⟨hcard, ?_⟩
  intro u
  by_cases hone : Nat.card f.range = 1
  · have hbot : f.range = ⊥ := Subgroup.card_eq_one.mp hone
    have hu : f u ∈ (⊥ : Subgroup (RankTwoBinaryResidue 1)ˣ) := hbot ▸ (show f u ∈ f.range from ⟨u, rfl⟩)
    rw [show f u = 1 from hu, one_pow]
  · have htwo : Nat.card f.range = 2 := by have hpos := Nat.card_pos (α := f.range); omega
    have hpower : (f.rangeRestrict u) ^ 2 = 1 := by
      simpa only [htwo] using (pow_card_eq_one' (x := f.rangeRestrict u))
    exact congrArg Subtype.val hpower

theorem deepAction_generator_rank_involution_bound {R : Type*} [Ring R]
    (Action : Subgroup Rˣ) [Finite Action] (hpgroup : IsPGroup 2 Action)
    {exponent : ℕ} (hcharacteristic : (2 : R) ^ exponent = 0) :
    pGeneratorRank 2 (evenActionDeep Action) ≤
      Nat.log 2 (Nat.card (principalInvolutionSubgroup hcharacteristic
        (Action ⊓ principalFourSubgroup R) (fun u => u.property.2))) := by
  let Deep := (Action ⊓ principalFourSubgroup R : Subgroup Rˣ)
  let e : evenActionDeep Action ≃* Deep := {
    toFun := fun u => ⟨u.val.val, u.val.property, u.property⟩
    invFun := fun u => ⟨⟨u.val, u.property.1⟩, u.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let : Finite Deep := Finite.of_equiv (evenActionDeep Action) e.toEquiv
  have hdeep := hpgroup.to_subgroup (evenActionDeep Action)
  rw [pGeneratorRank_mulEquiv Nat.prime_two hdeep e]
  exact principal_pGeneratorRank_le_involutions hcharacteristic Deep (hdeep.of_equiv e)
    (fun u => u.property.2)

section HomocyclicFull

variable {R : Type*} [Ring R]
variable (residue : R →+* RankTwoBinaryResidue 1)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)
variable (hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0)
variable (hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0)
variable (Action : Subgroup Rˣ) [Finite Action]

include residue hkernel hcancelTwo hcancelFour in
theorem homocyclic_fullAction_generator_rank_bound (hpgroup : IsPGroup 2 Action) :
    pGeneratorRank 2 Action ≤ pGeneratorRank 2 (evenActionDeep Action) + 2 := by
  let outer : Action →* (RankTwoBinaryResidue 1)ˣ := (Units.map residue.toMonoidHom).comp Action.subtype
  have hker : outer.ker = fullActionEven Action := by
    ext u
    exact residue_units_kernel residue hkernel u.val
  let e : Action ⧸ fullActionEven Action ≃* outer.range :=
    QuotientGroup.liftEquiv _ outer.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict, hker])
  have hsmall := homocyclic_residue_two_image_card hpgroup outer
  have hquotcard : Nat.card (Action ⧸ fullActionEven Action) ≤ 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact hsmall.1
  have hquotrank : pGeneratorRank 2 (Action ⧸ fullActionEven Action) ≤ 1 := by
    have hc := Nat.card_le_card_of_surjective
      (QuotientGroup.mk' (frattini (Action ⧸ fullActionEven Action)))
      (QuotientGroup.mk'_surjective (frattini (Action ⧸ fullActionEven Action)))
    have hlog := Nat.log_mono_right (b := 2) (hc.trans hquotcard)
    change pGeneratorRank 2 (Action ⧸ fullActionEven Action) ≤ Nat.log 2 2 at hlog
    norm_num at hlog
    exact hlog
  by_cases htrivial : ∀ u : Action, outer u = 1
  · have heven : Action ≤ principalCongruenceSubgroup R 2 := by
      intro u hu
      exact (residue_units_kernel residue hkernel u).mp (htrivial ⟨u, hu⟩)
    exact evenAction_generator_rank_bound residue hkernel hcancelTwo hcancelFour Action heven hpgroup
      (rankTwoBinaryResidue_square_commutator_bound 1)
  · push Not at htrivial
    obtain ⟨u, hu⟩ := htrivial
    let W := binaryHomRange (fullActionEvenLeadingHom residue hkernel hcancelTwo Action)
    let D := W.map (binaryResidueConjugationDifference (outer u))
    have hD : D ≤ binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action) :=
      fullAction_outer_difference_le_killed residue hkernel hcancelTwo Action hpgroup u
    have hsaving := fullAction_generator_rank_double_saving residue hkernel hcancelTwo Action hcancelFour hpgroup D hD
    have hbound := homocyclic_residue_outer_saving (outer u) hu (hsmall.2 u) W
    change pGeneratorRank 2 Action + Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) +
        Module.finrank (ZMod 2) D ≤ pGeneratorRank 2 (Action ⧸ fullActionEven Action) +
        Module.finrank (ZMod 2) W + pGeneratorRank 2 (evenActionDeep Action) at hsaving
    change Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) +
      Module.finrank (ZMod 2) D + 1 at hbound
    omega

include residue hkernel hcancelTwo hcancelFour in
theorem homocyclic_fullAction_generator_rank_involution_bound (hpgroup : IsPGroup 2 Action)
    {exponent : ℕ} (hcharacteristic : (2 : R) ^ exponent = 0) :
    pGeneratorRank 2 Action ≤
      Nat.log 2 (Nat.card (principalInvolutionSubgroup hcharacteristic
        (Action ⊓ principalFourSubgroup R) (fun u => u.property.2))) + 2 :=
  (homocyclic_fullAction_generator_rank_bound residue hkernel hcancelTwo hcancelFour Action hpgroup).trans
    (Nat.add_le_add_right (deepAction_generator_rank_involution_bound Action hpgroup hcharacteristic) 2)

end HomocyclicFull

section HomocyclicCanonical

variable {Abelian : Type*} [AddCommGroup Abelian]

theorem rank_two_homocyclic_full_action_generator_bound (exponent : ℕ) (hlarge : 3 ≤ exponent)
    (coordinates : Abelian ≃+ (ZMod (2 ^ exponent) × ZMod (2 ^ exponent)))
    (Action : Subgroup (AddMonoid.End Abelian)ˣ) (hpgroup : IsPGroup 2 Action) :
    ∃ T : Subgroup Action, T.Normal ∧ CFSG.Open.IsElemAbelian 2 T ∧
      (∀ u : Action, u ∈ T ↔ u.val ∈ principalFourSubgroup (AddMonoid.End Abelian) ∧ u ^ 2 = 1) ∧
      pGeneratorRank 2 Action ≤ Nat.log 2 (Nat.card T) + 2 := by
  let coordinates' : Abelian ≃+ CyclicPair 1 (2 ^ exponent) := by
    change Abelian ≃+ (ZMod (1 * 2 ^ exponent) × ZMod (2 ^ exponent))
    rw [one_mul]
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
  have htwo : 2 ∣ 2 ^ exponent := dvd_pow_self 2 (by omega : exponent ≠ 0)
  let residue : R →+* RankTwoBinaryResidue 1 := abelianEndBinaryResidueHom 1 _ htwo coordinates'
  have hkernel (r : R) : residue r = 0 ↔ ∃ s : R, r = 2 • s :=
    abelianEndBinaryResidueHom_zero _ _ htwo coordinates' r
  have hcancel (n : ℕ) (hn : 0 < n) (hdivides : n * 2 ∣ 2 ^ exponent)
      (r : R) (hr : n • r = 0) : residue r = 0 := by
    let e := addEndCoordinateTransport coordinates'
    have hzero : n • e r = 0 := by rw [← map_nsmul, hr, map_zero]
    exact cyclicPairEndBinaryResidueHom_cancel _ _ htwo n hn hdivides (e r) hzero
  have hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0 :=
    hcancel 2 (by decide) (by
      change 2 ^ 2 ∣ 2 ^ exponent
      exact Nat.pow_dvd_pow 2 (by omega))
  have hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0 :=
    hcancel 4 (by decide) (by
      change 2 ^ 3 ∣ 2 ^ exponent
      exact Nat.pow_dvd_pow 2 hlarge)
  have hcharacteristic := rank_two_endomorphism_characteristic exponent exponent le_rfl coordinates
  have hbound := homocyclic_fullAction_generator_rank_involution_bound residue hkernel hcancelTwo hcancelFour
    Action hpgroup hcharacteristic
  obtain ⟨T, hTnormal, hTelem, hTmem⟩ := principal_involution_subgroup_normal hcharacteristic Action
  refine ⟨T, hTnormal, hTelem, hTmem, ?_⟩
  let Deep := (Action ⊓ principalFourSubgroup R : Subgroup Rˣ)
  let Involutions := principalInvolutionSubgroup hcharacteristic Deep (fun u => u.property.2)
  have e : T ≃ Involutions := {
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
  rw [Nat.card_congr e]
  exact hbound

theorem rank_two_homocyclic_full_action_minimum_generators (exponent : ℕ) (hlarge : 3 ≤ exponent)
    (coordinates : Abelian ≃+ (ZMod (2 ^ exponent) × ZMod (2 ^ exponent)))
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
    rank_two_homocyclic_full_action_generator_bound exponent hlarge coordinates Action hpgroup
  rw [pGeneratorRank_eq_group_rank Nat.prime_two hpgroup] at hbound
  exact ⟨T, hTnormal, hTelem, hTmem, hbound⟩

end HomocyclicCanonical

end CFSG.LargeEvenClassification.Helpers
