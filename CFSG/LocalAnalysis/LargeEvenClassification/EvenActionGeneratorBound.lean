module

public import CFSG.LocalAnalysis.LargeEvenClassification.CongruenceLeadingResidue
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsFrattini

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def binaryHomRange {G F : Type*} [Group G] [AddCommGroup F]
    [Module (ZMod 2) F] (f : G →* Multiplicative F) : Submodule (ZMod 2) F :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' f.range)

theorem binaryHomRange_mem {G F : Type*} [Group G] [AddCommGroup F]
    [Module (ZMod 2) F] (f : G →* Multiplicative F) (z : F) :
    z ∈ binaryHomRange f ↔ ∃ g : G, f g = Multiplicative.ofAdd z := Iff.rfl

theorem binary_characteristic_additive_isPGroup {R : Type*} [Ring R] {exponent : ℕ}
    (hcharacteristic : (2 : R) ^ exponent = 0) : IsPGroup 2 (Multiplicative R) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro r
  refine ⟨exponent, ?_⟩
  change (2 ^ exponent : ℕ) • r.toAdd = 0
  rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, hcharacteristic, zero_mul]

theorem principal_two_isPGroup {R : Type*} [Ring R] [Finite R] {exponent : ℕ}
    (hcharacteristic : (2 : R) ^ exponent = 0) : IsPGroup 2 (principalCongruenceSubgroup R 2) := by
  let Double := (ringMultipleIdeal R 2).toAddSubgroup.toSubgroup
  have hpgroup := (binary_characteristic_additive_isPGroup hcharacteristic).to_subgroup Double
  obtain ⟨rank, hrank⟩ := hpgroup.exists_card_eq
  let forward : principalCongruenceSubgroup R 2 → ringMultipleIdeal R 2 :=
    fun u => ⟨(u.val : R) - 1, by
      obtain ⟨r, hr⟩ := (principalCongruenceSubgroup_mem 2 u.val).mp u.property
      exact ⟨r, by rw [hr]; simp⟩⟩
  have hinjective : Function.Injective forward := by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    exact sub_left_injective (congrArg Subtype.val h)
  have hsurjective : Function.Surjective forward := by
    intro r
    obtain ⟨s, hs⟩ := r.property
    have hisUnit : IsUnit (1 + r.val) := by
      rw [hs, nsmul_eq_mul, Nat.cast_ofNat]
      exact binary_one_add_double_isUnit hcharacteristic s
    refine ⟨⟨hisUnit.unit, (principalCongruenceSubgroup_mem 2 _).mpr ⟨s, ?_⟩⟩, ?_⟩
    · rw [hisUnit.unit_spec, hs]
    · apply Subtype.ext
      change (hisUnit.unit : R) - 1 = r.val
      rw [hisUnit.unit_spec]
      simp
  apply IsPGroup.of_card (n := rank)
  rw [Nat.card_congr (Equiv.ofBijective forward ⟨hinjective, hsurjective⟩)]
  have hcard : Nat.card (ringMultipleIdeal R 2) = Nat.card Double := by
    exact Nat.card_congr {
      toFun := fun r => ⟨Multiplicative.ofAdd r.val, r.property⟩
      invFun := fun r => ⟨r.val.toAdd, r.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hcard]
  exact hrank

theorem binaryHom_frattini_le_ker {G F : Type*} [Group G] [AddCommGroup F]
    [Module (ZMod 2) F] (f : G →* Multiplicative F) : frattini G ≤ f.ker := by
  let Image := f.range
  let : Module (ZMod 2) (Additive Image) := elementaryZModModule (fun z => by
    apply Subtype.ext
    change Multiplicative.ofAdd (2 • z.val.toAdd) = 1
    rw [two_nsmul, ZModModule.add_self]
    rfl)
  have h := elementary_quotient_kills_frattini Nat.prime_two f.rangeRestrict f.rangeRestrict_surjective
  intro g hg
  exact congrArg Subtype.val (h hg)

theorem binaryHom_quotient_generator_rank {G F : Type*} [Group G] [Finite G]
    [AddCommGroup F] [Module (ZMod 2) F] (hpgroup : IsPGroup 2 G)
    (Normal : Subgroup G) [Normal.Normal] (f : G →* Multiplicative F) (hker : f.ker = Normal) :
    pGeneratorRank 2 (G ⧸ Normal) = Module.finrank (ZMod 2) (binaryHomRange f) := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : Finite (binaryHomRange f) := by
    let rangeEquiv : f.range ≃ binaryHomRange f := {
      toFun := fun z => ⟨z.val.toAdd, z.property⟩
      invFun := fun z => ⟨Multiplicative.ofAdd z.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact Finite.of_equiv f.range rangeEquiv
  let e : G ⧸ Normal ≃* f.range := QuotientGroup.liftEquiv Normal f.rangeRestrict_surjective (by
    rw [MonoidHom.ker_rangeRestrict, hker])
  have hquotient := hpgroup.to_quotient Normal
  rw [pGeneratorRank_eq_group_rank Nat.prime_two hquotient, Group.rank_congr e,
    ← pGeneratorRank_eq_group_rank Nat.prime_two
      (hquotient.of_injective e.symm.toMonoidHom e.symm.injective)]
  have hexponent (z : f.range) : z ^ 2 = 1 := by
    apply Subtype.ext
    change Multiplicative.ofAdd (2 • z.val.toAdd) = 1
    rw [two_nsmul, ZModModule.add_self]
    rfl
  rw [elementary_pGeneratorRank_eq_log_card Nat.prime_two hexponent]
  have hcard : Nat.card f.range = Nat.card (binaryHomRange f) := by
    apply Nat.card_congr
    exact { toFun := fun z => ⟨z.val.toAdd, z.property⟩
            invFun := fun z => ⟨Multiplicative.ofAdd z.val, z.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [hcard, ← FiniteField.pow_finrank_eq_natCard 2 (binaryHomRange f), Nat.log_pow (by decide : 1 < 2)]

theorem binary_leading_image_frattini_saving {G F : Type*} [Group G] [Finite G]
    [AddCommGroup F] [Finite F] [Module (ZMod 2) F] (hpgroup : IsPGroup 2 G)
    (Normal : Subgroup G) [Normal.Normal] (leading : Normal →* Multiplicative F)
    (C : Submodule (ZMod 2) F)
    (hC : C ≤ binaryHomRange (leading.comp ((frattini G).comap Normal.subtype).subtype)) :
    pGeneratorRank 2 G + Module.finrank (ZMod 2) C ≤
      pGeneratorRank 2 (G ⧸ Normal) + pGeneratorRank 2 Normal := by
  let Killed := (frattini G).comap Normal.subtype
  let basis := Module.finBasis (ZMod 2) C
  have hlift (i : Fin (Module.finrank (ZMod 2) C)) :
      ∃ g : Killed, leading g.val = Multiplicative.ofAdd (basis i).val :=
    (binaryHomRange_mem _ _).mp (hC (basis i).property)
  let family : Fin (Module.finrank (ZMod 2) C) → Normal :=
    fun i => (Classical.choose (hlift i)).val
  have hfamily (i : Fin (Module.finrank (ZMod 2) C)) :
      leading (family i) = Multiplicative.ofAdd (basis i).val := Classical.choose_spec (hlift i)
  have hkilled (i : Fin (Module.finrank (ZMod 2) C)) : (family i : G) ∈ frattini G :=
    (Classical.choose (hlift i)).property
  let : CommGroup (Normal ⧸ frattini Normal) :=
    pGroupFrattiniCommGroup Nat.prime_two (hpgroup.to_subgroup Normal)
  let module : Module (ZMod 2) (Additive (Normal ⧸ frattini Normal)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two (hpgroup.to_subgroup Normal))
  let := module
  let quotient := QuotientGroup.lift (frattini Normal) leading (binaryHom_frattini_le_ker leading)
  let linear := quotient.toAdditiveLeft.toZModLinearMap 2
  have himages : (fun i => linear (Additive.ofMul
      ((QuotientGroup.mk' (frattini Normal)) (family i)))) = fun i => (basis i).val := by
    funext i
    change (quotient ((QuotientGroup.mk' (frattini Normal)) (family i))).toAdd = (basis i).val
    change (leading (family i)).toAdd = (basis i).val
    rw [hfamily]
    rfl
  have hindependent : LinearIndependent (ZMod 2) (fun i => Additive.ofMul
      ((QuotientGroup.mk' (frattini Normal)) (family i))) := by
    apply LinearIndependent.of_comp linear
    rw [Function.comp_def, himages]
    exact basis.linearIndependent.map' C.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hsaving := pGeneratorRank_normal_independent_saving Nat.prime_two hpgroup
    Normal family hkilled module hindependent
  simpa only [Fintype.card_fin] using hsaving

section EvenAction

variable {R F : Type*} [Ring R] [Ring F] [Module (ZMod 2) F]
variable (residue : R →+* F)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)
variable (hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0)
variable (hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0)
variable (Action : Subgroup Rˣ)
variable (heven : Action ≤ principalCongruenceSubgroup R 2)

@[expose] def evenActionInclusion : Action →* principalCongruenceSubgroup R 2 :=
  Action.inclusion heven

@[expose] noncomputable def evenActionLeadingHom : Action →* Multiplicative F :=
  (principalLeadingResidueHom residue hkernel 2 (by decide) hcancelTwo).comp
    (evenActionInclusion Action heven)

@[expose] def evenActionDeep : Subgroup Action :=
  (principalFourSubgroup R).comap Action.subtype

instance evenActionDeep_normal : (evenActionDeep Action).Normal := by
  let : (principalFourSubgroup R).Normal := principal_four_normal R
  exact Subgroup.Normal.comap inferInstance Action.subtype

omit [Module (ZMod 2) F] in
theorem evenActionLeadingHom_ker :
    (evenActionLeadingHom residue hkernel hcancelTwo Action heven).ker = evenActionDeep Action := by
  ext u
  change principalLeadingResidueHom residue hkernel 2 (by decide) hcancelTwo
    (evenActionInclusion Action heven u) = 1 ↔ (u.val ∈ principalFourSubgroup R)
  rw [principalLeadingResidueHom_kernel, show (2 : ℕ) * 2 = 4 from rfl,
    principalCongruenceSubgroup_four]
  rfl

@[expose] def evenActionDeepInclusion : evenActionDeep Action →* principalCongruenceSubgroup R 4 where
  toFun u := ⟨u.val.val, (principalCongruenceSubgroup_four R).symm ▸ u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def evenActionDeepLeadingHom : evenActionDeep Action →* Multiplicative F :=
  (principalLeadingResidueHom residue hkernel 4 (by decide) hcancelFour).comp
    (evenActionDeepInclusion Action)

@[expose] def evenActionKilledDeep : Subgroup (evenActionDeep Action) :=
  (frattini Action).comap (evenActionDeep Action).subtype

@[expose] noncomputable def evenActionKilledResidueHom : evenActionKilledDeep Action →* Multiplicative F :=
  (evenActionDeepLeadingHom residue hkernel hcancelFour Action).comp
    (evenActionKilledDeep Action).subtype

include heven in
theorem evenAction_square_residue_mem_killed [Finite Action] (hpgroup : IsPGroup 2 Action) (u : Action) :
    let x := (evenActionLeadingHom residue hkernel hcancelTwo Action heven u).toAdd
    x + x * x ∈ binaryHomRange (evenActionKilledResidueHom residue hkernel hcancelFour Action) := by
  dsimp only
  let g : principalCongruenceSubgroup R 2 := evenActionInclusion Action heven u
  have hdeep : u ^ 2 ∈ evenActionDeep Action := by
    change u.val ^ 2 ∈ principalFourSubgroup R
    rw [← principalCongruenceSubgroup_four]
    exact principal_two_square_mem_four g.val g.property
  let witness : evenActionKilledDeep Action :=
    ⟨⟨u ^ 2, hdeep⟩, pGroup_pow_mem_frattini Nat.prime_two hpgroup u⟩
  apply (binaryHomRange_mem _ _).mpr
  refine ⟨witness, ?_⟩
  apply Multiplicative.toAdd.injective
  exact principal_two_square_leading residue hcancelFour g

include heven in
theorem evenAction_commutator_residue_mem_killed [Finite Action] (hpgroup : IsPGroup 2 Action)
    (u v : Action) :
    let x := (evenActionLeadingHom residue hkernel hcancelTwo Action heven u).toAdd
    let y := (evenActionLeadingHom residue hkernel hcancelTwo Action heven v).toAdd
    x * y - y * x ∈ binaryHomRange (evenActionKilledResidueHom residue hkernel hcancelFour Action) := by
  dsimp only
  let g : principalCongruenceSubgroup R 2 := evenActionInclusion Action heven u
  let h : principalCongruenceSubgroup R 2 := evenActionInclusion Action heven v
  have hdeep : u * v * u⁻¹ * v⁻¹ ∈ evenActionDeep Action := by
    change u.val * v.val * u.val⁻¹ * v.val⁻¹ ∈ principalFourSubgroup R
    rw [← principalCongruenceSubgroup_four]
    exact principal_two_commutator_mem_four g.val h.val g.property h.property
  let witness : evenActionKilledDeep Action :=
    ⟨⟨u * v * u⁻¹ * v⁻¹, hdeep⟩, pGroup_commutator_mem_frattini Nat.prime_two hpgroup u v⟩
  apply (binaryHomRange_mem _ _).mpr
  refine ⟨witness, ?_⟩
  apply Multiplicative.toAdd.injective
  exact principal_two_commutator_leading residue hkernel hcancelFour g h

include heven in
theorem evenAction_residue_span_le_killed [Finite Action] (hpgroup : IsPGroup 2 Action) :
    residueSquareCommutatorSpan (binaryHomRange (evenActionLeadingHom residue hkernel hcancelTwo Action heven)) ≤
      binaryHomRange (evenActionKilledResidueHom residue hkernel hcancelFour Action) := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, rfl⟩
  · obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp hx
    have h := evenAction_square_residue_mem_killed residue hkernel hcancelTwo hcancelFour Action heven hpgroup u
    rw [hu] at h
    exact h
  · obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp hx
    obtain ⟨v, hv⟩ := (binaryHomRange_mem _ _).mp hy
    have h := evenAction_commutator_residue_mem_killed residue hkernel hcancelTwo hcancelFour Action heven
      hpgroup u v
    rw [hu, hv] at h
    exact h

include heven hcancelFour in
theorem evenAction_generator_rank_saving [Finite Action] [Finite F] (hpgroup : IsPGroup 2 Action) :
    let W := binaryHomRange (evenActionLeadingHom residue hkernel hcancelTwo Action heven)
    pGeneratorRank 2 Action + Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) ≤
      Module.finrank (ZMod 2) W + pGeneratorRank 2 (evenActionDeep Action) := by
  dsimp only
  have hsaving := binary_leading_image_frattini_saving hpgroup (evenActionDeep Action)
    (evenActionDeepLeadingHom residue hkernel hcancelFour Action)
    (residueSquareCommutatorSpan (binaryHomRange
      (evenActionLeadingHom residue hkernel hcancelTwo Action heven)))
    (evenAction_residue_span_le_killed residue hkernel hcancelTwo hcancelFour Action heven hpgroup)
  rw [binaryHom_quotient_generator_rank hpgroup (evenActionDeep Action)
    (evenActionLeadingHom residue hkernel hcancelTwo Action heven)
    (evenActionLeadingHom_ker residue hkernel hcancelTwo Action heven)] at hsaving
  exact hsaving

include residue hkernel hcancelTwo hcancelFour heven in
theorem evenAction_generator_rank_bound [Finite Action] [Finite F] (hpgroup : IsPGroup 2 Action)
    (hresidue : ∀ W : Submodule (ZMod 2) F,
      Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) + 2) :
    pGeneratorRank 2 Action ≤ pGeneratorRank 2 (evenActionDeep Action) + 2 := by
  have hsaving := evenAction_generator_rank_saving residue hkernel hcancelTwo hcancelFour Action heven hpgroup
  have hbound := hresidue (binaryHomRange (evenActionLeadingHom residue hkernel hcancelTwo Action heven))
  omega

include residue hkernel hcancelTwo hcancelFour heven in
theorem evenAction_generator_rank_involution_bound [Finite Action] [Finite F]
    (hpgroup : IsPGroup 2 Action) {exponent : ℕ} (hcharacteristic : (2 : R) ^ exponent = 0)
    (hresidue : ∀ W : Submodule (ZMod 2) F,
      Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) + 2) :
    pGeneratorRank 2 Action ≤
      Nat.log 2 (Nat.card (principalInvolutionSubgroup hcharacteristic
        ((Action ⊓ principalFourSubgroup R) : Subgroup Rˣ)
        (fun u => u.property.2))) + 2 := by
  let Deep := (Action ⊓ principalFourSubgroup R : Subgroup Rˣ)
  let e : evenActionDeep Action ≃* Deep := {
    toFun := fun u => ⟨u.val.val, u.val.property, u.property⟩
    invFun := fun u => ⟨⟨u.val, u.property.1⟩, u.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let : Finite Deep := Finite.of_equiv (evenActionDeep Action) e.toEquiv
  have hdeep := hpgroup.to_subgroup (evenActionDeep Action)
  have hDeep := hdeep.of_injective e.symm.toMonoidHom e.symm.injective
  have hprincipal := principal_pGeneratorRank_le_involutions hcharacteristic Deep hDeep
    (fun u => u.property.2)
  have hrank : pGeneratorRank 2 (evenActionDeep Action) = pGeneratorRank 2 Deep := by
    rw [pGeneratorRank_eq_group_rank Nat.prime_two hdeep,
      pGeneratorRank_eq_group_rank Nat.prime_two hDeep]
    exact Group.rank_congr e
  have hbound := evenAction_generator_rank_bound residue hkernel hcancelTwo hcancelFour Action heven
    hpgroup hresidue
  rw [hrank] at hbound
  exact hbound.trans (Nat.add_le_add_right hprincipal 2)

end EvenAction

section CanonicalRankTwo

variable {Abelian : Type*} [AddCommGroup Abelian]
variable (upper lower : ℕ) (hle : lower ≤ upper) (hlower : 3 ≤ lower)
variable (coordinates : Abelian ≃+ (ZMod (2 ^ upper) × ZMod (2 ^ lower)))

include hle coordinates in
theorem rank_two_endomorphism_characteristic : (2 : AddMonoid.End Abelian) ^ upper = 0 := by
  rw [← Nat.cast_ofNat, ← Nat.cast_pow]
  apply AddMonoid.End.ext
  intro x
  change (2 ^ upper : ℕ) • x = 0
  apply coordinates.injective
  rw [map_nsmul, map_zero]
  apply Prod.ext
  · change (2 ^ upper : ℕ) • (coordinates x).1 = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · change (2 ^ upper : ℕ) • (coordinates x).2 = 0
    rw [nsmul_eq_mul]
    have hcast : ((2 ^ upper : ℕ) : ZMod (2 ^ lower)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.pow_dvd_pow 2 hle)
    rw [hcast, zero_mul]

include hle hlower coordinates in
theorem rank_two_even_endomorphism_subgroup_generator_bound
    (Action : Subgroup (AddMonoid.End Abelian)ˣ)
    (heven : Action ≤ principalCongruenceSubgroup (AddMonoid.End Abelian) 2) :
    ∃ T : Subgroup Action, T.Normal ∧ CFSG.Open.IsElemAbelian 2 T ∧
      (∀ u : Action, u ∈ T ↔ u.val ∈ principalFourSubgroup (AddMonoid.End Abelian) ∧ u ^ 2 = 1) ∧
      pGeneratorRank 2 Action ≤ Nat.log 2 (Nat.card T) + 2 := by
  have hperiod : 2 ^ (upper - lower) * 2 ^ lower = 2 ^ upper := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  let coordinates' : Abelian ≃+ CyclicPair (2 ^ (upper - lower)) (2 ^ lower) := by
    change Abelian ≃+ (ZMod (2 ^ (upper - lower) * 2 ^ lower) × ZMod (2 ^ lower))
    rw [hperiod]
    exact coordinates
  let R := AddMonoid.End Abelian
  let F := RankTwoBinaryResidue ((2 ^ (upper - lower) : ℕ) : ZMod 2)
  let : Finite Abelian := Finite.of_equiv _ coordinates.symm.toEquiv
  let : Finite R := Finite.of_injective (fun f : R => (fun x : Abelian => f x)) (by
    intro f g h
    apply AddMonoid.End.ext
    exact congrFun h)
  let : Finite Action := Finite.of_injective (fun u : Action => u.val.val) (by
    intro u v h
    exact Subtype.ext (Units.ext h))
  have htwo : 2 ∣ 2 ^ lower := dvd_pow_self 2 (by omega : lower ≠ 0)
  let residue : R →+* F := abelianEndBinaryResidueHom _ _ htwo coordinates'
  have hkernel (r : R) : residue r = 0 ↔ ∃ s : R, r = 2 • s :=
    abelianEndBinaryResidueHom_zero _ _ htwo coordinates' r
  have hcancel (n : ℕ) (hn : 0 < n) (hdivides : n * 2 ∣ 2 ^ lower)
      (r : R) (hr : n • r = 0) : residue r = 0 := by
    let e := addEndCoordinateTransport coordinates'
    have hzero : n • e r = 0 := by
      rw [← map_nsmul, hr, map_zero]
    exact cyclicPairEndBinaryResidueHom_cancel _ _ htwo n hn hdivides (e r) hzero
  have hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0 :=
    hcancel 2 (by decide) (by
      change 2 ^ 2 ∣ 2 ^ lower
      exact Nat.pow_dvd_pow 2 (by omega))
  have hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0 :=
    hcancel 4 (by decide) (by
      change 2 ^ 3 ∣ 2 ^ lower
      exact Nat.pow_dvd_pow 2 hlower)
  have hcharacteristic := rank_two_endomorphism_characteristic upper lower hle coordinates
  have hpgroup : IsPGroup 2 Action :=
    (principal_two_isPGroup hcharacteristic).of_injective (Action.inclusion heven)
      (Subgroup.inclusion_injective heven)
  have hbound := evenAction_generator_rank_involution_bound residue hkernel hcancelTwo hcancelFour Action heven
    hpgroup hcharacteristic (rankTwoBinaryResidue_square_commutator_bound _)
  obtain ⟨T, hTNormal, hTElem, hTmem⟩ := principal_involution_subgroup_normal hcharacteristic Action
  refine ⟨T, hTNormal, hTElem, hTmem, ?_⟩
  let Deep := (Action ⊓ principalFourSubgroup R : Subgroup Rˣ)
  let Involutions := principalInvolutionSubgroup hcharacteristic Deep (fun u => u.property.2)
  have hequiv : T ≃ Involutions := {
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
  rw [Nat.card_congr hequiv]
  exact hbound

include hle hlower coordinates in
theorem rank_two_even_endomorphism_subgroup_minimum_generators
    (Action : Subgroup (AddMonoid.End Abelian)ˣ)
    (heven : Action ≤ principalCongruenceSubgroup (AddMonoid.End Abelian) 2) :
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
    rank_two_even_endomorphism_subgroup_generator_bound upper lower hle hlower coordinates Action heven
  have hpgroup : IsPGroup 2 Action :=
    (principal_two_isPGroup (rank_two_endomorphism_characteristic upper lower hle coordinates)).of_injective
      (Action.inclusion heven) (Subgroup.inclusion_injective heven)
  rw [pGeneratorRank_eq_group_rank Nat.prime_two hpgroup] at hbound
  exact ⟨T, hTnormal, hTelem, hTmem, hbound⟩

end CanonicalRankTwo

end CFSG.LargeEvenClassification.Helpers
