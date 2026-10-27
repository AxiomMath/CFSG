module

public import CFSG.LocalAnalysis.LargeEvenClassification.UnequalFullActionGeneratorBound
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsLiftSquare

public section

namespace CFSG.LargeEvenClassification.Helpers

section KernelSaving

variable {G A T : Type*} [Group G] [Finite G] [CommGroup A] [Finite A]
variable [CommGroup T] [Finite T]
variable (hpG : IsPGroup 2 G) (hpA : IsPGroup 2 A)
variable (B : Subgroup G) [B.Normal] (hcommutative : IsMulCommutative B)
variable (embedding : B →* A) (hexponent : ∀ t : T, t ^ 2 = 1)

include hpG hpA hcommutative hexponent in
theorem abelian_kernel_ambient_frattini_saving
    (injection : T →* (A ⧸ frattini A)) (hinjective : Function.Injective injection)
    (hlifts : ∀ t : T, ∃ b : B, (b : G) ∈ frattini G ∧
      (QuotientGroup.mk' (frattini A)) (embedding b) = injection t) :
    pGeneratorRank 2 G + Nat.log 2 (Nat.card T) ≤
      pGeneratorRank 2 (G ⧸ B) + pGeneratorRank 2 B := by
  classical
  let : CommGroup B := { (inferInstance : Group B) with
    mul_comm := @mul_comm' B _ hcommutative }
  let : CommGroup (A ⧸ frattini A) := pGroupFrattiniCommGroup Nat.prime_two hpA
  let : Module (ZMod 2) (Additive (A ⧸ frattini A)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpA)
  let : Module (ZMod 2) (Additive T) := elementaryZModModule hexponent
  let basis := Module.finBasis (ZMod 2) (Additive T)
  let family : Fin (Module.finrank (ZMod 2) (Additive T)) → B :=
    fun i => Classical.choose (hlifts (basis i).toMul)
  have hfamily i : (family i : G) ∈ frattini G ∧
      (QuotientGroup.mk' (frattini A)) (embedding (family i)) = injection (basis i).toMul :=
    Classical.choose_spec (hlifts (basis i).toMul)
  have hpB := hpG.to_subgroup B
  let : CommGroup (B ⧸ frattini B) := pGroupFrattiniCommGroup Nat.prime_two hpB
  let moduleB : Module (ZMod 2) (Additive (B ⧸ frattini B)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpB)
  let := moduleB
  let projection := (QuotientGroup.mk' (frattini A)).comp embedding
  have hkernel : frattini B ≤ projection.ker := by
    rw [commutative_frattini_eq_power_range (Ambient := B) Nat.prime_two hpB]
    rintro b ⟨x, rfl⟩
    change (QuotientGroup.mk' (frattini A)) (embedding (x ^ 2)) = 1
    rw [map_pow, map_pow]
    exact pGroup_frattini_quotient_exponent Nat.prime_two hpA _
  let induced := QuotientGroup.lift (frattini B) projection hkernel
  let linear := induced.toAdditive.toZModLinearMap 2
  let injectiveLinear := injection.toAdditive.toZModLinearMap 2
  have hindependent := basis.linearIndependent.map' injectiveLinear
    (LinearMap.ker_eq_bot.mpr (by
      intro x y h
      exact congrArg Additive.ofMul (hinjective (congrArg Additive.toMul h))))
  have heq i : linear (Additive.ofMul ((QuotientGroup.mk' (frattini B)) (family i))) =
      injectiveLinear (basis i) := by
    change Additive.ofMul (projection (family i)) = Additive.ofMul (injection (basis i).toMul)
    exact congrArg Additive.ofMul (hfamily i).2
  have hfamilyIndependent : LinearIndependent (ZMod 2)
      (fun i => Additive.ofMul ((QuotientGroup.mk' (frattini B)) (family i))) := by
    apply LinearIndependent.of_comp linear
    have heqFamily :
        (linear ∘ fun i => Additive.ofMul ((QuotientGroup.mk' (frattini B)) (family i))) =
          injectiveLinear ∘ basis := funext heq
    rw [heqFamily]
    exact hindependent
  have hsaving := pGeneratorRank_normal_independent_saving Nat.prime_two hpG B family
    (fun i => (hfamily i).1) moduleB hfamilyIndependent
  rw [Fintype.card_fin, ← elementary_log_card_eq_finrank Nat.prime_two] at hsaving
  exact hsaving

end KernelSaving

@[expose] def rankTwoAddCoordinates {A : Type*} [CommGroup A] {upper lower : ℕ}
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ upper)) × Multiplicative (ZMod (2 ^ lower))) :
    Additive A ≃+ (ZMod (2 ^ upper) × ZMod (2 ^ lower)) where
  toFun x := ((coordinates x.toMul).1.toAdd, (coordinates x.toMul).2.toAdd)
  invFun x := Additive.ofMul (coordinates.symm (Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2))
  left_inv x := by change Additive.ofMul (coordinates.symm (coordinates x.toMul)) = x; rw [coordinates.symm_apply_apply]; rfl
  right_inv x := by change ((coordinates (coordinates.symm _)).1.toAdd, (coordinates (coordinates.symm _)).2.toAdd) = x; rw [coordinates.apply_symm_apply]; rfl
  map_add' x y := by change ((coordinates (x.toMul * y.toMul)).1.toAdd, (coordinates (x.toMul * y.toMul)).2.toAdd) = _; rw [map_mul]; rfl

theorem rank_two_full_automorphism_generator_bound {A : Type*} [CommGroup A]
    (upper lower : ℕ) (hordered : lower ≤ upper) (hlarge : 3 ≤ lower)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ upper)) × Multiplicative (ZMod (2 ^ lower)))
    (Action : Subgroup (MulAut A)) [Finite Action] (hpgroup : IsPGroup 2 Action) :
    ∃ T : Subgroup Action, T.Normal ∧ CFSG.Open.IsElemAbelian 2 T ∧
      (∀ u : Action, u ∈ T ↔ u.val ∈ deepAbelianAutomorphisms A ∧ u ^ 2 = 1) ∧
      pGeneratorRank 2 Action ≤ Nat.log 2 (Nat.card T) + 2 := by
  let units := abelianAutomorphismUnits A
  let UnitsAction := Action.map units
  let e := Action.equivMapOfInjective units (abelianAutomorphismUnits_injective A)
  let : Finite UnitsAction := Finite.of_equiv Action e.toEquiv
  have hpUnits := hpgroup.of_equiv e
  have hnative : ∃ T : Subgroup UnitsAction, T.Normal ∧ CFSG.Open.IsElemAbelian 2 T ∧
      (∀ u : UnitsAction, u ∈ T ↔ u.val ∈ principalFourSubgroup (AddMonoid.End (Additive A)) ∧ u ^ 2 = 1) ∧
      pGeneratorRank 2 UnitsAction ≤ Nat.log 2 (Nat.card T) + 2 := by
    by_cases hequal : upper = lower
    · subst upper
      exact rank_two_homocyclic_full_action_generator_bound lower hlarge (rankTwoAddCoordinates coordinates)
        UnitsAction hpUnits
    · exact rank_two_unequal_full_action_generator_bound upper lower (by omega) hlarge
        (rankTwoAddCoordinates coordinates) UnitsAction hpUnits
  obtain ⟨NativeT, hnormal, helementary, hshape, hbound⟩ := hnative
  let : NativeT.Normal := hnormal
  let T := NativeT.comap e.toMonoidHom
  let eT : T ≃* NativeT := {
    toFun u := ⟨e u.val, u.property⟩
    invFun u := ⟨e.symm u.val, by change e (e.symm u.val) ∈ NativeT; rw [e.apply_symm_apply]; exact u.property⟩
    left_inv u := by apply Subtype.ext; exact e.symm_apply_apply u.val
    right_inv u := by apply Subtype.ext; exact e.apply_symm_apply u.val
    map_mul' u v := Subtype.ext (map_mul e u.val v.val) }
  have hTelem : CFSG.Open.IsElemAbelian 2 T := by
    constructor
    · apply isMulCommutative_iff.mpr
      intro u v
      apply eT.injective
      rw [map_mul, map_mul]
      exact @mul_comm' NativeT _ helementary.1 _ _
    · intro u hu
      apply e.injective
      rw [map_pow, map_one]
      exact helementary.2 (e u) hu
  refine ⟨T, inferInstance, hTelem, ?_, ?_⟩
  · intro u
    change e u ∈ NativeT ↔ _
    rw [hshape]
    constructor
    · rintro ⟨hdeep, hsquare⟩
      exact ⟨hdeep, e.injective (by rw [map_pow, map_one]; exact hsquare)⟩
    · rintro ⟨hdeep, hsquare⟩
      exact ⟨hdeep, by rw [← map_pow, hsquare, map_one]⟩
  · rw [pGeneratorRank_mulEquiv Nat.prime_two hpgroup e, Nat.card_congr eT.toEquiv]
    exact hbound

theorem rank_two_large_exponent_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (upper lower : ℕ) (hordered : lower ≤ upper) (hlarge : 3 ≤ lower)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ upper)) × Multiplicative (ZMod (2 ^ lower)))
    (U : Subgroup S) :
    ∃ generators : Finset U, Subgroup.closure (generators : Set U) = ⊤ ∧ generators.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := @mul_comm' A _ hcommutative }
  obtain ⟨AmbientT, _, hAmbientShape, _, squareMap, hsquareInjective, hsquares, _, _, _⟩ :=
    exists_rank_two_deep_lift_square_injection hpgroup A hcommutative hselfCentralizing hnoEight
      hordered hlarge coordinates
  let action : U →* MulAut A := (MulAut.conjNormal (H := A)).comp U.subtype
  let Action := action.range
  let quotient := action.rangeRestrict
  have hpU := hpgroup.to_subgroup U
  have hpAction := hpU.of_surjective quotient action.rangeRestrict_surjective
  have hkernel : quotient.ker = A.comap U.subtype := by
    rw [MonoidHom.ker_rangeRestrict]
    change (MulAut.conjNormal (H := A)).ker.comap U.subtype = _
    rw [conjNormal_ker_eq_centralizer A, hselfCentralizing]
  let B := quotient.ker
  let embedding : B →* A := {
    toFun b := ⟨b.val.val, hkernel.le b.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hembedding : Function.Injective embedding := by
    intro b c h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => a.val) h
  have hBcommutative : IsMulCommutative B := by
    apply isMulCommutative_iff.mpr
    intro b c
    apply hembedding
    rw [map_mul, map_mul, mul_comm]
  obtain ⟨T, _, hTelem, hTshape, hactionBound⟩ :=
    rank_two_full_automorphism_generator_bound upper lower hordered hlarge coordinates Action hpAction
  let toAmbientT : T →* AmbientT := {
    toFun t := ⟨t.val.val, by
      apply (hAmbientShape _).mpr
      have ht := (hTshape t.val).mp t.property
      refine ⟨ht.1, congrArg (fun g : Action => g.val) ht.2, ?_⟩
      obtain ⟨u, hu⟩ := t.val.property
      exact ⟨u.val, hu⟩⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have htoAmbient : Function.Injective toAmbientT := by
    intro t v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : AmbientT => a.val) h
  let injection := squareMap.comp toAmbientT
  have hinjective : Function.Injective injection := hsquareInjective.comp htoAmbient
  have hlifts (t : T) : ∃ b : B, (b : U) ∈ frattini U ∧
      (QuotientGroup.mk' (frattini A)) (embedding b) = injection t := by
    obtain ⟨u, hu⟩ := t.val.property
    have hsquare : u ^ 2 ∈ B := by
      apply Subtype.ext
      change action (u ^ 2) = 1
      rw [map_pow, hu]
      exact congrArg (fun g : Action => g.val) ((hTshape t.val).mp t.property).2
    let b : B := ⟨u ^ 2, hsquare⟩
    obtain ⟨a, ha, hmap⟩ := hsquares u.val (toAmbientT t) hu
    have hab : embedding b = a := by
      apply Subtype.ext
      exact ha.symm
    refine ⟨b, pGroup_pow_mem_frattini Nat.prime_two hpU u, ?_⟩
    rw [hab]
    exact hmap.symm
  let : CommGroup T := { (inferInstance : Group T) with mul_comm := @mul_comm' T _ hTelem.1 }
  have hexponent (t : T) : t ^ 2 = 1 := by
    apply Subtype.ext
    exact hTelem.2 t.val t.property
  have hsaving := abelian_kernel_ambient_frattini_saving hpU (hpgroup.to_subgroup A) B
    hBcommutative embedding hexponent injection hinjective hlifts
  have hAcard := binary_rank_two_frattini_quotient_card hpgroup A hcommutative
    (by omega) (by omega) coordinates
  have hArank : pGeneratorRank 2 A = 2 := by
    change Nat.log 2 (Nat.card (A ⧸ frattini A)) = 2
    rw [hAcard]
    decide
  let : CommGroup B := { (inferInstance : Group B) with
    mul_comm := @mul_comm' B _ hBcommutative }
  have hBrank := commutative_pGeneratorRank_embedding_le Nat.prime_two
    (hpgroup.to_subgroup A) embedding hembedding
  rw [hArank] at hBrank
  have e : U ⧸ B ≃* Action := QuotientGroup.quotientKerEquivOfSurjective quotient action.rangeRestrict_surjective
  have hquotient := pGeneratorRank_mulEquiv Nat.prime_two (hpU.to_quotient B) e
  rw [hquotient] at hsaving
  have hUrank : pGeneratorRank 2 U ≤ 4 := by omega
  obtain ⟨generators, hgenerates, hcard⟩ := pGeneratorRank_generators Nat.prime_two hpU
  exact ⟨generators, hgenerates, hcard.trans_le hUrank⟩

theorem rank_two_large_exponent_ambient_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (upper lower : ℕ) (hordered : lower ≤ upper) (hlarge : 3 ≤ lower)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ upper)) × Multiplicative (ZMod (2 ^ lower)))
    (U : Subgroup S) :
    ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  classical
  obtain ⟨generators, hgenerates, hcard⟩ := rank_two_large_exponent_four_generators hpgroup A
    hcommutative hselfCentralizing hnoEight upper lower hordered hlarge coordinates U
  refine ⟨generators.image U.subtype, Finset.card_image_le.trans hcard, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hgenerates, Subgroup.map_top]
  exact U.range_subtype

end CFSG.LargeEvenClassification.Helpers
