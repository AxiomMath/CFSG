module

public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourEvenGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem smallCfourAutomorphismEquiv_change_coordinates {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4)) (α δ : MulAut A) :
    smallCfourAutomorphismEquiv hcommutative (α.toAdditive.trans coordinates) δ =
      smallCfourAutomorphismEquiv hcommutative coordinates α *
        smallCfourAutomorphismEquiv hcommutative coordinates δ *
        (smallCfourAutomorphismEquiv hcommutative coordinates α)⁻¹ := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let e := smallCfourAutomorphismEquiv hcommutative coordinates
  have htransport : smallCfourAutomorphismEquiv hcommutative
      (α.toAdditive.trans coordinates) δ = e (α * δ * α⁻¹) := by
    apply Units.ext
    change smallCfourEndRingEquiv
      (addEndCoordinateTransport (α.toAdditive.trans coordinates) (abelianAutomorphismUnits A δ).val) =
      smallCfourEndRingEquiv
        (addEndCoordinateTransport coordinates (abelianAutomorphismUnits A (α * δ * α⁻¹)).val)
    apply congrArg smallCfourEndRingEquiv
    apply AddMonoid.End.ext
    intro x
    change coordinates (α.toAdditive (Additive.ofMul
      (δ ((α.toAdditive.symm (coordinates.symm x)).toMul)))) =
      coordinates (Additive.ofMul ((α * δ * α⁻¹) (coordinates.symm x).toMul))
    rfl
  exact htransport.trans (by rw [map_mul, map_mul, map_inv])

theorem smallCfour_conjugation_normalized_coordinates {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4)) :
    ∃ normalized : Additive A ≃+ (ZMod 4 × ZMod 4), ∀ s : S,
      smallCfourAutomorphismEquiv hcommutative normalized (MulAut.conjNormal (H := A) s)
        ∈ smallCfourSylow := by
  let e := smallCfourAutomorphismEquiv hcommutative coordinates
  let action := e.toMonoidHom.comp (MulAut.conjNormal (H := A))
  have hpimage := hpgroup.of_surjective action.rangeRestrict action.rangeRestrict_surjective
  obtain ⟨u, hu⟩ := smallCfour_two_subgroup_conjugate action.range hpimage
  let α := e.symm u
  refine ⟨α.toAdditive.trans coordinates, ?_⟩
  intro s
  rw [smallCfourAutomorphismEquiv_change_coordinates]
  change e α * action s * (e α)⁻¹ ∈ smallCfourSylow
  rw [e.apply_symm_apply]
  apply hu
  exact ⟨action s, ⟨s, rfl⟩, rfl⟩

theorem smallCfour_normalized_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4))
    (hnormalized : ∀ s : S,
      smallCfourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s)
        ∈ smallCfourSylow)
    (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let equivalence := smallCfourAutomorphismEquiv hcommutative coordinates
  let ambientAction := equivalence.toMonoidHom.comp (MulAut.conjNormal (H := A))
  let H := ambientAction.range
  have hHle : H ≤ smallCfourSylow := by
    rintro u ⟨s, rfl⟩
    exact hnormalized s
  by_cases heven : H ≤ smallCfourEvenSubgroup
  · exact small_cfour_even_action_four_generators hpgroup A hcommutative hselfCentralizing
      hnoEight coordinates (fun s => (smallCfourEvenSubgroup_mem _).mp (heven ⟨s, rfl⟩)) U
  have hHproper : H < smallCfourSylow := lt_of_le_of_ne hHle
    (small_cfour_full_action_obstruction A hcommutative hselfCentralizing hnoEight coordinates hHle)
  let action := ambientAction.comp U.subtype
  let Q := action.range
  let quotient := action.rangeRestrict
  have hpU := hpgroup.to_subgroup U
  have hpQ := hpU.of_surjective quotient action.rangeRestrict_surjective
  have hQleH : Q ≤ H := by
    rintro u ⟨s, rfl⟩
    exact ⟨s.val, rfl⟩
  have hQbound := small_cfour_proper_action_subgroup_generators H hHproper heven Q hQleH
  have hQrank : pGeneratorRank 2 Q ≤ 3 := by
    rw [pGeneratorRank_eq_group_rank Nat.prime_two hpQ]
    exact hQbound.1
  have hkernel : quotient.ker = A.comap U.subtype := by
    rw [MonoidHom.ker_rangeRestrict]
    change ambientAction.ker.comap U.subtype = A.comap U.subtype
    have hnative : ambientAction.ker = A := by
      have hnativeKernel : (MulAut.conjNormal (H := A)).ker = A :=
        (conjNormal_ker_eq_centralizer A).trans hselfCentralizing
      ext s
      change equivalence (MulAut.conjNormal (H := A) s) = 1 ↔ s ∈ A
      have hmem : s ∈ A ↔ MulAut.conjNormal (H := A) s = 1 :=
        (Subgroup.ext_iff.mp hnativeKernel s).symm
      rw [hmem, ← map_one equivalence, equivalence.injective.eq_iff]
    exact congrArg (Subgroup.comap U.subtype) hnative
  let embedding : quotient.ker →* A := {
    toFun b := ⟨b.val.val, hkernel.le b.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinjective : Function.Injective embedding := by
    intro b c h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => a.val) h
  have hcritical (hrank : pGeneratorRank 2 Q = 3) : ∃ u : U, ∃ b : quotient.ker,
      (b : U) = u ^ 2 ∧ ∀ a : A, embedding b ≠ a ^ 2 := by
    rw [pGeneratorRank_eq_group_rank Nat.prime_two hpQ] at hrank
    obtain ⟨u, hu⟩ := hQbound.2 hrank
    have hlift : equivalence (MulAut.conjNormal (H := A) u.val) =
        smallCfourEvenUnit smallCfourUpper := hu
    have hcentral (s : S) : Commute (smallCfourEvenUnit smallCfourUpper) (ambientAction s) :=
      smallCfourCentralShear _ (hHle ⟨s, rfl⟩)
    obtain ⟨square, hsquare, hprimitive, _, _, _⟩ := small_cfour_central_action_lift_square A
      hcommutative hselfCentralizing hnoEight coordinates smallCfourUpper (by decide +kernel)
      (by decide +kernel) hcentral u.val hlift
    have hmem : u ^ 2 ∈ quotient.ker := by
      rw [hkernel]
      change (u.val ^ 2 : S) ∈ A
      exact hsquare ▸ square.property
    let b : quotient.ker := ⟨u ^ 2, hmem⟩
    have hb : embedding b = square := Subtype.ext hsquare.symm
    exact ⟨u, b, rfl, fun a => hb ▸ hprimitive a⟩
  exact abelian_kernel_three_action_primitive_square_four_generators hpU (hpgroup.to_subgroup A)
    quotient action.rangeRestrict_surjective embedding hinjective
    (smallCfour_generator_rank hpgroup A hcommutative coordinates).le hQrank hcritical

theorem small_cfour_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4)) (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  obtain ⟨normalized, hnormalized⟩ :=
    smallCfour_conjugation_normalized_coordinates hpgroup A hcommutative coordinates
  exact smallCfour_normalized_four_generators hpgroup A hcommutative hselfCentralizing
    hnoEight normalized hnormalized U

theorem small_cfour_ambient_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4)) (U : Subgroup S) :
    ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  classical
  obtain ⟨generators, hgenerates, hcard⟩ := small_cfour_four_generators hpgroup A
    hcommutative hselfCentralizing hnoEight coordinates U
  refine ⟨generators.image U.subtype, Finset.card_image_le.trans hcard, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hgenerates, Subgroup.map_top]
  exact U.range_subtype

end CFSG.LargeEvenClassification.Helpers
