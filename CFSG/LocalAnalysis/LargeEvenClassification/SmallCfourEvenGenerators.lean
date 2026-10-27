module

public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniKernelCount
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourLiftSquare

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem abelian_kernel_three_action_primitive_square_four_generators
    {G A Q : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] [Group Q]
    (hpG : IsPGroup 2 G) (hpA : IsPGroup 2 A) (quotient : G →* Q)
    (hsurjective : Function.Surjective quotient) (embedding : quotient.ker →* A)
    (hinjective : Function.Injective embedding) (hArank : pGeneratorRank 2 A ≤ 2)
    (hQrank : pGeneratorRank 2 Q ≤ 3)
    (hcritical : pGeneratorRank 2 Q = 3 → ∃ u : G, ∃ b : quotient.ker,
      (b : G) = u ^ 2 ∧ ∀ a : A, embedding b ≠ a ^ 2) :
    ∃ X : Finset G, Subgroup.closure (X : Set G) = ⊤ ∧ X.card ≤ 4 := by
  let B := quotient.ker
  have hcommutative : IsMulCommutative B := by
    apply isMulCommutative_iff.mpr
    intro b c
    apply hinjective
    rw [map_mul, map_mul, mul_comm]
  let : CommGroup B := { (inferInstance : Group B) with mul_comm := @mul_comm' B _ hcommutative }
  have hBrank : pGeneratorRank 2 B ≤ 2 :=
    (commutative_pGeneratorRank_embedding_le Nat.prime_two hpA embedding hinjective).trans hArank
  have e : G ⧸ B ≃* Q := QuotientGroup.quotientKerEquivOfSurjective quotient hsurjective
  have hquotient := pGeneratorRank_mulEquiv Nat.prime_two (hpG.to_quotient B) e
  have hGrank : pGeneratorRank 2 G ≤ 4 := by
    by_cases hsmall : pGeneratorRank 2 Q ≤ 2
    · have h := pGeneratorRank_extension_le Nat.prime_two hpG B
      rw [hquotient] at h
      omega
    · obtain ⟨u, b, hsquare, hprimitive⟩ := hcritical (by omega)
      have hfrattini : (b : G) ∈ frattini G := hsquare ▸ pGroup_pow_mem_frattini Nat.prime_two hpG u
      have hnotPower : ¬∃ a : B, a ^ 2 = b := by
        rintro ⟨a, ha⟩
        exact hprimitive (embedding a) (congrArg embedding ha |>.symm.trans (map_pow embedding a 2))
      have h := pGeneratorRank_normal_square_saving Nat.prime_two hpG B hcommutative b hfrattini hnotPower
      rw [hquotient] at h
      omega
  obtain ⟨X, hgenerates, hcard⟩ := pGeneratorRank_generators Nat.prime_two hpG
  exact ⟨X, hgenerates, hcard.trans_le hGrank⟩

theorem smallCfour_even_action_proper {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4))
    (heven : ∀ s : S, smallCfourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s)
      ∈ smallCfourEvenSubgroup) :
    ((smallCfourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range ≠ smallCfourEvenSubgroup := by
  let action := (smallCfourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
    (MulAut.conjNormal (H := A))
  intro hfull
  have hrotation : smallCfourEvenUnit smallCfourRotation ∈ action.range := by
    rw [hfull]
    exact ⟨Multiplicative.ofAdd smallCfourRotation, rfl⟩
  obtain ⟨t, ht⟩ := hrotation
  have hcentral (s : S) : Commute (smallCfourEvenUnit smallCfourRotation) (action s) :=
    smallCfour_even_units_commute _ _ ⟨Multiplicative.ofAdd smallCfourRotation, rfl⟩ (heven s)
  obtain ⟨_, _, _, _, _, hsingular⟩ := small_cfour_central_action_lift_square A hcommutative
    hselfCentralizing hnoEight coordinates smallCfourRotation (by decide +kernel)
    (by decide +kernel) hcentral t ht
  have hdet : smallCfourBinaryDeterminant smallCfourRotation = 1 := by decide +kernel
  have hbad : (1 : ZMod 2) = 0 := hdet.symm.trans hsingular
  revert hbad
  decide

theorem smallCfour_generator_rank {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) (hcommutative : IsMulCommutative A)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4)) : pGeneratorRank 2 A = 2 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  have hcoordinates := AddEquiv.toMultiplicativeRight coordinates
  have hpA := hpgroup.to_subgroup A
  rw [pGeneratorRank_mulEquiv Nat.prime_two hpA hcoordinates]
  have hcard : Nat.card (Multiplicative (ZMod 4 × ZMod 4) ⧸
      frattini (Multiplicative (ZMod 4 × ZMod 4))) = 4 := by
    rw [commutative_frattini_eq_power_range Nat.prime_two (hpA.of_equiv hcoordinates)]
    have htotal := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (powMonoidHom 2 : Multiplicative (ZMod 4 × ZMod 4) →* _).range
    have hrange : Nat.card (powMonoidHom 2 : Multiplicative (ZMod 4 × ZMod 4) →* _).range = 4 := by
      change Nat.card {x : Multiplicative (ZMod 4 × ZMod 4) // ∃ y, y ^ 2 = x} = 4
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    have htotalCard : Nat.card (Multiplicative (ZMod 4 × ZMod 4)) = 16 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hrange, htotalCard] at htotal
    omega
  change Nat.log 2 (Nat.card _) = 2
  rw [hcard]
  decide

theorem small_cfour_even_action_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ (ZMod 4 × ZMod 4))
    (heven : ∀ s : S, smallCfourBinaryHom
      (smallCfourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s)).val = 1)
    (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let equivalence := smallCfourAutomorphismEquiv hcommutative coordinates
  let ambientAction := equivalence.toMonoidHom.comp (MulAut.conjNormal (H := A))
  let H := ambientAction.range
  have hHle : H ≤ smallCfourEvenSubgroup := by
    rintro u ⟨s, rfl⟩
    exact (smallCfourEvenSubgroup_mem _).mpr (heven s)
  have hHproper := smallCfour_even_action_proper A hcommutative hselfCentralizing hnoEight
    coordinates (fun s => (smallCfourEvenSubgroup_mem _).mpr (heven s))
  let action := ambientAction.comp U.subtype
  let Q := action.range
  let quotient := action.rangeRestrict
  have hpU := hpgroup.to_subgroup U
  have hpQ := hpU.of_surjective quotient action.rangeRestrict_surjective
  have hQleH : Q ≤ H := by
    rintro u ⟨s, rfl⟩
    exact ⟨s.val, rfl⟩
  have hQle := hQleH.trans hHle
  have hQproper : Q ≠ smallCfourEvenSubgroup := by
    intro h
    apply hHproper
    exact le_antisymm hHle (h.symm ▸ hQleH)
  have hQrank := smallCfour_proper_even_generator_rank Q hQle hQproper hpQ
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
      rw [hmem]
      rw [← map_one equivalence, equivalence.injective.eq_iff]
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
    let hom := smallCfourEvenCoordinateHom Q hQle
    let W := binaryHomRange hom
    have hdimension : Module.finrank (ZMod 2) W = 3 :=
      (smallCfourEvenCoordinateHom_generator_rank Q hQle hpQ).symm.trans hrank
    obtain ⟨f, hf, hnonzero, hunit⟩ := small_cfour_matrix_hyperplane_norm_element W hdimension
    obtain ⟨q, hq⟩ := (binaryHomRange_mem hom f).mp hf
    obtain ⟨u, hu⟩ := q.property
    have hlift : equivalence (MulAut.conjNormal (H := A) u.val) = smallCfourEvenUnit f := by
      have hcoord := smallCfourEvenCoordinateHom_spec Q hQle q
      rw [hq] at hcoord
      exact hu.trans hcoord.symm
    have hcentral (s : S) : Commute (smallCfourEvenUnit f) (ambientAction s) :=
      smallCfour_even_units_commute _ _ ⟨Multiplicative.ofAdd f, rfl⟩ (hHle ⟨s, rfl⟩)
    obtain ⟨square, hsquare, hprimitive, _, _, _⟩ := small_cfour_central_action_lift_square A hcommutative
      hselfCentralizing hnoEight coordinates f hnonzero ((smallCfourBinary_isUnit_iff _).mp hunit)
      hcentral u.val hlift
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

end CFSG.LargeEvenClassification.Helpers
