module

public import CFSG.LocalAnalysis.LargeEvenClassification.PrincipalCongruence

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def additiveAutomorphismUnits (Abelian : Type groupUniverse) [AddCommGroup Abelian] :
    AddAut Abelian → (AddMonoid.End Abelian)ˣ := fun automorphism => {
    val := (AddMonoid.End.equiv Abelian).symm automorphism.toAddMonoidHom
    inv := (AddMonoid.End.equiv Abelian).symm automorphism.symm.toAddMonoidHom
    val_inv := by
      apply AddMonoid.End.ext
      intro element
      exact automorphism.apply_symm_apply element
    inv_val := by
      apply AddMonoid.End.ext
      intro element
      exact automorphism.symm_apply_apply element }

theorem additiveAutomorphismUnits_injective (Abelian : Type groupUniverse) [AddCommGroup Abelian] :
    Function.Injective (additiveAutomorphismUnits Abelian) := by
  intro first second heq
  apply AddEquiv.ext
  intro element
  exact congrArg (fun unit : (AddMonoid.End Abelian)ˣ => unit.val element) heq

@[expose] def abelianAutomorphismUnits (Abelian : Type groupUniverse) [CommGroup Abelian] :
    MulAut Abelian →* (AddMonoid.End (Additive Abelian))ˣ := {
  toFun := fun automorphism => additiveAutomorphismUnits (Additive Abelian) automorphism.toAdditive
  map_one' := by
    apply Units.ext
    apply AddMonoid.End.ext
    intro element
    rfl
  map_mul' := by
    intro first second
    apply Units.ext
    apply AddMonoid.End.ext
    intro element
    rfl }

theorem abelianAutomorphismUnits_injective (Abelian : Type groupUniverse) [CommGroup Abelian] :
    Function.Injective (abelianAutomorphismUnits Abelian) := by
  intro first second heq
  apply MulEquiv.ext
  intro element
  have haction := congrArg (fun unit : (AddMonoid.End (Additive Abelian))ˣ =>
    unit.val (Additive.ofMul element)) heq
  exact congrArg Additive.toMul haction

theorem pGroup_addEnd_binary_characteristic {Abelian : Type groupUniverse} [CommGroup Abelian]
    [Finite Abelian] (hpgroup : IsPGroup 2 Abelian) :
    ∃ exponent : ℕ, (2 : AddMonoid.End (Additive Abelian)) ^ exponent = 0 := by
  obtain ⟨rank, hcard⟩ := hpgroup.exists_card_eq
  refine ⟨rank, ?_⟩
  rw [← Nat.cast_ofNat, ← Nat.cast_pow]
  apply AddMonoid.End.ext
  intro element
  change (2 ^ rank : ℕ) • element = 0
  have hpow := pow_card_eq_one' (x := element.toMul)
  rw [hcard] at hpow
  exact congrArg Additive.ofMul hpow

theorem additive_principal_norm {Abelian : Type groupUniverse} [AddCommGroup Abelian]
    {exponent : ℕ} (hcharacteristic : (2 : AddMonoid.End Abelian) ^ exponent = 0)
    (automorphism : AddAut Abelian) (operator : AddMonoid.End Abelian)
    (hprincipal : ∀ element : Abelian, automorphism element = element + 4 • operator element) :
    (∀ element : Abelian, automorphism element + element = 0 ↔ 2 • element = 0) ∧
      (∀ element : Abelian, ∃ source : Abelian, automorphism source + source = 2 • element) := by
  let normUnit : AddMonoid.End Abelian := 1 + 2 * operator
  have hinvertible : IsUnit normUnit := binary_one_add_double_isUnit hcharacteristic operator
  have hnorm : ∀ element : Abelian, automorphism element + element = normUnit (2 • element) := by
    intro element
    change automorphism element + element = 2 • element + 2 • operator (2 • element)
    rw [hprincipal, map_nsmul, smul_smul]
    norm_num
    abel
  constructor
  · intro element
    rw [hnorm]
    exact hinvertible.smul_eq_zero
  · intro element
    obtain ⟨source, hsource⟩ := hinvertible.smul_bijective.2 element
    refine ⟨source, ?_⟩
    rw [hnorm, map_nsmul]
    exact congrArg (fun vector : Abelian => 2 • vector) hsource

theorem abelian_principal_norm {Abelian : Type groupUniverse} [CommGroup Abelian] [Finite Abelian]
    (hpgroup : IsPGroup 2 Abelian) (automorphism : MulAut Abelian)
    (hprincipal : abelianAutomorphismUnits Abelian automorphism ∈
      principalFourSubgroup (AddMonoid.End (Additive Abelian))) :
    (∀ element : Abelian, automorphism element * element = 1 ↔ element ^ 2 = 1) ∧
      (∀ element : Abelian, ∃ source : Abelian, automorphism source * source = element ^ 2) := by
  obtain ⟨exponent, hcharacteristic⟩ := pGroup_addEnd_binary_characteristic hpgroup
  obtain ⟨operator, hoperator⟩ := hprincipal
  have haction : ∀ element : Additive Abelian,
      automorphism.toAdditive element = element + 4 • operator element := by
    intro element
    exact congrArg (fun endomorphism : AddMonoid.End (Additive Abelian) => endomorphism element)
      hoperator
  obtain ⟨hkernel, himage⟩ := additive_principal_norm hcharacteristic automorphism.toAdditive
    operator haction
  constructor
  · intro element
    exact hkernel (Additive.ofMul element)
  · intro element
    obtain ⟨source, hsource⟩ := himage (Additive.ofMul element)
    exact ⟨source.toMul, congrArg Additive.toMul hsource⟩

end CFSG.LargeEvenClassification.Helpers
