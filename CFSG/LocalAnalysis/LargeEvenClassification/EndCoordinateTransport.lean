module

public import CFSG.LocalAnalysis.LargeEvenClassification.DeepAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoResidualMap

public section

namespace CFSG.LargeEvenClassification.Helpers

universe sourceUniverse targetUniverse

@[expose] def addEndCoordinateTransport {Source : Type sourceUniverse} {Target : Type targetUniverse}
    [AddCommGroup Source] [AddCommGroup Target] (coordinates : Source ≃+ Target) :
    AddMonoid.End Source ≃+* AddMonoid.End Target where
  toFun := fun operator => (AddMonoid.End.equiv Target).symm
    (coordinates.toAddMonoidHom.comp ((AddMonoid.End.equiv Source operator).comp
      coordinates.symm.toAddMonoidHom))
  invFun := fun operator => (AddMonoid.End.equiv Source).symm
    (coordinates.symm.toAddMonoidHom.comp ((AddMonoid.End.equiv Target operator).comp
      coordinates.toAddMonoidHom))
  left_inv := by
    intro operator
    apply AddMonoid.End.ext
    intro element
    change coordinates.symm (coordinates (operator (coordinates.symm (coordinates element)))) = _
    rw [coordinates.symm_apply_apply, coordinates.symm_apply_apply]
  right_inv := by
    intro operator
    apply AddMonoid.End.ext
    intro element
    change coordinates (coordinates.symm (operator (coordinates (coordinates.symm element)))) = _
    rw [coordinates.apply_symm_apply, coordinates.apply_symm_apply]
  map_add' := by
    intro first second
    apply AddMonoid.End.ext
    intro element
    exact map_add coordinates _ _
  map_mul' := by
    intro first second
    apply AddMonoid.End.ext
    intro element
    change coordinates (first (second (coordinates.symm element))) =
      coordinates (first (coordinates.symm (coordinates (second (coordinates.symm element)))))
    rw [coordinates.symm_apply_apply]

theorem addEndCoordinateTransport_apply {Source : Type sourceUniverse} {Target : Type targetUniverse}
    [AddCommGroup Source] [AddCommGroup Target] (coordinates : Source ≃+ Target)
    (operator : AddMonoid.End Source) (element : Target) :
    addEndCoordinateTransport coordinates operator element = coordinates (operator (coordinates.symm element)) := rfl

theorem addEndCoordinateTransport_principal_iff {Source : Type sourceUniverse}
    {Target : Type targetUniverse} [AddCommGroup Source] [AddCommGroup Target]
    (coordinates : Source ≃+ Target) (unit : (AddMonoid.End Source)ˣ) :
    Units.map (addEndCoordinateTransport coordinates).toMonoidHom unit ∈
      principalFourSubgroup (AddMonoid.End Target) ↔
        unit ∈ principalFourSubgroup (AddMonoid.End Source) := by
  let transport := addEndCoordinateTransport coordinates
  change (∃ operator : AddMonoid.End Target, transport unit.val = 1 + 4 * operator) ↔
    ∃ operator : AddMonoid.End Source, unit.val = 1 + 4 * operator
  constructor
  · rintro ⟨operator, hoperator⟩
    refine ⟨transport.symm operator, ?_⟩
    have heq := congrArg transport.symm hoperator
    simpa only [transport.symm_apply_apply, map_add, map_one, map_mul, map_ofNat] using heq
  · rintro ⟨operator, hoperator⟩
    refine ⟨transport operator, ?_⟩
    rw [hoperator, map_add, map_one, map_mul, map_ofNat]

@[expose] def multiplicativePairAddCoordinates {Abelian : Type sourceUniverse} [CommGroup Abelian]
    {scale modulus : ℕ} (coordinates : Abelian ≃*
      Multiplicative (ZMod (scale * modulus)) × Multiplicative (ZMod modulus)) :
    Additive Abelian ≃+ CyclicPair scale modulus where
  toFun := fun element => ((coordinates element.toMul).1.toAdd, (coordinates element.toMul).2.toAdd)
  invFun := fun element => Additive.ofMul
    (coordinates.symm (Multiplicative.ofAdd element.1, Multiplicative.ofAdd element.2))
  left_inv := by
    intro element
    change Additive.ofMul (coordinates.symm (coordinates element.toMul)) = element
    rw [coordinates.symm_apply_apply]
    rfl
  right_inv := by
    intro element
    change ((coordinates (coordinates.symm _)).1.toAdd, (coordinates (coordinates.symm _)).2.toAdd) = element
    rw [coordinates.apply_symm_apply]
    rfl
  map_add' := by
    intro first second
    change ((coordinates (first.toMul * second.toMul)).1.toAdd,
      (coordinates (first.toMul * second.toMul)).2.toAdd) = _
    rw [map_mul]
    rfl

section Action

variable {Abelian : Type sourceUniverse} [CommGroup Abelian]
variable (scale modulus : ℕ) [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)]
variable (hfour : 4 ∣ modulus) (coordinates : Additive Abelian ≃+ CyclicPair scale modulus)

@[expose] noncomputable def abelianCoordinateResidualHom : MulAut Abelian →* (ResidualRing (scale : ZMod 4))ˣ :=
  (cyclicPairResidualUnits scale modulus hfour).comp
    ((Units.map (addEndCoordinateTransport coordinates).toMonoidHom).comp
      (abelianAutomorphismUnits Abelian))

theorem abelianCoordinateResidualHom_kernel :
    (abelianCoordinateResidualHom scale modulus hfour coordinates).ker =
      deepAbelianAutomorphisms Abelian := by
  ext automorphism
  change cyclicPairResidualUnits scale modulus hfour
    (Units.map (addEndCoordinateTransport coordinates).toMonoidHom
      (abelianAutomorphismUnits Abelian automorphism)) = 1 ↔
    abelianAutomorphismUnits Abelian automorphism ∈
      principalFourSubgroup (AddMonoid.End (Additive Abelian))
  rw [cyclicPairResidualUnits_kernel, addEndCoordinateTransport_principal_iff]

include hfour coordinates in
theorem abelianCoordinateResidualQuotient_embedding (Action : Subgroup (MulAut Abelian)) :
    let Deep := (deepAbelianAutomorphisms Abelian).comap Action.subtype
    let _ : Deep.Normal := Subgroup.Normal.comap (deepAbelianAutomorphisms_normal Abelian) Action.subtype
    ∃ embedding : (Action ⧸ Deep) →* (ResidualRing (scale : ZMod 4))ˣ,
      Function.Injective embedding := by
  dsimp only
  let Deep := (deepAbelianAutomorphisms Abelian).comap Action.subtype
  let : Deep.Normal := Subgroup.Normal.comap (deepAbelianAutomorphisms_normal Abelian) Action.subtype
  let residual := (abelianCoordinateResidualHom scale modulus hfour coordinates).comp Action.subtype
  have hkernel : residual.ker = Deep := by
    ext automorphism
    change abelianCoordinateResidualHom scale modulus hfour coordinates (automorphism : MulAut Abelian) = 1 ↔
      (automorphism : MulAut Abelian) ∈ deepAbelianAutomorphisms Abelian
    exact Subgroup.ext_iff.mp (abelianCoordinateResidualHom_kernel scale modulus hfour coordinates) _
  refine ⟨QuotientGroup.lift Deep residual hkernel.symm.le, ?_⟩
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr hkernel.symm

theorem binary_power_residual_twist (exponent : ℕ) :
    (2 ^ exponent : ZMod 4) = 1 ∨ (2 ^ exponent : ZMod 4) = 0 ∨
      (2 ^ exponent : ZMod 4) = 2 := by
  rcases exponent with _ | exponent
  · exact Or.inl (by simp)
  rcases exponent with _ | exponent
  · exact Or.inr (Or.inr (by simp))
  · apply Or.inr
    apply Or.inl
    rw [pow_succ, pow_succ, mul_assoc]
    have hzero : (2 : ZMod 4) * 2 = 0 := by decide
    rw [hzero, mul_zero]

include hfour coordinates in
theorem abelianCoordinateResidualQuotient_rank (exponent : ℕ) (hscale : scale = 2 ^ exponent)
    (Action : Subgroup (MulAut Abelian)) [Finite Action] (hpgroup : IsPGroup 2 Action) :
    let Deep := (deepAbelianAutomorphisms Abelian).comap Action.subtype
    let _ : Deep.Normal := Subgroup.Normal.comap (deepAbelianAutomorphisms_normal Abelian) Action.subtype
    pGeneratorRank 2 (Action ⧸ Deep) ≤ 5 := by
  dsimp only
  let Deep := (deepAbelianAutomorphisms Abelian).comap Action.subtype
  let : Deep.Normal := Subgroup.Normal.comap (deepAbelianAutomorphisms_normal Abelian) Action.subtype
  obtain ⟨embedding, hinjective⟩ := abelianCoordinateResidualQuotient_embedding scale modulus hfour coordinates Action
  have htwist : (scale : ZMod 4) = 1 ∨ (scale : ZMod 4) = 0 ∨ (scale : ZMod 4) = 2 := by
    rw [hscale, Nat.cast_pow, Nat.cast_ofNat]
    exact binary_power_residual_twist exponent
  exact residual_binary_two_subgroup_generator_rank (hpgroup.to_quotient Deep)
    htwist embedding hinjective

end Action

end CFSG.LargeEvenClassification.Helpers
