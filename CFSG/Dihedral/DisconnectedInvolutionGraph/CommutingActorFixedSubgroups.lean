module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeInvolutionQuotient

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction A G]

@[expose] def actorFixedSubgroup (actor : A) : Subgroup G :=
  (MulDistribMulAction.toMonoidHom G actor).eqLocus (MonoidHom.id G)

@[simp]
theorem mem_actorFixedSubgroup (actor : A) (element : G) :
    element ∈ actorFixedSubgroup (G := G) actor ↔ actor • element = element := Iff.rfl

theorem commuting_actor_fixed_subgroup_invariant (actor : A) :
    InvariantSubgroup (A := A) (actorFixedSubgroup (G := G) actor) := by
  intro other element hfixed
  change actor • (other • element) = other • element
  rw [← mul_smul, mul_comm actor other, mul_smul]
  exact congrArg (fun value : G => other • value) hfixed

theorem invariant_subgroup_sup (first second : Subgroup G)
    (hfirst : InvariantSubgroup (A := A) first)
    (hsecond : InvariantSubgroup (A := A) second) :
    InvariantSubgroup (A := A) (first ⊔ second) := by
  intro actor
  have hmap : (first ⊔ second).map (MulDistribMulAction.toMonoidHom G actor) ≤
      first ⊔ second := by
    rw [Subgroup.map_sup]
    apply sup_le
    · apply le_trans (b := first) _ le_sup_left
      apply Subgroup.map_le_iff_le_comap.mpr
      intro element hmem
      exact hfirst actor element hmem
    · apply le_trans (b := second) _ le_sup_right
      apply Subgroup.map_le_iff_le_comap.mpr
      intro element hmem
      exact hsecond actor element hmem
  intro element hmem
  exact hmap (Subgroup.mem_map.mpr ⟨element, hmem, rfl⟩)

theorem commuting_involutions_fixed_subgroups_generate_of_normal
    [Finite G] (first second : A)
    (hfirstSquare : first * first = 1) (hsecondSquare : second * second = 1)
    (subgroup : Subgroup G) [subgroup.Normal]
    (hinvariant : InvariantSubgroup (A := A) subgroup) (hodd : Odd (Nat.card subgroup))
    (hfirstFixed : actorFixedSubgroup (G := G) first ≤ subgroup)
    (hsecondFixed : actorFixedSubgroup (G := G) second ≤ subgroup)
    (hproductFixed : actorFixedSubgroup (G := G) (first * second) ≤ subgroup) :
    subgroup = ⊤ := by
  let _ := invariantQuotientAction subgroup hinvariant
  have hproductSquare : (first * second) * (first * second) = 1 := by
    calc
      (first * second) * (first * second) = (first * first) * (second * second) := by ac_rfl
      _ = 1 := by rw [hfirstSquare, hsecondSquare, one_mul]
  have hfirstFree := involution_actor_quotient_fixedPointFree first hfirstSquare subgroup
    hinvariant hodd (fun element hfixed => hfirstFixed hfixed)
  have hsecondFree := involution_actor_quotient_fixedPointFree second hsecondSquare subgroup
    hinvariant hodd (fun element hfixed => hsecondFixed hfixed)
  have hproductFree := involution_actor_quotient_fixedPointFree (first * second) hproductSquare
    subgroup hinvariant hodd (fun element hfixed => hproductFixed hfixed)
  have hfirstInvolutive : Function.Involutive (fun quotient : G ⧸ subgroup => first • quotient) := by
    intro quotient
    change first • (first • quotient) = quotient
    rw [← mul_smul, hfirstSquare, one_smul]
  have hsecondInvolutive : Function.Involutive (fun quotient : G ⧸ subgroup => second • quotient) := by
    intro quotient
    change second • (second • quotient) = quotient
    rw [← mul_smul, hsecondSquare, one_smul]
  have hfirstInv := hfirstFree.coe_eq_inv_of_involutive (φ :=
    MulDistribMulAction.toMonoidHom (G ⧸ subgroup) first) hfirstInvolutive
  have hsecondInv := hsecondFree.coe_eq_inv_of_involutive (φ :=
    MulDistribMulAction.toMonoidHom (G ⧸ subgroup) second) hsecondInvolutive
  apply QuotientGroup.subsingleton_iff.mp
  refine ⟨fun firstQuotient secondQuotient => ?_⟩
  have hall : ∀ quotient : G ⧸ subgroup, quotient = 1 := by
    intro quotient
    apply hproductFree
    change (first * second) • quotient = quotient
    rw [mul_smul]
    rw [show second • quotient = quotient⁻¹ from congrFun hsecondInv quotient,
      show first • quotient⁻¹ = (quotient⁻¹)⁻¹ from congrFun hfirstInv quotient⁻¹, inv_inv]
  exact (hall firstQuotient).trans (hall secondQuotient).symm

end CFSG.DisconnectedInvolutionGraph.Helpers
