module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicTwoTransfer
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneSylowTransport

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

theorem quaternion_unique_involution (size : ℕ) [NeZero size]
    (first second : Involution (QuaternionGroup size)) : first = second := by
  let coordinates : Multiplicative (ZMod (2 * size)) →* QuaternionGroup size :=
    { toFun := fun coordinate => QuaternionGroup.a (Multiplicative.toAdd coordinate)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinjective : Function.Injective coordinates := by
    intro first second hequal
    exact congrArg Multiplicative.ofAdd (QuaternionGroup.a.inj hequal)
  have hfirstA : ∃ coordinate : ZMod (2 * size), (first : QuaternionGroup size) =
      QuaternionGroup.a coordinate := by
    cases helement : first.val with
    | a coordinate => exact ⟨coordinate, rfl⟩
    | xa coordinate =>
      have horder := first.property
      rw [helement, QuaternionGroup.orderOf_xa] at horder
      omega
  have hsecondA : ∃ coordinate : ZMod (2 * size), (second : QuaternionGroup size) =
      QuaternionGroup.a coordinate := by
    cases helement : second.val with
    | a coordinate => exact ⟨coordinate, rfl⟩
    | xa coordinate =>
      have horder := second.property
      rw [helement, QuaternionGroup.orderOf_xa] at horder
      omega
  obtain ⟨firstCoordinate, hfirst⟩ := hfirstA
  obtain ⟨secondCoordinate, hsecond⟩ := hsecondA
  have hfirstOrder : orderOf (Multiplicative.ofAdd firstCoordinate) = 2 := by
    rw [← orderOf_injective coordinates hinjective]
    change orderOf (QuaternionGroup.a firstCoordinate) = 2
    rw [← hfirst]
    exact first.property
  have hsecondOrder : orderOf (Multiplicative.ofAdd secondCoordinate) = 2 := by
    rw [← orderOf_injective coordinates hinjective]
    change orderOf (QuaternionGroup.a secondCoordinate) = 2
    rw [← hsecond]
    exact second.property
  have hequal := cyclic_involutions_unique
    (⟨Multiplicative.ofAdd firstCoordinate, hfirstOrder⟩ :
      Involution (Multiplicative (ZMod (2 * size))))
    ⟨Multiplicative.ofAdd secondCoordinate, hsecondOrder⟩
  apply Subtype.ext
  rw [hfirst, hsecond]
  exact congrArg (fun involution : Involution (Multiplicative (ZMod (2 * size))) =>
    coordinates involution.val) hequal

theorem quaternion_no_commuting_distinct_involutions (size : ℕ) [NeZero size] :
    NoCommutingDistinctInvolutions (QuaternionGroup size) :=
  fun first second _ => quaternion_unique_involution size first second

theorem quaternion_sylow_no_commuting_distinct_involutions
    {G : Type*} [Group G] [Finite G] (sylow : Sylow 2 G) (exponent : ℕ)
    (hquaternion : Nonempty ((sylow : Subgroup G) ≃* QuaternionGroup (2 ^ exponent))) :
    NoCommutingDistinctInvolutions G := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨equivalence⟩ := hquaternion
  apply (no_commuting_distinct_involutions_sylow_iff sylow).mpr
  exact no_commuting_distinct_involutions_of_injective equivalence.toMonoidHom
    equivalence.injective (quaternion_no_commuting_distinct_involutions (2 ^ exponent))

end CFSG.DisconnectedInvolutionGraph.Helpers
