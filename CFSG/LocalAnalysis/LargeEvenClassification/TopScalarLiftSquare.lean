module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalarNorm
public import CFSG.LocalAnalysis.LargeEvenClassification.BinaryCoordinateRoots

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem central_power_involution_primitive_lift_square {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (hcard : Nat.card (normalElementarySquareKernel A hcommutative) = 4)
    (exponent : ℕ) (δ : MulAut A)
    (hpower : ∀ a : A, δ a = a ^ (1 + 2 ^ (exponent + 2)))
    (hsquare : δ ^ 2 = 1) (hnontrivial : δ ≠ 1)
    (t : S) (hlift : MulAut.conjNormal (H := A) t = δ) :
    ∃ square : A, (square : S) = t ^ 2 ∧ ∀ a : A, square ≠ a ^ 2 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  have hcentral (s : S) : Commute δ (MulAut.conjNormal (H := A) s) := by
    apply MulEquiv.ext
    intro a
    change δ (MulAut.conjNormal (H := A) s a) = MulAut.conjNormal (H := A) s (δ a)
    rw [hpower, hpower, map_pow]
  have hprincipal : abelianAutomorphismUnits A δ ∈ principalFourSubgroup (AddMonoid.End (Additive A)) := by
    refine ⟨(2 ^ exponent : ℕ) • (1 : AddMonoid.End (Additive A)), ?_⟩
    apply AddMonoid.End.ext
    intro a
    change Additive.ofMul (δ a.toMul) = a + 4 • ((2 ^ exponent : ℕ) • a)
    rw [hpower]
    change (1 + 2 ^ (exponent + 2) : ℕ) • a = a + 4 • ((2 ^ exponent : ℕ) • a)
    rw [add_nsmul, one_nsmul, smul_smul, pow_add]
    congr 1
    norm_num
    rw [Nat.mul_comm]
  obtain ⟨hnormKernel, hnormSurjective⟩ := abelian_principal_norm (hpgroup.to_subgroup A) δ hprincipal
  obtain ⟨hmem, hobstruction⟩ := central_action_involution_norm_obstruction A hcommutative
    hselfCentralizing hnoEight δ hsquare hnontrivial hcentral hnormKernel hcard t hlift
  let square : A := ⟨t ^ 2, hmem⟩
  refine ⟨square, rfl, ?_⟩
  intro a hsquarePower
  obtain ⟨b, hb⟩ := hnormSurjective a
  exact hobstruction b (congrArg (fun a : A => a.val) (hsquarePower.trans hb.symm))

theorem top_scalar_fixed_long_coordinate (exponent : ℕ)
    (x : ZMod (2 ^ (exponent + 3)))
    (hfixed : (1 + (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2)) * x = x) :
    ∃ y : ZMod (2 ^ (exponent + 3)), x = 2 • y := by
  obtain ⟨y, hy⟩ := binaryCongruenceInvolution_fixed_square exponent x
    (by rw [binaryCongruenceInvolution_val]; exact hfixed)
  refine ⟨y, ?_⟩
  simpa only [two_nsmul] using hy.symm

theorem rank_two_cyclic_times_two_scalar_square_obstruction {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (exponent : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (exponent + 3))) × Multiplicative (ZMod 2))
    (t : S)
    (hscalar : ∀ a : A, MulAut.conjNormal (H := A) t a = a ^ (1 + 2 ^ (exponent + 2))) :
    ∃ square : A, (square : S) = t ^ 2 ∧
      (∃ y : ZMod (2 ^ (exponent + 3)), (coordinates square).1.toAdd = 2 • y) ∧
      (coordinates square).2.toAdd = 1 ∧ ∀ a : A, square ≠ a ^ 2 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let δ := MulAut.conjNormal (H := A) t
  have hδsquare : δ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro a
    change δ (δ a) = a
    rw [hscalar, hscalar, ← pow_mul]
    apply coordinates.injective
    rw [map_pow]
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change ((1 + 2 ^ (exponent + 2)) * (1 + 2 ^ (exponent + 2)) : ℕ) •
        (coordinates a).1.toAdd = (coordinates a).1.toAdd
      rw [nsmul_eq_mul]
      have hscalarSquare := congrArg (fun u : (ZMod (2 ^ (exponent + 3)))ˣ => u.val)
        (binaryCongruenceInvolution_sq exponent)
      change (binaryCongruenceInvolution exponent).val ^ 2 = 1 at hscalarSquare
      rw [binaryCongruenceInvolution_val] at hscalarSquare
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, pow_two, one_mul] using
        congrArg (fun z : ZMod (2 ^ (exponent + 3)) => z * (coordinates a).1.toAdd) hscalarSquare
    · apply Multiplicative.toAdd.injective
      change ((1 + 2 ^ (exponent + 2)) * (1 + 2 ^ (exponent + 2)) : ℕ) •
        (coordinates a).2.toAdd = (coordinates a).2.toAdd
      rw [nsmul_eq_mul]
      push_cast
      have hzero : (2 : ZMod 2) ^ (exponent + 2) = 0 := by
        simpa only [Nat.cast_ofNat] using
          (ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 1 ≤ exponent + 2))
      rw [hzero]
      simp
  have hδnontrivial : δ ≠ 1 := by
    intro h
    let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
    have hx := hscalar x
    change δ x = x ^ (1 + 2 ^ (exponent + 2)) at hx
    rw [h] at hx
    change x = x ^ (1 + 2 ^ (exponent + 2)) at hx
    have hxcoord := congrArg (fun a : A => (coordinates a).1.toAdd) hx
    rw [map_pow, coordinates.apply_symm_apply] at hxcoord
    change (1 : ZMod (2 ^ (exponent + 3))) = (1 + 2 ^ (exponent + 2) : ℕ) • 1 at hxcoord
    have hunit : binaryCongruenceInvolution exponent = 1 := by
      apply Units.ext
      rw [binaryCongruenceInvolution_val]
      change 1 + (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2) = 1
      simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, mul_one] using hxcoord.symm
    exact binaryCongruenceInvolution_ne_one exponent hunit
  have hcard := binary_rank_two_square_kernel_card A hcommutative (by omega : 0 < exponent + 3)
    (by decide : 0 < 1) coordinates
  obtain ⟨square, hsquare, hprimitive⟩ := central_power_involution_primitive_lift_square hpgroup A
    hcommutative hselfCentralizing hnoEight hcard exponent δ hscalar hδsquare hδnontrivial t rfl
  have hfixed : δ square = square := by
    apply Subtype.ext
    change t * square.val * t⁻¹ = square.val
    rw [hsquare]
    group
  have hfixedCoordinates := congrArg (fun a : A => (coordinates a).1.toAdd) (hscalar square |>.symm.trans hfixed)
  rw [map_pow] at hfixedCoordinates
  change (1 + 2 ^ (exponent + 2) : ℕ) • (coordinates square).1.toAdd = (coordinates square).1.toAdd at hfixedCoordinates
  obtain ⟨y, hy⟩ := top_scalar_fixed_long_coordinate exponent (coordinates square).1.toAdd
    (by simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using hfixedCoordinates)
  have hshort : (coordinates square).2.toAdd = 1 := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    rcases hcases (coordinates square).2.toAdd with hzero | hone
    · let root := coordinates.symm (Multiplicative.ofAdd y, 1)
      apply False.elim
      apply hprimitive root
      apply coordinates.injective
      rw [map_pow, coordinates.apply_symm_apply]
      apply Prod.ext
      · apply Multiplicative.toAdd.injective
        exact hy
      · apply Multiplicative.toAdd.injective
        simpa using hzero
    · exact hone
  exact ⟨square, hsquare, ⟨y, hy⟩, hshort, hprimitive⟩

end CFSG.LargeEvenClassification.Helpers
