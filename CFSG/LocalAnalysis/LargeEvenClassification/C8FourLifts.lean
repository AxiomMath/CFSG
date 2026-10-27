module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourNorm
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourReplacement

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem c8_four_adjusted_scalar_lift {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (t : S)
    (hlift : c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) t) = c8FourDelta) :
    ∃ t₀ : S, t₀ ^ 2 = ((coordinates.symm (0, 1)).toMul : S) ∧
      c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) t₀) = c8FourDelta := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := c8FourAutomorphismEquiv hcommutative coordinates
  let α := MulAut.conjNormal (H := A) t
  let y := (coordinates.symm (0, 1)).toMul
  obtain ⟨a, ha, hprimitive, hfixed⟩ := c8_four_central_action_primitive_square A hcommutative
    hselfCentralizing hnoEight coordinates c8FourDelta c8FourDelta_square c8FourDelta_ne_one
    c8Four_scalar_shear_norms.1 c8Four_scalar_shear_norms.2.1
    (fun s => c8FourDelta_central _) t hlift
  have hnotDouble : ¬ ∃ z : CyclicPair 2 4, 2 • z = coordinates (Additive.ofMul a) := by
    rintro ⟨z, hz⟩
    apply hprimitive (coordinates.symm z).toMul
    apply Additive.ofMul.injective
    apply coordinates.injective
    change coordinates (Additive.ofMul a) = coordinates (2 • coordinates.symm z)
    rw [map_nsmul, coordinates.apply_symm_apply, hz]
  have hrootFinite : ∀ a : CyclicPair 2 4,
      c8FourApply c8FourDelta a = a → (¬ ∃ z : CyclicPair 2 4, 2 • z = a) →
        ∃ r : CyclicPair 2 4, 2 • r = (0, 1) - a := by decide +kernel
  obtain ⟨r, hr⟩ := hrootFinite _ hfixed hnotDouble
  obtain ⟨z, hz⟩ := c8Four_scalar_shear_norms.2.1 r
  let b := (coordinates.symm z).toMul
  have hnorm : α b * b = y * a⁻¹ := by
    apply Additive.ofMul.injective
    apply coordinates.injective
    change coordinates (Additive.ofMul (α b) + Additive.ofMul b) =
      coordinates (Additive.ofMul y + -Additive.ofMul a)
    rw [map_add, map_add, map_neg, c8FourAutomorphismEquiv_apply hcommutative coordinates, hlift]
    dsimp only [b, y]
    change c8FourApply c8FourDelta (coordinates (coordinates.symm z)) + coordinates (coordinates.symm z) =
      coordinates (coordinates.symm (0, 1)) + -coordinates (Additive.ofMul a)
    rw [coordinates.apply_symm_apply, coordinates.apply_symm_apply, hz, hr]
    exact sub_eq_add_neg _ _
  have hbaction : MulAut.conjNormal (H := A) (b : S) = 1 := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact (show Commute (b : S) (c : S) from congrArg Subtype.val (mul_comm b c)).mul_inv_cancel
  refine ⟨(b : S) * t, ?_, ?_⟩
  · rw [involution_action_left_lift_square A t b hcommutative, ← ha]
    change ((α b * b) * a : A).val = y.val
    rw [hnorm]
    group
  · rw [map_mul, hbaction, one_mul]
    exact hlift

theorem commuting_involution_lift_product {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (t u : S) (a w : A) (ha : (a : S) = t ^ 2) (hw : (w : S) = u ^ 2)
    (htwo : MulAut.conjNormal (H := A) t ^ 2 = 1)
    (hcommute : Commute (MulAut.conjNormal (H := A) t) (MulAut.conjNormal (H := A) u)) :
    ∃ c : A,
      MulAut.conjNormal (H := A) u a = a * MulAut.conjNormal (H := A) t c * c ∧
      (t * u) ^ 2 = ((a * c * w : A) : S) := by
  let action : S →* MulAut A := MulAut.conjNormal
  have hkernel : action.ker = A := (conjNormal_ker_eq_centralizer A).trans hselfCentralizing
  have hc : t⁻¹ * u * t * u⁻¹ ∈ A := by
    apply hkernel.le
    change action (t⁻¹ * u * t * u⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc' : Commute (action t) (action u) := hcommute
    rw [mul_assoc (action t)⁻¹, hc'.eq.symm]
    group
  let c : A := ⟨t⁻¹ * u * t * u⁻¹, hc⟩
  have hconjugate : u * t * u⁻¹ = t * c := by dsimp only [c]; group
  have htInverse : MulAut.conjNormal (H := A) t⁻¹ = MulAut.conjNormal (H := A) t := by
    rw [map_inv]
    have h := (eq_inv_of_mul_eq_one_left (show action t * action t = 1 by simpa only [pow_two] using htwo)).symm
    exact h
  refine ⟨c, ?_, ?_⟩
  · apply Subtype.ext
    change u * (a : S) * u⁻¹ = (a : S) * (MulAut.conjNormal (H := A) t c : S) * c
    rw [ha, ← htInverse, MulAut.conjNormal_apply, inv_inv]
    calc
      u * t ^ 2 * u⁻¹ = (u * t * u⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = (t * c) ^ 2 := by rw [hconjugate]
      _ = t ^ 2 * (t⁻¹ * (c : S) * t) * c := by simp only [pow_two]; group
  · change (t * u) ^ 2 = (a : S) * (c : S) * w
    rw [ha, hw]
    dsimp only [c]
    simp only [pow_two]
    group

theorem c8_four_central_involution_pair_exclusion {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4)
    (hdelta : c8FourDelta ∈ ((c8FourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range)
    (hnu : c8FourNu ∈ ((c8FourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range)
    (hcentral : ∀ s : S, Commute c8FourNu
      (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s))) : False := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := c8FourAutomorphismEquiv hcommutative coordinates
  obtain ⟨t, ht⟩ := hdelta
  obtain ⟨t, hsquare, ht⟩ := c8_four_adjusted_scalar_lift A hcommutative hselfCentralizing hnoEight coordinates t ht
  obtain ⟨u, hu⟩ := hnu
  change e (MulAut.conjNormal (H := A) u) = c8FourNu at hu
  let y := (coordinates.symm (0, 1)).toMul
  obtain ⟨w, hw, hprimitive, hfixed⟩ := c8_four_central_action_primitive_square A hcommutative
    hselfCentralizing hnoEight coordinates c8FourNu c8FourNu_square c8FourNu_ne_one
    c8Four_scalar_shear_norms.2.2.1 c8Four_scalar_shear_norms.2.2.2.1 hcentral u hu
  have htwo : MulAut.conjNormal (H := A) t ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, ht, c8FourDelta_square, map_one]
  have hcommute : Commute (MulAut.conjNormal (H := A) t) (MulAut.conjNormal (H := A) u) := by
    apply e.injective
    rw [map_mul, map_mul, ht, hu]
    exact (c8FourDelta_central _).eq
  obtain ⟨c, hc, hproduct⟩ := commuting_involution_lift_product A hselfCentralizing t u y w hsquare.symm hw htwo hcommute
  have hfixy : MulAut.conjNormal (H := A) u y = y := by
    apply Additive.ofMul.injective
    apply coordinates.injective
    rw [c8FourAutomorphismEquiv_apply hcommutative coordinates, hu]
    dsimp only [y]
    change c8FourApply c8FourNu (coordinates (coordinates.symm (0, 1))) = coordinates (coordinates.symm (0, 1))
    rw [coordinates.apply_symm_apply]
    decide +kernel
  have hcnorm : MulAut.conjNormal (H := A) t c * c = 1 := by
    rw [hfixy] at hc
    exact mul_left_cancel (by simpa only [mul_assoc, mul_one] using hc.symm)
  have hczero : c8FourApply c8FourDelta (coordinates (Additive.ofMul c)) + coordinates (Additive.ofMul c) = 0 := by
    rw [← ht, ← c8FourAutomorphismEquiv_apply, ← map_add]
    change coordinates (Additive.ofMul ((MulAut.conjNormal (H := A) t) c * c)) = 0
    rw [hcnorm]
    exact map_zero coordinates
  have hwzero : ¬ ∃ z : CyclicPair 2 4, 2 • z = coordinates (Additive.ofMul w) := by
    rintro ⟨z, hz⟩
    apply hprimitive (coordinates.symm z).toMul
    apply Additive.ofMul.injective
    apply coordinates.injective
    change coordinates (Additive.ofMul w) = coordinates (2 • coordinates.symm z)
    rw [map_nsmul, coordinates.apply_symm_apply]
    exact hz.symm
  have hfinite : ∀ c w : CyclicPair 2 4,
      c8FourApply c8FourDelta c + c = 0 → c8FourApply c8FourNu w = w →
      (¬ ∃ z : CyclicPair 2 4, 2 • z = w) → ∃ z : CyclicPair 2 4, 2 • z = (0, 1) + c + w := by
    decide +kernel
  obtain ⟨z, hz⟩ := hfinite _ _ hczero hfixed hwzero
  have hcentralProduct (s : S) : Commute (c8FourDelta * c8FourNu) (e (MulAut.conjNormal (H := A) s)) :=
    (c8FourDelta_central _).mul_left (hcentral s)
  have htu : e (MulAut.conjNormal (H := A) (t * u)) = c8FourDelta * c8FourNu := by
    rw [map_mul, map_mul, ht, hu]
  obtain ⟨a, ha, hprimitiveTu, _⟩ := c8_four_central_action_primitive_square A hcommutative
    hselfCentralizing hnoEight coordinates (c8FourDelta * c8FourNu) c8FourDeltaNu_square c8FourDeltaNu_ne_one
    c8Four_scalar_shear_norms.2.2.2.2.1 c8Four_scalar_shear_norms.2.2.2.2.2 hcentralProduct (t * u) htu
  apply hprimitiveTu (coordinates.symm z).toMul
  have heq : a = y * c * w := Subtype.ext (ha.trans hproduct)
  rw [heq]
  apply Additive.ofMul.injective
  apply coordinates.injective
  change coordinates (Additive.ofMul y + Additive.ofMul c + Additive.ofMul w) = coordinates (2 • coordinates.symm z)
  rw [map_add, map_add, map_nsmul, coordinates.apply_symm_apply]
  dsimp only [y]
  change coordinates (coordinates.symm (0, 1)) + coordinates (Additive.ofMul c) + coordinates (Additive.ofMul w) = 2 • z
  rw [coordinates.apply_symm_apply]
  exact hz.symm

end CFSG.LargeEvenClassification.Helpers
