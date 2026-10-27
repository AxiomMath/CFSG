module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionPredicates

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem central_action_involution_fixed_norm_exclusion {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (automorphism : MulAut A) (hsquare : automorphism ^ 2 = 1) (hne : automorphism ≠ 1)
    (hcentral : ∀ s : S, Commute automorphism (MulAut.conjNormal (H := A) s))
    (hkernel : ∀ a : A, automorphism a * a = 1 ↔ a ^ 2 = 1)
    (hcard : Nat.card (normalElementarySquareKernel A hcommutative) = 4)
    (hfixedNorm : ∀ a : A, automorphism a = a → ∃ b : A, automorphism b * b = a)
    (t : S) (hlift : MulAut.conjNormal (H := A) t = automorphism) : False := by
  obtain ⟨hmem, hnotNorm⟩ := central_action_involution_norm_obstruction A hcommutative
    hselfCentralizing hnoEight automorphism hsquare hne hcentral hkernel hcard t hlift
  let a : A := ⟨t ^ 2, hmem⟩
  have hfixed : automorphism a = a := by
    rw [← hlift]
    apply Subtype.ext
    change t * t ^ 2 * t⁻¹ = t ^ 2
    group
  obtain ⟨b, hb⟩ := hfixedNorm a hfixed
  exact hnotNorm b (congrArg Subtype.val hb.symm)

theorem c8_four_central_forbidden_norm_exclusion {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (g : C8FourCode)
    (hsquare : g ^ 2 = 1) (hne : g ≠ 1) (hkernel : c8FourNormKernel g)
    (hfixedNorm : ∀ x : CyclicPair 2 4, c8FourApply g x = x →
      ∃ y : CyclicPair 2 4, c8FourApply g y + y = x)
    (hcentral : ∀ s : S, Commute g
      (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s)))
    (t : S) (hlift : c8FourAutomorphismEquiv hcommutative coordinates
      (MulAut.conjNormal (H := A) t) = g) : False := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := c8FourAutomorphismEquiv hcommutative coordinates
  let α := e.symm g
  have hαsquare : α ^ 2 = 1 := by rw [← map_pow, hsquare, map_one]
  have hαne : α ≠ 1 := by
    intro h
    apply hne
    have h' := congrArg e h
    change e (e.symm g) = e 1 at h'
    simpa only [e.apply_symm_apply, map_one] using h'
  have hαcentral (s : S) : Commute α (MulAut.conjNormal (H := A) s) := by
    apply e.injective
    change e (e.symm g * MulAut.conjNormal (H := A) s) =
      e (MulAut.conjNormal (H := A) s * e.symm g)
    simpa only [map_mul, e.apply_symm_apply] using (hcentral s).eq
  have hnorm (a : A) : coordinates (Additive.ofMul (α a * a)) =
      c8FourApply g (coordinates (Additive.ofMul a)) + coordinates (Additive.ofMul a) := by
    change coordinates (Additive.ofMul (α a) + Additive.ofMul a) = _
    rw [map_add, c8FourAutomorphismEquiv_apply]
    change c8FourApply (e (e.symm g)) _ + _ = _
    rw [e.apply_symm_apply]
  have hαkernel (a : A) : α a * a = 1 ↔ a ^ 2 = 1 := by
    have hleft : α a * a = 1 ↔ c8FourApply g (coordinates (Additive.ofMul a)) +
        coordinates (Additive.ofMul a) = 0 := by
      rw [← hnorm, ← map_zero coordinates]
      constructor
      · intro h
        rw [h]
        rfl
      · intro h
        exact Additive.ofMul.injective (coordinates.injective h)
    have hright : a ^ 2 = 1 ↔ 2 • coordinates (Additive.ofMul a) = 0 := by
      rw [← map_nsmul, ← map_zero coordinates]
      constructor
      · intro h
        exact congrArg coordinates (congrArg Additive.ofMul h)
      · intro h
        exact Additive.ofMul.injective (coordinates.injective h)
    rw [hleft, hright]
    exact hkernel _
  let pairs : A ≃* Multiplicative (ZMod 8) × Multiplicative (ZMod 4) :=
    (AddEquiv.toMultiplicativeRight coordinates).trans (MulEquiv.prodMultiplicative _ _)
  have hcard := binary_rank_two_square_kernel_card A hcommutative
    (by decide : 0 < 3) (by decide : 0 < 2) pairs
  have hliftα : MulAut.conjNormal (H := A) t = α :=
    e.injective (by rw [hlift, e.apply_symm_apply])
  apply central_action_involution_fixed_norm_exclusion A hcommutative hselfCentralizing
    hnoEight α hαsquare hαne hαcentral hαkernel hcard _ t hliftα
  intro a ha
  have hfixed : c8FourApply g (coordinates (Additive.ofMul a)) = coordinates (Additive.ofMul a) := by
    have happly := c8FourAutomorphismEquiv_apply hcommutative coordinates α a
    change coordinates (Additive.ofMul (α a)) = c8FourApply (e (e.symm g)) _ at happly
    rw [e.apply_symm_apply, ha] at happly
    exact happly.symm
  obtain ⟨y, hy⟩ := hfixedNorm _ hfixed
  refine ⟨(coordinates.symm y).toMul, ?_⟩
  apply Additive.ofMul.injective
  apply coordinates.injective
  rw [hnorm]
  change c8FourApply g (coordinates (coordinates.symm y)) +
    coordinates (coordinates.symm y) = coordinates (Additive.ofMul a)
  simpa only [coordinates.apply_symm_apply] using hy

theorem c8_four_ambient_action_conditions {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) :
    let action := (c8FourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))
    (∀ g : C8FourCode, g ∈ action.range →
      (∀ h ∈ action.range, g * h = h * g) → g ≠ 1 → g ^ 2 = 1 →
      c8FourNormKernel g → ¬ (∀ x : CyclicPair 2 4, c8FourApply g x = x →
        ∃ y : CyclicPair 2 4, c8FourApply g y + y = x)) ∧
    ¬ (c8FourDelta ∈ action.range ∧ c8FourNu ∈ action.range ∧
      ∀ h ∈ action.range, c8FourNu * h = h * c8FourNu) ∧
    (c8FourDelta ∈ action.range → c8FourCompatible action.range) := by
  intro action
  refine ⟨?_, ?_, ?_⟩
  · intro g hg hcentral hne hsquare hkernel hfixedNorm
    obtain ⟨t, ht⟩ := hg
    exact c8_four_central_forbidden_norm_exclusion A hcommutative hselfCentralizing
      hnoEight coordinates g hsquare hne hkernel hfixedNorm
      (fun s => hcentral (action s) ⟨s, rfl⟩) t ht
  · rintro ⟨hdelta, hnu, hcentral⟩
    exact c8_four_central_involution_pair_exclusion A hcommutative hselfCentralizing
      hnoEight coordinates hdelta hnu (fun s => hcentral (action s) ⟨s, rfl⟩)
  · exact c8_four_central_cover_compatibility A hcommutative hselfCentralizing
      hnoEight coordinates

theorem c8_four_ambient_action_admissible {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) :
    c8FourActionAdmissible (((c8FourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range) := by
  obtain ⟨hnorm, hpair, hcover⟩ := c8_four_ambient_action_conditions A hcommutative
    hselfCentralizing hnoEight coordinates
  refine ⟨?_, ?_, hcover⟩
  · intro g hg hi hkernel
    exact hnorm g hg.1 hg.2 hi.1 hi.2 hkernel
  · rintro ⟨hdelta, hnu⟩
    exact hpair ⟨hdelta, hnu.1, hnu.2⟩

end CFSG.LargeEvenClassification.Helpers
